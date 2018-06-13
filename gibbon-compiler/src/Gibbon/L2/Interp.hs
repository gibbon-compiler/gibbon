{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Interpreter reducing L2 programs to values.

module Gibbon.L2.Interp (interpProg2) where

import           Control.DeepSeq
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.ByteString.Builder (toLazyByteString, string8)
import           Data.Loc
import           Data.Foldable (foldlM)
import           System.Clock
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Sequence as S

import           Gibbon.Common
import           Gibbon.GenericOps
import           Gibbon.Interp
import           Gibbon.L1.Syntax as L1
import           Gibbon.L1.Interp as L1
import           Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

instance Interp Prog2 where
  interpProg = interpProg2

-- | Interpret a program, including printing timings to the screen.
--   The returned bytestring contains that printed timing info.
interpProg2 :: RunConfig -> Prog2 -> IO (Value, B.ByteString)
interpProg2 rc Prog{ddefs,fundefs,mainExp} =
  case mainExp of
    -- Print nothing, return "void"
    Nothing -> return (VProd [], B.empty)
    Just (e,_) -> do
      let fenv = M.fromList [ (funName f , f) | f <- M.elems fundefs]
      -- logs contains print side effects
      ((x,logs), Store finstore) <-
        runStateT (runWriterT (interp rc ddefs fenv e)) (Store M.empty)
      -- Policy: don't return locations
      let res = case x of
                 VLoc reg off ->
                     let Buffer b = finstore M.! reg
                     in deserialize ddefs (S.drop off b)
                 _ -> x
      return (res, toLazyByteString logs)

interp :: RunConfig -> DDefs Ty2 -> M.Map Var (FunDef (L Exp2)) -> L Exp2
       -> WriterT Log (StateT Store IO) Value
interp rc ddefs fenv e = fst <$> go M.empty M.empty e
  where
    {-# NOINLINE goWrapper #-}
    goWrapper !_ix env sizeEnv ex = go env sizeEnv ex

    go :: ValEnv -> SizeEnv -> L Exp2 -> WriterT Log (StateT Store IO) (Value, Size)
    go env sizeEnv (L _ ex) =
      case ex of
        -- We interpret a function application by substituting the operand (at
        -- the call-site) for the function argument in the environment. Since
        -- this is a L2 program, we have real locations (and regions) and we
        -- have to make sure that those get passed in as well. We do that
        -- by extending the environment with the location at the call-site.
        --
        -- TODO: After ThreadRegions, even regions are passed in the locs
        -- field. Need to extend the environment with some kind of region
        -- value as well. Also, since we're storing regions in the value
        -- environment anyways, we probably don't need an additional store.
        --
        AppE f locs arg ->
          case M.lookup f fenv of
            Nothing -> error $ "L2.Interp: unbound function: "++sdoc ex
            Just FunDef{funArg,funBody,funTy} -> do
              (rand,sz) <- go env sizeEnv arg
              let inLocs  = inLocVars funTy
                  outLocs = outLocVars funTy
                  -- ASSUMPTION: Ordering is important in `locs`, and we assume
                  -- that the input locations appear before output locations.
                  env' = foldr
                           (\(fnLoc, callSiteLoc) acc ->
                              M.insert fnLoc (acc M.! callSiteLoc)  acc)
                           env
                           (zip (inLocs ++ outLocs) locs)
              go (M.insert funArg rand env') (M.insert funArg sz sizeEnv) funBody

        CaseE{} -> error $ "TODO: L2.Interp: " ++ sdoc ex

        -- This operation constructs a packed value by writing things to the
        -- buffer. The packed value is represented by a 1 byte tag,
        -- followed by other arguments.
        -- ---
        -- These pointers are different (but similar in spirit) to the
        -- indirections that we add in Gibbon2 mode.
        -- ---
        -- Consider the Leaf constructor of the Tree type:
        --
        --    | SerTag 0 Leaf | SerInt  | SerInt 1 | ... |
        --
        DataConE loc dcon args ->
          case M.lookup loc env of
            Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc
            Just (VLoc reg offset) -> do
              buf_maybe <- lookupInStore reg
              case buf_maybe of
                Nothing  -> error $ "L2.Interp: Unbound region " ++ sdoc reg
                Just buf -> do
                  vals <- mapM (go env sizeEnv) args
                  let tys = lookupDataCon ddefs dcon
                      tag = getTagOfDataCon ddefs dcon
                      bufWithTag = insertAtBuffer offset (SerTag tag dcon) buf
                      (bufWithVals, new_off) =
                        foldl
                          (\(acc, off) ((v, sz), _ty) ->
                               let new_off1 = off + sizeToInt sz in
                                 case v of
                                   VInt i -> ( insertAtBuffer off (SerInt i) acc , new_off1 )
                                   -- This is a packed value, and it must already
                                   -- be written to the buffer (by the thing that
                                   -- returned this). So we just update the offset
                                   -- to point to the end of this value.
                                   VLoc{} -> ( acc , new_off1 )
                                   _ -> error $ "L2.Interp: DataConE todo: " ++ sdoc v)
                          (bufWithTag, offset+1)
                          (zip vals tys)
                  insertIntoStore reg bufWithVals
                  return (VLoc reg offset, SOne (new_off - offset))
            Just val -> error $ "L2.Interp: Unexpected value for " ++ sdoc loc ++ ":" ++ sdoc val

        LetE (v,_,_ty,rhs) bod -> do
          (rhs', sz) <- go env sizeEnv rhs
          go (M.insert v rhs' env) (M.insert v sz sizeEnv) bod

        Ext ext ->
          case ext of
            LetRegionE reg bod -> do
              insertIntoStore (regionToVar reg) emptyBuffer
              go env sizeEnv bod

            LetLocE loc locexp bod ->
              case locexp of
                StartOfLE reg -> do
                  buf_maybe <- lookupInStore (regionToVar reg)
                  case buf_maybe of
                    Nothing -> error $ "L2.Interp: Unbound region: " ++ sdoc reg
                    Just _ ->
                      go (M.insert loc (VLoc (regionToVar reg) 0) env) sizeEnv bod

                AfterConstantLE i loc2 -> do
                  case M.lookup loc2 env of
                    Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc
                    Just (VLoc reg offset) ->
                      go (M.insert loc (VLoc reg (offset + i)) env) sizeEnv bod
                    Just val ->
                      error $ "L2.Interp: Unexpected value for " ++ sdoc loc2 ++ ":" ++ sdoc val

                AfterVariableLE v loc2 -> do
                  case M.lookup loc2 env of
                    Nothing -> error $ "L2.Interp: Unbound location: " ++ sdoc loc
                    Just (VLoc reg offset) ->
                      case M.lookup v sizeEnv of
                        Nothing -> error $ "L2.Interp: No size info found: " ++ sdoc v
                        Just sz ->
                          go (M.insert loc (VLoc reg (offset + (sizeToInt sz))) env)
                             sizeEnv bod
                    Just val ->
                      error $ "L2.Interp: Unexpected value for " ++ sdoc loc2 ++ ":" ++ sdoc val
                _ -> error $ "L2.Interp: TODO " ++ sdoc locexp

            _ -> error $ "L2.Interp: TODO " ++ sdoc ext

        -- Straightforward recursion (same as the L1 interpreter)
        LitE n    -> return (VInt n, SOne 8)
        LitSymE s -> return (VInt (strToInt $ fromVar s), SOne 8)
        VarE v    -> return (env # v, sizeEnv # v)

        PrimAppE p args -> do (args',_) <- unzip <$> mapM (go env sizeEnv) args
                              case sizeOfTy (primRetTy p) of
                                Just sz -> return (L1.applyPrim rc p args', SOne sz)
                                Nothing -> error $ "L2.Interp: Couldn't guess the size: " ++ sdoc ex

        IfE a b c -> do (v,_) <- go env sizeEnv a
                        case v of
                         VBool flg -> if flg
                                      then go env sizeEnv b
                                      else go env sizeEnv c
                         oth -> error$ "interp: expected bool, got: "++show oth

        MkProdE ls -> do
            (args, szs) <- unzip <$> mapM (go env sizeEnv) ls
            return (VProd args , SMany szs)

        ProjE ix e0 -> do (VProd ls, SMany szs) <- go env sizeEnv e0
                          return (ls !! ix, szs !! ix)

        TimeIt bod _ isIter -> do
              let iters = if isIter then rcIters rc else 1
              !_ <- return $! force env
              st <- liftIO $ getTime clk
              (val,sz) <- foldM (\ _ i -> goWrapper i env sizeEnv bod)
                            (error "Internal error: this should be unused.")
                          [1..iters]
              en <- liftIO $ getTime clk
              let tm = fromIntegral (toNanoSecs $ diffTimeSpec en st)
                        / 10e9 :: Double
              if isIter
               then do tell$ string8 $ "ITERS: "++show iters       ++"\n"
                       tell$ string8 $ "SIZE: " ++show (rcSize rc) ++"\n"
                       tell$ string8 $ "BATCHTIME: "++show tm      ++"\n"
               else tell$ string8 $ "SELFTIMED: "++show tm ++"\n"
              return $! (val, sz)

        MapE{} -> error $ "L2.Interp: TODO " ++ sdoc ex
        FoldE{} -> error $ "L2.Interp: TODO " ++ sdoc ex

clk :: Clock
clk = Monotonic

--------------------------------------------------------------------------------

data Size = SOne Int
          | SMany [Size]
  deriving (Read, Show, Eq, Ord, Generic, Out)

type SizeEnv = M.Map Var Size

sizeToInt :: Size -> Int
sizeToInt (SOne i)   = i
sizeToInt (SMany ls) = sum $ map sizeToInt ls
