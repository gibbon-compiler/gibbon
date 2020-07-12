{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Interpreter for L1
module Gibbon.L1.Interp ( interpProg, interp, applyPrim ) where

import           Data.ByteString.Builder ( toLazyByteString, string8)
import qualified Data.ByteString.Lazy.Char8 as B
import           Data.Char ( ord )
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.List as L
import qualified Data.Map as M
import           System.Clock
import           System.IO.Unsafe
import           System.Random
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.L1.Syntax as L1


interpChatter :: Int
interpChatter = 7

------------------------------------------------------------

instance InterpExt () Exp1 (E1Ext () Ty1) where
  gInterpExt rc valenv ddefs fundefs ex =
      case ex of
          BenchE fn locs args _b -> interp rc valenv ddefs fundefs (AppE fn locs args)
          AddFixed{} -> error "L1.Interp: AddFixed not handled."

instance Interp () Exp1 where
  gInterpExp = interp

instance InterpProg () Exp1 where
  gInterpProg _s = interpProg

-- | Interpret a program, including printing timings to the screen.
--   The returned bytestring contains that printed timing info.
interpProg :: Interp () e => RunConfig -> Prog e -> IO ((), Value e, B.ByteString)
interpProg rc Prog{ddefs,fundefs,mainExp} =
  case mainExp of
    -- Print nothing, return "void"
    Nothing -> return ((), VProd [], B.empty)
    Just (e,_) -> do
      let fenv = M.fromList [ (funName f , f) | f <- M.elems fundefs]
      (v,logs,_) <- runInterpM (gInterpExp rc M.empty ddefs fenv e) ()
      pure ((), v, toLazyByteString logs)

interp :: forall e l d s.
          (Show l, Ord l, NFData l, Out l,
           Show d, NFData d, Out d, Ord d,
           Ord (e l d), NFData (e l d),
           InterpExt s (PreExp e l d) (e l d))
       => RunConfig
       -> ValEnv (PreExp e l d)
       -> DDefs (TyOf (PreExp e l d))
       -> FunDefs (PreExp e l d)
       -> (PreExp e l d)
       -> InterpM s (PreExp e l d) (Value (PreExp e l d))
interp rc valenv ddefs fenv = go valenv
  where
    {-# NOINLINE goWrapper #-}
    goWrapper env !_ix ex = go env ex

    go :: ValEnv (PreExp e l d) -> (PreExp e l d) -> InterpM s (PreExp e l d) (Value (PreExp e l d))
    go env x0 = do
        case x0 of
          Ext ext -> do
              gInterpExt rc env ddefs fenv ext

          LitE c    -> return $ VInt c
          FloatE c  -> return $ VFloat c
          LitSymE s -> return $ VSym (fromVar s)
          VarE v    -> do
              return $ env # v

          -- -- Don't sort for now
          -- PrimAppE (VSortP{}) [ls,VarE fp] -> do
          --   (VList vals) <- go env ls
          --   applySortP env vals fp

          PrimAppE p ls -> do args <- mapM (go env) ls
                              dbgTraceIt (sdoc x0) (pure ())
                              applyPrim rc p args
          ProjE ix ex   -> do VProd ls <- go env ex
                              return $ ls !!! ix

          -- N.B. this AppE is shared by the interpreters for L0 and L1
          AppE f _ ls -> do
            dbgTraceIt (sdoc x0) (pure ())
            ls' <- mapM (go env) ls
            -- Look in the local environment first
            case M.lookup f env of
              Nothing ->
                case M.lookup f fenv of
                  Just fn -> do
                      let env' = M.union (M.fromList (zip (funArgs fn) ls')) env
                      go env' (funBody fn)
                  Nothing -> error $ "L1.Interp: unbound function in application: "++ndoc x0
              Just fn@(VLam args bod closed_env) ->
                if length args /= length ls'
                then error $ "L0.Interp: unexpected arguments in application: "++ ndoc ls' ++ " in " ++ ndoc fn
                else do
                  let env' = M.fromList (zip args ls') `M.union` closed_env `M.union` env
                  go env' bod
              Just oth -> error $ "L0.Interp: expected a lambda in application, got: "++ ndoc oth ++ " in " ++ ndoc oth


          CaseE _ [] -> error$ "L1.Interp: CaseE with empty alternatives list: "++ndoc x0

          CaseE x1 alts@((_sometag,_,_):_) -> do
                 v <- go env x1
                 case v of
                   VPacked k ls2 -> do
                       let vs = L.map fst prs
                           (_,prs,rhs) = lookup3 k alts
                           env' = M.union (M.fromList (zip vs ls2)) env
                       go env' rhs
                   _ -> error$ "L1.Interp: type error, expected data constructor, got: "++ndoc v++
                               "\nWhen evaluating scrutinee of case expression: "++ndoc x1


          LetE (v,_,_ty,rhs) bod -> do
            rhs' <- go env rhs
            let env' = M.insert v rhs' env
            go env' bod

          MkProdE ls -> VProd <$> mapM (go env) ls
          -- TODO: Should check this against the ddefs.
          DataConE _ k ls -> do
              args <- mapM (go env) ls
              return $ VPacked k args

          TimeIt bod _ isIter -> do
              let iters = if isIter then rcIters rc else 1
              !_ <- return $! force env
              st <- liftIO $ getTime clk
              val <- foldM (\ _ i -> goWrapper env i bod)
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
              return $! val

          SpawnE f locs args -> go env (AppE f locs args)
          SyncE -> pure $ VInt (-1)

          WithArenaE v e -> do
              let env' = M.insert v (VInt 0) env
              go env' e

          IfE a b c -> do v <- go env a
                          case v of
                           VBool flg -> if flg
                                        then go env b
                                        else go env c
                           oth -> error$ "interp: expected bool, got: "++show oth

          MapE _ _bod    -> error "L1.Interp: finish MapE"
          FoldE _ _ _bod -> error "L1.Interp: finish FoldE"

    -- _applySortP :: ValEnv (PreExp e l d) -> [(Value (PreExp e l d))] -> Var -> WriterT InterpLog IO (Value (PreExp e l d))
    -- _applySortP env ls f = do
    --   let fn  = case M.lookup f fenv of
    --               Just fun -> fun
    --               Nothing -> error $ "L1.Interp: unbound function given to vsort: "++ndoc f
    --       ls' = sortBy
    --             (\a b ->
    --                  let env' = M.union (M.fromList (zip (funArgs fn) [a,b])) env
    --                      (i,_) =
    --                        unsafePerformIO $ (runWriterT (go env' (funBody fn)))
    --                      VInt j = i
    --                  in compare j 0)
    --             ls
    --   pure (VList ls')


applyPrim :: (Show ty, Ord l, Out l, Show l, Show d, Out d, Ord d,  Ord (e l d), Out (e l d), Show (e l d))
          => RunConfig -> Prim ty -> [(Value (PreExp e l d))] -> InterpM s (PreExp e l d) (Value (PreExp e l d))
applyPrim rc p args =
 case (p,args) of
   (MkTrue,[])             -> pure $ VBool True
   (MkFalse,[])            -> pure $ VBool False
   -- FIXME: randomIO does not guarentee unique numbers every time.
   (Gensym, [])            -> pure $ VSym $ "gensym_" ++ (show $ (unsafePerformIO randomIO :: Int) `mod` 1000)
   (AddP,[VInt x, VInt y]) -> pure $ VInt (x+y)
   (SubP,[VInt x, VInt y]) -> pure $ VInt (x-y)
   (MulP,[VInt x, VInt y]) -> pure $ VInt (x*y)
   (DivP,[VInt x, VInt y]) -> pure $ VInt (x `quot` y)
   (ModP,[VInt x, VInt y]) -> pure $ VInt (x `rem` y)
   (ExpP,[VInt x, VInt y]) -> pure $ VInt (x ^ y)
   (FAddP,[VFloat x, VFloat y]) -> pure $ VFloat (x+y)
   (FSubP,[VFloat x, VFloat y]) -> pure $ VFloat (x-y)
   (FMulP,[VFloat x, VFloat y]) -> pure $ VFloat (x*y)
   (FDivP,[VFloat x, VFloat y]) -> pure $ VFloat (x / y)
   (FExpP,[VFloat x, VFloat y]) -> pure $ VFloat (x ** y)
   -- Constrained to the value of RAND_MAX (in C) on my laptop: 2147483647 (2^31 − 1)
   (RandP,[]) -> do
       i <- liftIO $ randomIO
       pure $ VInt $ i `mod` 2147483647
   (FRandP,[]) -> do
       i <- liftIO $ randomIO
       pure $ VFloat i
   (IntToFloatP,[VInt x]) -> pure $ VFloat (fromIntegral x)
   (FloatToIntP,[VFloat x]) -> pure $ VInt (round x)
   (FSqrtP,[VFloat x]) -> pure $ VFloat (sqrt x)
   (EqSymP,[VSym x, VSym y]) -> pure $ VBool (x==y)
   (EqIntP,[VInt x, VInt y]) -> pure $ VBool (x==y)
   (EqFloatP,[VFloat x, VFloat y]) -> pure $ VBool (x==y)
   (LtP,[VInt x, VInt y]) -> pure $ VBool (x < y)
   (GtP,[VInt x, VInt y]) -> pure $ VBool (x > y)
   (LtEqP,[VInt x, VInt y]) -> pure $ VBool (x <= y)
   (GtEqP,[VInt x, VInt y]) -> pure $ VBool (x >= y)
   (FLtP,[VFloat x, VFloat y]) -> pure $ VBool (x < y)
   (FGtP,[VFloat x, VFloat y]) -> pure $ VBool (x > y)
   (FLtEqP,[VFloat x, VFloat y]) -> pure $ VBool (x <= y)
   (FGtEqP,[VFloat x, VFloat y]) -> pure $ VBool (x >= y)
   (AndP, [VBool x, VBool y]) -> pure $ VBool (x && y)
   (OrP, [VBool x, VBool y])  -> pure $ VBool (x || y)
   ((DictInsertP _ty),[_, VDict mp, key, val]) -> pure $ VDict (M.insert key val mp)
   ((DictLookupP _),[VDict mp, key])        -> pure $ mp # key
   ((DictHasKeyP _),[VDict mp, key])        -> pure $ VBool (M.member key mp)
   ((DictEmptyP _),[_])                     -> pure $ VDict M.empty
   ((ErrorP msg _ty),[]) -> pure $ error msg
   (SizeParam,[]) -> pure $ VInt (rcSize rc)
   (IsBig,[_one,_two]) -> pure $ VBool False
   (ReadPackedFile file _ _ ty,[]) ->
       error $ "L1.Interp: unfinished, need to read a packed file: "++show (file,ty)
   (ReadArrayFile{},[]) -> do
       pure (VList [])
   (VAllocP _,_n) -> pure (VList [])
   (VFreeP _,_n) -> pure (VProd [])
   (VFree2P _,_n) -> pure (VProd [])
   (VLengthP _,[(VList ls)]) -> pure $ VInt (length ls)
   (VNthP _,[(VList ls), VInt n]) -> pure $ ls !!! n
   (InplaceVUpdateP _,[(VList ls), VInt i, v]) -> do
       let ls' = if length ls <= i
                 then
                     let need = (i+1) - (length ls)
                     in VList $ ls ++ (replicate need v)
                 else VList (replaceNth i v ls)
       pure ls'
   (VSliceP _,[VInt from, VInt len, (VList ls)]) -> do
       pure $ VList (L.take len (L.drop from ls))
   (GetNumProcessors, []) -> pure $ VInt 1
   -- Don't sort for now.
   (VSortP _, [ls, _fn]) -> do
       pure ls
   (InplaceVSortP _, [ls, _fn]) -> do
       pure ls
   oth -> error $ "unhandled prim or wrong number of arguments: "++show oth

  where
     replaceNth :: Int -> a -> [a] -> [a]
     replaceNth _ _ [] = []
     replaceNth n newVal (x:xs)
       | n == 0 = newVal:xs
       | otherwise = x:replaceNth (n-1) newVal xs


clk :: Clock
clk = Monotonic

strToInt :: String -> Int
strToInt = product . L.map ord
