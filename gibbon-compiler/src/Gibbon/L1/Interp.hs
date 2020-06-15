{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Interpreter for the source language (L1)
--

module Gibbon.L1.Interp
    ( execAndPrint, interpProg1,
      -- * Helpers
      applyPrim, strToInt
    ) where

import           Data.ByteString.Builder (Builder, toLazyByteString, string8)
import qualified Data.ByteString.Lazy.Char8 as B
import           Data.Char ( ord )
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Writer
import           Data.List as L
import           Data.Map as M
import           System.Clock
import           System.IO.Unsafe
import           System.Random
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.L1.Syntax as L1


interpChatter :: Int
interpChatter = 7

------------------------------------------------------------

instance Interp Prog1 where
  interpProg = interpProg1

-- | Interpret a program, including printing timings to the screen.
--   The returned bytestring contains that printed timing info.
interpProg1 :: RunConfig -> Prog1 -> IO (Value, B.ByteString)
interpProg1 rc Prog{ddefs,fundefs,mainExp} =
  case mainExp of
    -- Print nothing, return "void"
    Nothing -> return (VProd [], B.empty)
    Just (e,_) -> do
      let fenv = M.fromList [ (funName f , f) | f <- M.elems fundefs]
      -- logs contains print side effects
      (res,logs) <- runWriterT (interp rc ddefs fenv e)
      return (res, toLazyByteString logs)


interp :: forall l. ( Out l, Show l, Expression (E1Ext l (UrTy l)) )
       => RunConfig
       -> DDefs (TyOf (PreExp E1Ext l (UrTy l)))
       -> FunDefs (PreExp E1Ext l (UrTy l))
       -> (PreExp E1Ext l (UrTy l))
       -> WriterT Log IO Value
interp rc _ddefs fenv = go M.empty
  where
    {-# NOINLINE goWrapper #-}
    goWrapper !_ix env ex = go env ex

    go :: ValEnv -> (PreExp E1Ext l (UrTy l)) -> WriterT Log IO Value
    go env x0 =
        case x0 of
          Ext (BenchE fn locs args _b) -> go env ( AppE fn locs args)
          Ext (AddFixed{}) -> error "L1.Interp: AddFixed not handled."

          LitE c    -> return $ VInt c
          FloatE c  -> return $ VFloat c
          LitSymE s -> return $ VSym (fromVar s)
          VarE v    -> return $ env # v

          -- Don't sort for now
          PrimAppE (VSortP{}) [ls,VarE fp] -> do
            (VList vals) <- go env ls
            applySortP env vals fp

          LetE (_,_,_, PrimAppE (InPlaceVSortP{}) [ls, VarE fp]) bod -> do
            old_v@(VList vals) <- go env ls
            val <- applySortP env vals fp
            -- go (M.insert )
            let mp = M.filter (== old_v) env
            case M.keys mp of
              [one] -> go (M.insert one val env) bod
              []    -> error "L1.Interp: InPlaceSortP no accessor found"
              oth   -> go (M.insert (last oth) val env) bod

          LetE (_,_,_, PrimAppE (InPlaceVSnocP{}) [ls, arg]) bod -> do
            old_v@(VList vals) <- go env ls
            v <- go env arg
            let new_ls = VList (vals ++ [v])
            -- go (M.insert )
            let mp = M.filter (== old_v) env
            case M.keys mp of
              [one] -> go (M.insert one new_ls env) bod
              []    -> error "L1.Interp: InPlaceSnocP no accessor found"
              oth   -> go (M.insert (last oth) new_ls env) bod

          PrimAppE p ls -> do args <- mapM (go env) ls
                              return $ applyPrim rc p args
          ProjE ix ex   -> do VProd ls <- go env ex
                              return $ ls !!! ix

          AppE f _ ls -> do ls' <- mapM (go env) ls
                            case M.lookup f fenv of
                             Just fn -> go (M.union (M.fromList (zip (funArgs fn) ls')) env) (funBody fn)
                             Nothing -> error $ "L1.Interp: unbound function in application: "++ndoc x0

          CaseE _ [] -> error$ "L1.Interp: CaseE with empty alternatives list: "++ndoc x0

          CaseE x1 alts@((_sometag,_,_):_) -> do
                 v <- go env x1
                 case v of
                   VPacked k ls2 ->
                       let vs = L.map fst prs
                           (_,prs,rhs) = lookup3 k alts
                           env' = M.union (M.fromList (zip vs ls2)) env
                       in go env' rhs
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
              val <- foldM (\ _ i -> goWrapper i env bod)
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

          WithArenaE v e -> let env' = M.insert v (VInt 0) env
                            in go env' e

          IfE a b c -> do v <- go env a
                          case v of
                           VBool flg -> if flg
                                        then go env b
                                        else go env c
                           oth -> error$ "interp: expected bool, got: "++show oth

          MapE _ _bod    -> error "L1.Interp: finish MapE"
          FoldE _ _ _bod -> error "L1.Interp: finish FoldE"
    applySortP :: ValEnv -> [Value] -> Var -> WriterT Log IO Value
    applySortP env ls f = do
      let fn  = case M.lookup f fenv of
                  Just fun -> fun
                  Nothing -> error $ "L1.Interp: unbound function given to vsort: "++ndoc f
          ls' = sortBy
                (\a b ->
                     let env' = M.union (M.fromList (zip (funArgs fn) [a,b])) env
                         (i,_) =
                           unsafePerformIO $ (runWriterT (go env' (funBody fn)))
                         VInt j = i
                     in compare j 0)
                ls
      pure (VList ls')


applyPrim :: (Show l) => RunConfig -> Prim (UrTy l) -> [Value] -> Value
applyPrim rc p ls =
 case (p,ls) of
   (MkTrue,[])             -> VBool True
   (MkFalse,[])            -> VBool False
   -- FIXME: randomIO does not guarentee unique numbers every time.
   (Gensym, [])            -> VSym $ "gensym_" ++ (show $ (unsafePerformIO randomIO :: Int) `mod` 1000)
   (AddP,[VInt x, VInt y]) -> VInt (x+y)
   (SubP,[VInt x, VInt y]) -> VInt (x-y)
   (MulP,[VInt x, VInt y]) -> VInt (x*y)
   (DivP,[VInt x, VInt y]) -> VInt (x `quot` y)
   (ModP,[VInt x, VInt y]) -> VInt (x `rem` y)
   (ExpP,[VInt x, VInt y]) -> VInt (x ^ y)
   (FAddP,[VFloat x, VFloat y]) -> VFloat (x+y)
   (FSubP,[VFloat x, VFloat y]) -> VFloat (x-y)
   (FMulP,[VFloat x, VFloat y]) -> VFloat (x*y)
   (FDivP,[VFloat x, VFloat y]) -> VFloat (x / y)
   (FExpP,[VFloat x, VFloat y]) -> VFloat (x ** y)
   -- Constrained to the value of RAND_MAX (in C) on my laptop: 2147483647 (2^31 − 1)
   (RandP,[]) -> VInt $ (unsafePerformIO randomIO) `mod` 2147483647
   (FRandP,[]) -> VFloat $ (unsafePerformIO randomIO) / 2147483647
   (IntToFloatP,[VInt x]) -> VFloat (fromIntegral x)
   (FloatToIntP,[VFloat x]) -> VInt (round x)
   (FSqrtP,[VFloat x]) -> VFloat (sqrt x)
   (SymAppend,[VInt x, VInt y]) -> VInt (x * (strToInt $ show y))
   (EqSymP,[VSym x, VSym y]) -> VBool (x==y)
   (EqIntP,[VInt x, VInt y]) -> VBool (x==y)
   (EqFloatP,[VFloat x, VFloat y]) -> VBool (x==y)
   (LtP,[VInt x, VInt y]) -> VBool (x < y)
   (GtP,[VInt x, VInt y]) -> VBool (x > y)
   (LtEqP,[VInt x, VInt y]) -> VBool (x <= y)
   (GtEqP,[VInt x, VInt y]) -> VBool (x >= y)
   (FLtP,[VFloat x, VFloat y]) -> VBool (x < y)
   (FGtP,[VFloat x, VFloat y]) -> VBool (x > y)
   (FLtEqP,[VFloat x, VFloat y]) -> VBool (x <= y)
   (FGtEqP,[VFloat x, VFloat y]) -> VBool (x >= y)
   (AndP, [VBool x, VBool y]) -> VBool (x && y)
   (OrP, [VBool x, VBool y])  -> VBool (x || y)
   ((DictInsertP _ty),[_, VDict mp, key, val]) -> VDict (M.insert key val mp)
   ((DictLookupP _),[VDict mp, key])        -> mp # key
   ((DictHasKeyP _),[VDict mp, key])        -> VBool (M.member key mp)
   ((DictEmptyP _),[_])                      -> VDict M.empty
   ((ErrorP msg _ty),[]) -> error msg
   (SizeParam,[]) -> VInt (rcSize rc)
   (IsBig,[_one,_two]) -> VBool False
   (ReadPackedFile file _ _ ty,[]) ->
       error $ "L1.Interp: unfinished, need to read a packed file: "++show (file,ty)
   (ReadArrayFile{},[]) -> VList []
   (VEmptyP _,[]) -> VList []
   (VNthP _,[VInt n, VList ls]) -> ls !!! n
   (VLengthP _,[VList ls]) -> VInt (length ls)
   (VUpdateP _,[VList ls, VInt i, v]) -> if length ls < i
                                         then error $ "L1.Interp: VUpdate"
                                         else VList (replaceNth i v ls)
   (VSnocP _,[VList ls, v]) -> VList (ls ++ [v])
   (VSliceP _,[VList ls, VInt from, VInt to]) ->
     VList (L.take (to - from + 1) (L.drop from ls))
   oth -> error $ "unhandled prim or wrong number of arguments: "++show oth

  where
     replaceNth :: Int -> a -> [a] -> [a]
     replaceNth _ _ [] = []
     replaceNth n newVal (x:xs)
       | n == 0 = newVal:xs
       | otherwise = x:replaceNth (n-1) newVal xs

clk :: Clock
clk = Monotonic

type Log = Builder

strToInt :: String -> Int
strToInt = product . L.map ord
