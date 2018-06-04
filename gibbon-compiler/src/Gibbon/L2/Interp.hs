{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Interpreter reducing L2 programs to values.

module Gibbon.L2.Interp () where

import           Control.DeepSeq
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.ByteString.Builder (toLazyByteString, string8)
import           Data.Loc
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

interp :: RunConfig -> DDefs Ty2 -> M.Map Var (FunDef (L Exp2)) -> L Exp2
        -> WriterT Log (StateT Store IO) Value
interp rc ddefs fenv = go M.empty
  where
    {-# NOINLINE goWrapper #-}
    goWrapper !_ix env ex = go env ex

    go :: ValEnv -> L Exp2 -> WriterT Log (StateT Store IO) Value
    go env (L _ ex) =
      case ex of
        AppE{} -> error $ "TODO: L2.Interp" ++ sdoc ex
        CaseE{} -> error $ "TODO: L2.Interp" ++ sdoc ex
        DataConE{} -> error $ "TODO: L2.Interp" ++ sdoc ex
        Ext{} -> error $ "TODO: L2.Interp" ++ sdoc ex

        -- Straightforward recursion (same as the L1 interpreter)
        LitE n    -> return $ VInt n
        LitSymE s -> return $ VInt (strToInt $ fromVar s)
        VarE v    -> return $ env # v

        PrimAppE p args -> do args' <- mapM (go env) args
                              return $ L1.applyPrim rc p args'

        ProjE ix ex -> do VProd ls <- go env ex
                          return $ ls !! ix

        MkProdE ls -> VProd <$> mapM (go env) ls

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

clk :: Clock
clk = Monotonic
