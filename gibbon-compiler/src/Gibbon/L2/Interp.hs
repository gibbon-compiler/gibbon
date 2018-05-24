{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Interpreter reducing L2 programs to values.

module Gibbon.L2.Interp () where

import           Control.Monad.Writer
import           Control.Monad.State
import           Data.Loc
import           Text.PrettyPrint.GenericPretty
import           System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Sequence as S

import           Gibbon.Common
import           Gibbon.GenericOps
import           Gibbon.L1.Syntax as L1
import           Gibbon.L1.Interp as L1
import           Gibbon.L2.Syntax as L2

instance Interp Prog2 where
  interpNoLogs rc p = unsafePerformIO $ show . fst <$> L1.interpProg rc p
  interpWithStdout rc p = do
   (v,logs) <- L1.interpProg rc p
   return (show v, lines (B.unpack logs))


instance (Out d, Out l, Show l, Show d) => InterpE (E2Ext l d) where
    type ExpTy (E2Ext l d) = L (PreExp E2Ext l (UrTy l))
    interpE = interpE2Ext

interpE2Ext :: RunConfig
            -> DDefs (TyOf (E2Ext l d))
            -> M.Map Var (FunDef (UrTy l) (L (PreExp e l (UrTy l))))
            -> E2Ext l d
            -> WriterT Log (StateT Store IO) Value
interpE2Ext _rc _ddefs _fenv _ext = error "TODO: interpE2Ext"
