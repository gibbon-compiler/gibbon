{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Interpreter for the source language (L0)
module Gibbon.L0.Interp where

import qualified Data.Map.Lazy as M

import           Gibbon.Common
import           Gibbon.L0.Syntax
import qualified Gibbon.L1.Interp as L1

--------------------------------------------------------------------------------

instance InterpExt () Exp0 (E0Ext Ty0 Ty0) where
  gInterpExt rc valenv ddefs fundefs ex =
      case ex of
        LambdaE args bod -> return (VLam (map fst args) bod valenv)
        FunRefE _tyapps f ->
          case M.lookup f valenv of
            Just lam -> pure lam
            Nothing  ->
              case M.lookup f fundefs of
                Nothing -> error $ "L0.Interp: Unbound function reference: " ++ sdoc f
                Just fn -> pure $ VLam (funArgs fn) (funBody fn) M.empty
        BenchE fn locs args _b ->
          gInterpExp rc valenv ddefs fundefs (AppE fn locs args)
        ParE0 ls -> gInterpExp rc valenv ddefs fundefs (MkProdE ls)
        PrintPacked _ty _arg -> pure $ VProd []
        CopyPacked _ty arg -> gInterpExp rc valenv ddefs fundefs arg
        TravPacked _ty _arg -> pure $ VProd []
        L _ e -> gInterpExp rc valenv ddefs fundefs e
        PolyAppE{} -> error "L0.Interp: PolyAppE not handled."
        LinearExt{} -> error $ "L0.Interp: a linear types extension wasn't desugared: " ++ sdoc ex

instance Interp () Exp0 where
  gInterpExp  = L1.interp

instance InterpProg () Exp0 where
  gInterpProg _s = L1.interpProg
