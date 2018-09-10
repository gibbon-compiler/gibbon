{-# LANGUAGE FlexibleInstances #-}

-- | Flatten ported to L2.

module Gibbon.Passes.Flatten2 where

-- import Control.Monad.State
import Text.PrettyPrint.GenericPretty (Out)
-- import qualified Data.Map as M
import Prelude hiding (exp)

import Gibbon.Common
import Gibbon.GenericOps
import Gibbon.L1.Syntax () -- Instances
import Gibbon.L2.Syntax as L2
import Gibbon.GenericOps (Flattenable, gFlattenExp,gFlattenGatherBinds)
-- import Gibbon.Passes.Flatten (TEnv)


-- ddfs
-- Expected type: DDefs (TyOf (e l (UrTy l)))
-- Actual type: DDefs (TyOf (PreExp e l (UrTy l)))

instance (Show l, Out l, Expression (e l (UrTy l))) => Flattenable (PreExp e l (UrTy l)) where
  gFlattenExp ddfs env2 exp =
    case exp of
      LitE _  -> return exp
      Ext ext -> Ext <$> gFlattenExp ddfs env2 ext

{-
-- | Just like Flatten.hs, but on L2.
flatten2 :: L2.Prog -> SyM L2.Prog
flatten2 prg@(L2.Prog ddefs _ _) = L2.mapMExprs fn prg
  where
   fn :: Env2 (UrTy LocVar) -> L2.Exp2 -> SyM L2.Exp2
   fn env2 ex = gFlattenExp ddefs env2 ex

type Binds l e = (Var,[l],UrTy l, PreExp e l (UrTy l))

-- instance Flattenable Exp2 where

-- instance (Show l, Show d, Out l, Out d) =>
--          Flattenable (PreExp l (E2Ext l d) d) where
--  gFlattenExp = _
--   where
--    exp :: TEnv l -> PreExp l e (UrTy l) -> SyM ([Binds l e],PreExp l e (UrTy l))
--    exp tenv ex =
--      case ex of
--        Ext ext -> case ext of
--                    LetRegionE r bod -> _
--        oth -> gFlattenExp

instance (Show l, Show d, Out l, Out d) =>
         Flattenable (E2Ext l d) where
 gFlattenExp = error $ "FINISHME: Flatten2 gFlattenExp"
  where
   _exp :: TEnv l -> E2Ext l d -> SyM ([Binds l e],E2Ext l d)
   _exp _ _ = error $ "FINISHME: Flatten2 gFlattenExp"

 gFlattenGatherBinds = error $ "FINISHME: Flatten2 gFlattenGatherBinds"

-}
