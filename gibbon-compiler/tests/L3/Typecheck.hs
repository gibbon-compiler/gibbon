{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

module L3.Typecheck where

import Gibbon.Passes.InferEffects
import Gibbon.Passes.InferMultiplicity
import Gibbon.Passes.RouteEnds
import Gibbon.Passes.BoundsCheck
import Gibbon.Passes.ThreadRegions
import Gibbon.Passes.Cursorize
import Gibbon.Passes.Unariser
import Gibbon.Passes.ShakeTree
import Gibbon.Passes.HoistNewBuf
import Gibbon.Passes.FindWitnesses
import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L1.Syntax hiding (FunDef, Prog, add1Prog)
import Gibbon.L2.Syntax
import Gibbon.L2.Examples
import qualified Gibbon.L2.Typecheck as L2
import qualified Gibbon.L3.Typecheck as L3
import qualified Gibbon.L3.Syntax as L3

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

runT :: Prog -> L3.Prog
runT prg = fst $ runSyM 0 $ do
  l2 <- inferEffects prg
  l2 <- inferRegScope Infinite l2
  l2 <- L2.tcProg l2
  l2 <- routeEnds l2
  l2 <- L2.tcProg l2
  l2 <- boundsCheck l2
  l2 <- threadRegions l2
  l3 <- cursorize defaultDynFlags l2
  l3 <- findWitnesses l3
  l3 <- L3.tcProg l3
  l3 <- shakeTree l3
  l3 <- hoistNewBuf l3
  l3 <- unariser l3
  L3.tcProg l3

l3TypecheckerTests :: TestTree
l3TypecheckerTests = $(testGroupGenerator)

-- | just a dummy assertion, but we check that runT doesn't raise an exception
case_run_add1 :: Assertion
case_run_add1 = res @=? res
  where res = runT add1Prog

case_run_intAdd :: Assertion
case_run_intAdd = res @=? res
  where res = runT intAddProg
