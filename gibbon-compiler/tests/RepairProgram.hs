{-# LANGUAGE TemplateHaskell #-}

-- | Tests for AddLayout
--
module RepairProgram
  (repairProgramTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Passes.RepairProgram
import Gibbon.Passes.InferEffects
import Gibbon.L2.Examples

runner prg = fst $ defaultPackedRunPassM $ do
  l2 <- inferEffects prg
  let (needs,_) = needsRepair l2
  return needs

case_rightmost :: Assertion
case_rightmost = True @=? runner rightmostProg

case_leftmost :: Assertion
case_leftmost = False @=? runner leftmostProg

case_add1 :: Assertion
case_add1 = False @=? runner add1Prog

repairProgramTests :: TestTree
repairProgramTests = $(testGroupGenerator)
