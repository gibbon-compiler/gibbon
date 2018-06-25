{-# LANGUAGE TemplateHaskell #-}

-- | Tests for AddLayout
--
module AddLayout
  (addLayoutTests) where

import Data.Set as S
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Passes.AddLayout
import Gibbon.Passes.InferEffects
import Gibbon.Passes.RemoveCopies
import Gibbon.L2.Examples

runner prg = fst $ defaultPackedRunPassM $ do
  l2 <- removeCopies prg
  l2 <- inferEffects l2
  return $ needsLayout l2

case_rightmost :: Assertion
case_rightmost = S.singleton "Tree" @=? runner rightmostProg

case_leftmost :: Assertion
case_leftmost = S.empty @=? runner leftmostProg

case_add1 :: Assertion
case_add1 = S.empty @=? runner add1Prog

addLayoutTests :: TestTree
addLayoutTests = $(testGroupGenerator)
