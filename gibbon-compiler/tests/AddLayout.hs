{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Tests for AddLayout
--
module AddLayout where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Passes.AddLayout
import Gibbon.Passes.InferEffects
import Gibbon.L2.Examples

runner prg = fst $ runSyM 0 $ do
  l2 <- inferEffects prg
  let (needs,_) = needsLayout l2
  return needs

case_rightmost :: Assertion
case_rightmost = True @=? runner rightmostProg

case_leftmost :: Assertion
case_leftmost = False @=? runner leftmostProg

case_add1 :: Assertion
case_add1 = False @=? runner add1Prog

addLayoutTests :: TestTree
addLayoutTests = $(testGroupGenerator)
