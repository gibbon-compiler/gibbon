{-# LANGUAGE TemplateHaskell #-}

-- | Tests for L2.Interp
--
module L2.Interp
  (l2InterpTests) where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Data.Map as M

import Gibbon.Common
import Gibbon.Language
import Gibbon.L2.Interp
import Gibbon.L2.Examples as L2

case_leafProg :: Assertion
case_leafProg = "(Leaf 1)" @=? gInterpNoLogs emptyStore defaultRunConfig leafProg

case_nodeProg :: Assertion
case_nodeProg = "(Node (Leaf 1) (Leaf 2))" @=? gInterpNoLogs emptyStore defaultRunConfig nodeProg

l2InterpTests :: TestTree
l2InterpTests = $(testGroupGenerator)
