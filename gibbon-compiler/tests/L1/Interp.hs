{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests for L1.Interp
--
module L1.Interp (l1InterpTests) where

import Data.Loc
import Data.Map as M

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Gibbon.Common
import Gibbon.Interp
import Gibbon.L1.Syntax as L1
import Gibbon.L1.Interp as L1

--------------------------------------------------------------------------------

p1 :: Prog1
p1 = Prog emptyDD M.empty
          (Just ( l$ LetE ("x", [], IntTy, l$ LitE 3) $
                  l$ VarE "x"
                , IntTy ))

case_test1 :: Assertion
case_test1 = "3" @=? interpNoLogs (RunConfig 1 1 dbgLvl False) p1

--------------------------------------------------------------------------------

l1InterpTests :: TestTree
l1InterpTests = $(testGroupGenerator)
