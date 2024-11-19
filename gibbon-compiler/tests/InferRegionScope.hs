{-# LANGUAGE TemplateHaskell #-}

-- | Tests for RouteEnds2
--
module InferRegionScope where

import Data.Set as S
import Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common hiding (FunDef)
import Gibbon.L2.Syntax as L2
import Gibbon.L2.Examples
import Gibbon.Passes.InferRegionScope
import qualified Gibbon.L1.Syntax as L1


-- Region escapes scope, hence is global
case_t1 :: Assertion
case_t1 = expected @=? actual
  where
    actual = fst $ defaultPackedRunPassM $ inferRegScopeExp M.empty test1

    test1 :: L2.Exp2
    test1 = Ext $ LetRegionE (VarR "r1") Undefined Nothing $
            Ext $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1")) $
            LetE ("x1",[],PackedTy "A" (singleLocVar "l1"),
                     DataConE (singleLocVar "l1") "A" [LitE 1]) $
            VarE "x1"

    expected :: L2.Exp2
    expected = Ext $ LetRegionE (GlobR "r1" Infinite) Undefined Nothing $
               Ext $ LetLocE (singleLocVar "l1") (StartOfRegionLE (GlobR "r1" Infinite)) $
               LetE ("x1",[],PackedTy "A" (singleLocVar "l1"),
                        DataConE (singleLocVar "l1") "A" [LitE 1]) $
               VarE "x1"



-- A local, stack allocated region
case_t2 :: Assertion
case_t2 = expected @=? actual
  where
    actual = fst $ defaultPackedRunPassM $ inferRegScopeExp M.empty test1

    test1 :: L2.Exp2
    test1 = Ext $ LetRegionE (VarR "r1") Undefined Nothing $
            Ext $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1")) $
            LetE ("x1",[],PackedTy "A" (singleLocVar "l1"),
                     DataConE (singleLocVar "l1") "A" [LitE 1]) $
            LitE 1

    expected :: L2.Exp2
    expected = Ext $ LetRegionE (GlobR "r1" Infinite) Undefined Nothing $
               Ext $ LetLocE (singleLocVar "l1") (StartOfRegionLE (GlobR "r1" Infinite)) $
               LetE ("x1",[],PackedTy "A" (singleLocVar "l1"),
                        DataConE (singleLocVar "l1") "A" [LitE 1]) $
               LitE 1

inferRegScopeTests :: TestTree
inferRegScopeTests = $(testGroupGenerator)
