{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Tests for RouteEnds2
--
module InferMultiplicity where

import Data.Loc
import Data.Set as S
import Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Packed.FirstOrder.Common hiding (FunDef)
import Packed.FirstOrder.L2.Syntax as L2
import Packed.FirstOrder.L2.Examples
import Packed.FirstOrder.Passes.InferMultiplicity
import qualified Packed.FirstOrder.L1.Syntax as L1


-- Region escapes scope, hence is global
case_t1 :: Assertion
case_t1 = expected @=? actual
  where
    actual = inferRegScopeExp Infinite test1

    test1 :: L L2.Exp2
    test1 = l$ Ext $ LetRegionE (VarR "r1") $
            l$ Ext $ LetLocE "l1" (StartOfLE (VarR "r1")) $
            l$ LetE ("x1",[],PackedTy "A" "l1",
                     l$ DataConE "l1" "A" [l$ LitE 1]) $
            l$ VarE "x1"

    expected :: L L2.Exp2
    expected = l$ Ext $ LetRegionE (GlobR "r1" Infinite) $
               l$ Ext $ LetLocE "l1" (StartOfLE (VarR "r1")) $
               l$ LetE ("x1",[],PackedTy "A" "l1",
                        l$ DataConE "l1" "A" [l$ LitE 1]) $
               l$ VarE "x1"



-- A local, stack allocated region
case_t2 :: Assertion
case_t2 = expected @=? actual
  where
    actual = inferRegScopeExp Infinite test1

    test1 :: L L2.Exp2
    test1 = l$ Ext $ LetRegionE (VarR "r1") $
            l$ Ext $ LetLocE "l1" (StartOfLE (VarR "r1")) $
            l$ LetE ("x1",[],PackedTy "A" "l1",
                     l$ DataConE "l1" "A" [l$ LitE 1]) $
            l$ LitE 1

    expected :: L L2.Exp2
    expected = l$ Ext $ LetRegionE (GlobR "r1" Infinite) $
               l$ Ext $ LetLocE "l1" (StartOfLE (VarR "r1")) $
               l$ LetE ("x1",[],PackedTy "A" "l1",
                        l$ DataConE "l1" "A" [l$ LitE 1]) $
               l$ LitE 1

inferRegScopeTests :: TestTree
inferRegScopeTests = $(testGroupGenerator)
