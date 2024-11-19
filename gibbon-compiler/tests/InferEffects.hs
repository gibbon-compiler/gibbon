{-# LANGUAGE TemplateHaskell #-}

-- | Tests for RouteEnds2
--
module InferEffects where

import Data.Set as S
import Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.L2.Syntax as L2
import Gibbon.L2.Examples
import Gibbon.Passes.InferEffects
import Gibbon.L1.Syntax as L1


assertInferEffects :: Prog2 -> Var -> Set Effect -> Assertion
assertInferEffects prg fnName expected = expected @=? eff
  where -- run inferEffects and get the effect from it's type
        Prog{fundefs} = fst $ defaultPackedRunPassM $ inferEffects prg
        eff = arrEffs $ funTy (fundefs ! fnName)


-- | Add1 function has a traversal effect [Traverse "lin2"]
--
case_add1 :: Assertion
case_add1 = assertInferEffects add1Prog "add1" (S.singleton $ Traverse (singleLocVar "lin2"))

-- | Identity fn doesn't have any traversal effect
case_id1 :: Assertion
case_id1 = assertInferEffects id1Prog "id1" S.empty

-- | Copying has a traversal effect
case_copyTree :: Assertion
case_copyTree =  assertInferEffects copyTreeProg "copyTree" (S.singleton $ Traverse (singleLocVar "lin23"))

-- | Call copy on the body of id1
case_call_copy_on_id1 :: Assertion
case_call_copy_on_id1 = assertInferEffects copyOnId1Prog "id1WithCopy" (S.singleton $ Traverse (singleLocVar "lin19"))

case_id2 :: Assertion
case_id2 = assertInferEffects id2Prog "id2" S.empty

case_id3 :: Assertion
case_id3 = assertInferEffects id3Prog "id3" S.empty

case_int_add :: Assertion
case_int_add = assertInferEffects intAddProg "intAdd" S.empty

case_packed_tuple :: Assertion
case_packed_tuple = assertInferEffects testProdProg "testprod" (S.singleton $ Traverse (singleLocVar "lin131"))

inferEffects2Tests :: TestTree
inferEffects2Tests = $(testGroupGenerator)
