{-# LANGUAGE TemplateHaskell #-}

-- | Fully-factored (SoA) indirections: when a re-placement is refused, how
-- buffers are counted, and the whole-program test that selects the factored
-- INDIRECTION arm.
module FactoredIndirections (factoredIndirectionsTests) where

import Data.List (isInfixOf)
import qualified Data.Map as M
import Data.Maybe (isJust, isNothing)
import Gibbon.Common
import Gibbon.L2.Syntax
import Gibbon.Passes.RemoveCopies
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

-- | A Tree-like SoA location: a tag buffer and one scalar buffer.
soa :: String -> LocVar
soa n = SoA (toVar n) [(("Leaf", 0), Single (toVar (n ++ "_f0")))]

-- | @lin@ placed @k@ bytes after @lout@ in the tag buffer.
offsetBy :: Int -> OffEnv
offsetBy k = learnOffset (soa "i") (AfterConstantLE k (soa "o")) M.empty

refused :: OffEnv -> LocVar -> LocVar -> Maybe String
refused = unsupportedReplacement False

case_buffer_count_includes_nested_fields :: Assertion
case_buffer_count_includes_nested_fields =
  locBufferCount (SoA "t" [ (("N", 0), Single "f")
                          , (("N", 1), SoA "p" [(("P", 0), Single "q")]) ])
    @?= 4

case_tag_bytes_are_a_tag_and_one_cursor_per_buffer :: Assertion
case_tag_bytes_are_a_tag_and_one_cursor_per_buffer =
  soaIndirectionTagBytes (soa "o") @?= 17

case_coinciding_tags_are_refused :: Assertion
case_coinciding_tags_are_refused =
  case refused (offsetBy 0) (soa "i") (soa "o") of
    Just why -> assertBool why ("tag-buffer start is only 0 bytes" `isInfixOf` why)
    Nothing -> assertFailure "a re-placement onto the value's own tag was accepted"

case_a_node_that_would_reach_the_value_is_refused :: Assertion
case_a_node_that_would_reach_the_value_is_refused =
  assertBool "16 bytes is short of 17" (isJust (refused (offsetBy 16) (soa "i") (soa "o")))

case_a_node_that_fits_becomes_an_indirection :: Assertion
case_a_node_that_fits_becomes_an_indirection =
  assertBool "17 bytes fits" (isNothing (refused (offsetBy 17) (soa "i") (soa "o")))

case_unrelated_locations_become_an_indirection :: Assertion
case_unrelated_locations_become_an_indirection =
  assertBool "different roots" (isNothing (refused M.empty (soa "i") (soa "o")))

-- | Mutable cursors keep AoS copies; a factored copy still becomes an
-- indirection, so the same-region rule for kept copies does not apply.
case_mutable_cursors_do_not_refuse_a_factored_indirection :: Assertion
case_mutable_cursors_do_not_refuse_a_factored_indirection =
  assertBool "kept-copy rule applied to SoA"
    (isNothing (unsupportedReplacement True (offsetBy 17) (soa "i") (soa "o")))

case_mixed_layouts_are_refused :: Assertion
case_mixed_layouts_are_refused =
  assertBool "SoA to single" (isJust (refused M.empty (soa "i") (Single "o")))

-- | A program whose main expression is one indirection at the given locations.
indirectionProg :: LocVar -> LocVar -> Prog2
indirectionProg lout lin =
  Prog M.empty M.empty
       (Just ( Ext (IndirectionE "Tree" "INDIRECTION_1" (lout, lout) (lin, lin) (VarE "t"))
             , PackedTy "Tree" lout ))

case_factored_indirection_is_detected :: Assertion
case_factored_indirection_is_detected =
  writesFactoredIndirections isSoALoc (indirectionProg (soa "o") (soa "i")) @?= True

case_linear_indirection_is_not_factored :: Assertion
case_linear_indirection_is_not_factored =
  writesFactoredIndirections isSoALoc (indirectionProg (Single "o") (Single "i")) @?= False

factoredIndirectionsTests :: TestTree
factoredIndirectionsTests = $(testGroupGenerator)
