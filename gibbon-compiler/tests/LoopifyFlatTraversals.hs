{-# LANGUAGE TemplateHaskell #-}

-- | Tests for 'Gibbon.Passes.LoopifyFlatTraversals', the flat AoS loopifier.
--
-- The pass turns a recursive traversal into a single cursor walk, so every
-- test here is about a refusal: which bodies may NOT become a loop, and why.
module LoopifyFlatTraversals
  ( loopifyFlatTraversalsTests
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language
import qualified Gibbon.L2.Syntax as L2
import Gibbon.L3.Syntax
import Gibbon.Passes.LoopifyFlatTraversals
import Gibbon.Passes.LoopifyTraversals (trulyInvariantArgs)

selfName :: Var
selfName = "walk"

selfCall :: [Exp3] -> Exp3
selfCall = AppE selfName NotTailRec []

otherCall :: [Exp3] -> Exp3
otherCall = AppE "consumeOne" NotTailRec []

-- 'hasUnerasableCall': erasure rewrites `AppE f | f == walk` and nothing
-- else, so anything else it leaves behind runs once per node.

case_self_calls_alone_are_erasable :: Assertion
case_self_calls_alone_are_erasable =
  assertBool "a body whose only calls are ordinary self-calls is erasable"
             (not (hasUnerasableCall selfName
                     (LetE ("r", [], ProdTy [], selfCall [VarE "child"])
                           (MkProdE []))))

-- | A call erasure cannot remove survives into the loop body, where it re-runs
-- once per node and consumes extra input.
case_non_self_call_is_refused :: Assertion
case_non_self_call_is_refused =
  assertBool "a call erasure cannot remove must refuse the candidate"
             (hasUnerasableCall selfName
                (LetE ("r", [], ProdTy [], otherCall [VarE "child"])
                      (MkProdE [])))

-- | 'eraseSelfCallsExt' has no equation for a spawned self-call, so it
-- survives into the loop body even though it names the function itself.
case_spawned_self_call_is_refused :: Assertion
case_spawned_self_call_is_refused =
  assertBool "a spawned self-call is not erased, so it must be refused"
             (hasUnerasableCall selfName (SpawnE selfName [] [VarE "child"]))

-- | The traversal gap the same finding exposed: a call hidden inside another
-- call's arguments was invisible to the collector.
case_non_self_call_nested_in_call_argument_is_refused :: Assertion
case_non_self_call_nested_in_call_argument_is_refused =
  assertBool "a call nested in a self-call's arguments is still found"
             (hasUnerasableCall selfName
                (selfCall [otherCall [VarE "child"]]))

-- | ... and inside a `PrimAppE`'s arguments.
case_non_self_call_nested_in_primapp_is_refused :: Assertion
case_non_self_call_nested_in_primapp_is_refused =
  assertBool "a call nested in a PrimAppE argument is still found"
             (hasUnerasableCall selfName
                (PrimAppE addP64 [otherCall [VarE "child"], mkLitE64 1]))

-- | ... and underneath an extension node, which the hand-written ext
-- traversal used to fall through.
case_non_self_call_under_ext_is_refused :: Assertion
case_non_self_call_under_ext_is_refused =
  assertBool "a call under an Ext node is still found"
             (hasUnerasableCall selfName
                (Ext (Assert (otherCall [VarE "child"]))))

-- 'trulyInvariantArgs' decides the flat pass's argument guard: every formal
-- past the ABI cursor block is read once at entry, so the recursion must
-- pass it through unchanged.

case_flat_abi_cursor_count_is_four :: Assertion
case_flat_abi_cursor_count_is_four =
  assertEqual "mutable-cursor AoS cursorization spends four leading formals"
              4 flatAbiCursorCount

case_flat_scalar_formal_must_pass_through :: Assertion
case_flat_scalar_formal_must_pass_through =
  let formals = ["end_r", "end_r2", "out_loc", "in_cur", "k"]
      -- `walk l (k+1)`: the scalar is rebound, so it is not invariant and the
      -- guard on the formals past the cursor block fails.
      body = LetE ("k2", [], IntTy W64, PrimAppE addP64 [VarE "k", mkLitE64 1])
                  (LetE ("r", [], ProdTy [],
                         selfCall [VarE "end_r", VarE "end_r2", VarE "out_loc",
                                   VarE "child", VarE "k2"])
                        (MkProdE []))
      invariant = trulyInvariantArgs selfName formals body
   in assertBool "a rebound scalar formal is not loop invariant"
                 (not (all (`S.member` invariant) (drop flatAbiCursorCount formals)))

case_flat_scalar_formal_passed_through_is_accepted :: Assertion
case_flat_scalar_formal_passed_through_is_accepted =
  let formals = ["end_r", "end_r2", "out_loc", "in_cur", "k"]
      -- `walk l k`: the corpus shape (DomTree scaleLayout and friends).
      body = LetE ("r", [], ProdTy [],
                   selfCall [VarE "end_r", VarE "end_r2", VarE "out_loc",
                             VarE "child", VarE "k"])
                  (MkProdE [])
      invariant = trulyInvariantArgs selfName formals body
   in assertBool "a scalar formal passed straight back through is invariant"
                 (all (`S.member` invariant) (drop flatAbiCursorCount formals))

-- 'hasObservableEffect': the loop visits nodes in memory order, the
-- recursion visited them in DFS order, so an observable effect must refuse
-- the candidate.

case_pure_arithmetic_is_not_an_observable_effect :: Assertion
case_pure_arithmetic_is_not_an_observable_effect =
  assertBool "total arithmetic may be reordered"
             (not (hasObservableEffect
                     (PrimAppE addP64 [VarE "x", mkLitE64 1])))

-- | Printing reorders with the traversal while the values still agree, so a
-- value-only oracle sees nothing.
case_printing_is_an_observable_effect :: Assertion
case_printing_is_an_observable_effect =
  assertBool "a print in the body must refuse the candidate"
             (hasObservableEffect
                (LetE ("p", [], ProdTy [], PrimAppE (PrintInt (IntPrimWidth W64)) [VarE "x"])
                      (MkProdE [])))

-- | Trapping arithmetic is deliberately NOT refused: reordering two aborts
-- is not observable, and a body that both traps and prints is refused for
-- the printing.  The guarded-division corpus cases depend on this.
case_trapping_division_is_not_refused :: Assertion
case_trapping_division_is_not_refused =
  assertBool "a guarded division must still be loopifiable"
             (not (hasObservableEffect
                     (PrimAppE (DivP (IntPrimWidth W64)) [VarE "x", VarE "y"])))

-- | An effect under an extension node is still an effect.
case_effect_under_ext_is_found :: Assertion
case_effect_under_ext_is_found =
  assertBool "a print under an Ext node is still found"
             (hasObservableEffect
                (Ext (WriteScalar (IntS W64) "cur" (PrimAppE (PrintInt (IntPrimWidth W64)) [VarE "x"]))))

-- 'callerEndsAreValueEnds': the emitted loop stops at
-- `while (*input_cursor != *input_end)`, so what CALLERS pass at the end
-- position decides whether it stops at the value's end or runs off the data.

-- | @walk@ in the flat AoS ABI: (inputEnd, outputRegionEnd, outputLoc,
-- inputStart).  Its body bumps the output location and the input cursor,
-- which is what makes a call to it evidence of a value end.
walkFun :: FunDef3
walkFun =
  FunDef { funName = selfName
         , funArgs = ["in_end", "out_end", "out_loc", "in_cur"]
         , funTy = (replicate 4 MutCursorTy, ProdTy [])
         , funBody =
             LetE ("b1", [], ProdTy [], Ext (BumpCursorMutable "out_loc" (mkLitE64 1)))
                  (LetE ("b2", [], ProdTy [], Ext (BumpCursorMutable "in_cur" (mkLitE64 1)))
                        (MkProdE []))
         , funMeta = FunMeta Rec NoInline False [MayVectorize] Nothing
         }

-- | A producer: (outputRegionEnd, outputLoc, n).  It advances its output
-- location, which is what makes a call to it evidence that the cursor now
-- holds the end of the value it wrote.
buildFun :: FunDef3
buildFun =
  FunDef { funName = "build"
         , funArgs = ["out_end", "out_loc", "n"]
         , funTy = ([MutCursorTy, MutCursorTy, IntTy W64], ProdTy [])
         , funBody =
             LetE ("b", [], ProdTy [], Ext (BumpCursorMutable "out_loc" (mkLitE64 1)))
                  (MkProdE [])
         , funMeta = FunMeta Rec NoInline False [] Nothing
         }

buildCall :: [Exp3] -> Exp3
buildCall = AppE "build" NotTailRec []

progWithMain :: Exp3 -> Prog3
progWithMain m =
  Prog { ddefs = M.empty
       , fundefs = M.fromList [(selfName, walkFun), ("build", buildFun)]
       , mainExp = Just (m, ProdTy [])
       }

-- | The corpus shape: a region start, a mutable cursor addressing it, a
-- producing call that advances that cursor past the value it wrote, and only
-- then the traversal -- with the same region start as its input.
case_end_advanced_by_an_earlier_call_is_a_value_end :: Assertion
case_end_advanced_by_an_earlier_call_is_a_value_end =
  assertBool "an end advanced past one value by an earlier call is accepted"
    (callerEndsAreValueEnds selfName (progWithMain body))
  where
    body =
      LetE ("r", [], CursorTy, Ext (NewBuffer L2.Infinite L2.RegionMutable))
        (LetE ("m", [], MutCursorTy, Ext (AddrOfCursor (VarE "r")))
          (LetE ("e2", [], MutCursorTy, Ext (AddrOfCursor (VarE "out_r")))
            (LetE ("produce", [], ProdTy [], buildCall [VarE "e2", VarE "m", mkLitE64 5])
              (LetE ("use", [], ProdTy [],
                     AppE selfName NotTailRec [] [VarE "m", VarE "e2", VarE "e2", VarE "r"])
                (MkProdE [])))))

-- | An enclosing REGION end reaches the call as `AddrOfCursor` of a formal no
-- call ever advanced.  The walk would then run past the value, through its
-- sibling and off the data.
case_end_from_an_unadvanced_cursor_is_refused :: Assertion
case_end_from_an_unadvanced_cursor_is_refused =
  assertBool "an end no call ever advanced is not a value end"
    (not (callerEndsAreValueEnds selfName (progWithMain body)))
  where
    body =
      LetE ("m", [], MutCursorTy, Ext (AddrOfCursor (VarE "region_end")))
        (LetE ("s", [], MutCursorTy, Ext (AddrOfCursor (VarE "subtree_start")))
          (LetE ("use", [], ProdTy [],
                 AppE selfName NotTailRec [] [VarE "m", VarE "m", VarE "m", VarE "s"])
            (MkProdE [])))

-- | The end must end the value the START argument points at, not some other
-- value that happens to have a known end.
case_end_of_a_different_value_is_refused :: Assertion
case_end_of_a_different_value_is_refused =
  assertBool "an end belonging to another value is refused"
    (not (callerEndsAreValueEnds selfName (progWithMain body)))
  where
    body =
      LetE ("r1", [], CursorTy, Ext (NewBuffer L2.Infinite L2.RegionMutable))
        (LetE ("r2", [], CursorTy, Ext (NewBuffer L2.Infinite L2.RegionMutable))
          (LetE ("m", [], MutCursorTy, Ext (AddrOfCursor (VarE "r1")))
            (LetE ("e2", [], MutCursorTy, Ext (AddrOfCursor (VarE "out_r")))
              (LetE ("produce", [], ProdTy [], buildCall [VarE "e2", VarE "m", mkLitE64 5])
                (LetE ("use", [], ProdTy [],
                       AppE selfName NotTailRec [] [VarE "m", VarE "e2", VarE "e2", VarE "r2"])
                  (MkProdE []))))))

-- | Advanced twice, the span would cover two values and the walk would run
-- through both, so the cursor is poisoned rather than trusted.
case_end_advanced_twice_is_refused :: Assertion
case_end_advanced_twice_is_refused =
  assertBool "a cursor advanced past two values is not a single value's end"
    (not (callerEndsAreValueEnds selfName (progWithMain body)))
  where
    body =
      LetE ("r", [], CursorTy, Ext (NewBuffer L2.Infinite L2.RegionMutable))
        (LetE ("m", [], MutCursorTy, Ext (AddrOfCursor (VarE "r")))
          (LetE ("e2", [], MutCursorTy, Ext (AddrOfCursor (VarE "out_r")))
            (LetE ("p1", [], ProdTy [], buildCall [VarE "e2", VarE "m", mkLitE64 5])
              (LetE ("p2", [], ProdTy [], buildCall [VarE "e2", VarE "m", mkLitE64 5])
                (LetE ("use", [], ProdTy [],
                       AppE selfName NotTailRec [] [VarE "m", VarE "e2", VarE "e2", VarE "r"])
                  (MkProdE []))))))

-- Every decline the report can print must have its own text: a copied line
-- would send a reader looking at the wrong condition.

case_flat_decline_reasons_are_distinct :: Assertion
case_flat_decline_reasons_are_distinct = do
  let ds = [ FlatNotCandidate, FlatMutFormalAddCursor, FlatParentChildDependency
           , FlatCallerEndNotValueEnd, FlatNotVoidReturn, FlatAbiNotMutCursors
           , FlatNotSingleLinearTyCon, FlatNoInputCursor, FlatNoInputEnd
           , FlatVariantArgs, FlatUnerasableCall, FlatObservableEffect
           , FlatNonTraversalInputUpdate ]
      rs = map flatDeclineReason ds
  assertBool "no decline reason may be empty" (all (not . null) rs)
  length ds @=? S.size (S.fromList rs)

loopifyFlatTraversalsTests :: TestTree
loopifyFlatTraversalsTests = $(testGroupGenerator)
