{-# LANGUAGE TemplateHaskell #-}

module VectorizeTraversals
  ( vectorizeTraversalsTests
  ) where

import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3
import Gibbon.Passes.VectorizeTraversals

-- | The pass's own hard error requires --auto-loopification or
-- --opt-loopification to also be present -- vectorization only ever rewrites
-- loops loopification already produced. These tests exercise
-- VectorizeTraversals in isolation against hand-built already-loopified
-- fixtures, so Opt_AutoLoopification is set here purely to satisfy that
-- precondition, exactly as a real compile invoking both passes together
-- always would.
-- Pinned to BASELINE SSE2.  Every lane count, group count and cursor-bump
-- size asserted below was derived for a 128-bit register, and they are the
-- detailed statement of the vectorizer's cursor arithmetic.  Since
-- --opt-vectorization now defaults to the widest SIMD the machine has, the
-- flag has to be set explicitly here or those assertions would silently be
-- testing a different width.  'runnerAvx2' covers the 256-bit width.
runner64 :: L3.Prog3 -> L3.Prog3
runner64 = runnerWith (gopt_set Opt_SimdBaselineSse2)

-- | The same pass at the 256-bit width.
runnerAvx2 :: L3.Prog3 -> L3.Prog3
runnerAvx2 = runnerWith id

runnerWith :: (DynFlags -> DynFlags) -> L3.Prog3 -> L3.Prog3
runnerWith f prg =
  fst $
    runPassM
      (defaultConfig {dynflags = f (gopt_set Opt_AutoLoopification
                                     (gopt_set Opt_EnableVectorization (dynflags defaultConfig)))})
      0
      (vectorizeTraversals prg)

-- | At AVX2 every lane count doubles and every cursor advances a 32-byte
-- register, from exactly the same source program.  This is the property that
-- makes the width a single decision rather than an assumption spread across
-- the pass and the backend.
case_w32_add_vectorizes_with_eight_lanes_at_avx2 :: Assertion
case_w32_add_vectorizes_with_eight_lanes_at_avx2 =
  let body = funBodyOf "w32Add" (runnerAvx2 w32Prog)
   in do
        countVecStoresOf (L3.IntS W32) 8 body @?= 1
        countVecLoadsOf (L3.IntS W32) 8 body @?= 1
        -- and never at the 128-bit count
        countVecStoresOf (L3.IntS W32) 4 body @?= 0
        countVecLoadsOf (L3.IntS W32) 4 body @?= 0
        countBumpsBy 32 body @?= 2

case_w32_multiply_vectorizes_at_avx2 :: Assertion
case_w32_multiply_vectorizes_at_avx2 =
  let body = funBodyOf "w32Mul" (runnerAvx2 w32Prog)
   in do
        countVecStoresOf (L3.IntS W32) 8 body @?= 1
        countBumpsBy 32 body @?= 2

case_int_add_vectorizes_64_bit :: Assertion
case_int_add_vectorizes_64_bit =
  let body = funBodyOf "intAdd64" (runner64 vectorizeProg)
   in do
        countVecAdds body @?= 2
        countVecStores body @?= 2

case_int_select_vectorizes :: Assertion
case_int_select_vectorizes =
  -- Stride 4 at 2 lanes per group (IntS W64 is unconditionally 8 bytes) is
  -- 2 groups, hence 2 stores -- matching intAdd64's shape below exactly.
  countVecStores (funBodyOf "intSelect" (runner64 vectorizeProg)) @?= 2

-- | GibInt/IntS W64 is unconditionally 8 bytes, so a 128-bit register holds
-- exactly 2 of them and each vector iteration advances 2 * 8 = 16 bytes.
case_int_select_lane_count_is_two_and_bump_is_sixteen_bytes :: Assertion
case_int_select_lane_count_is_two_and_bump_is_sixteen_bytes =
  let body = funBodyOf "intSelect" (runner64 vectorizeProg)
   in do
        countVecStoresOf L3.intS64 2 body @?= 2
        countVecLoadsOf L3.intS64 2 body @?= 2
        countVecStoresOf L3.intS64 4 body @?= 0
        countVecLoadsOf L3.intS64 4 body @?= 0
        -- two groups x (in, out) cursors, each advancing a full register
        countBumpsBy 16 body @?= 4

-- | The 64-bit mirror: 8-byte lanes, so 2 lanes fill the register and each
-- vector iteration still advances 16 bytes -- but via `int64x2`, not `int32x4`.
case_64_bit_lane_count_is_two_and_bump_is_sixteen_bytes :: Assertion
case_64_bit_lane_count_is_two_and_bump_is_sixteen_bytes =
  let body = funBodyOf "intAdd64" (runner64 vectorizeProg)
   in do
        countVecStoresOf L3.intS64 2 body @?= 2
        countVecLoadsOf L3.intS64 2 body @?= 2
        countVecStoresOf L3.intS64 4 body @?= 0
        -- two groups x (in, out) cursors, each advancing a full register
        countBumpsBy 16 body @?= 4

case_mixed_int_mask_float_select_stays_scalar :: Assertion
case_mixed_int_mask_float_select_stays_scalar =
  countVecStores (funBodyOf "mixedSelect" (runner64 vectorizeProg)) @?= 0

case_unsupported_write_keeps_whole_loop_scalar :: Assertion
case_unsupported_write_keeps_whole_loop_scalar =
  countVecStores (funBodyOf "partialUnsupported" (runner64 vectorizeProg)) @?= 0

-- Both arms of a `VecSelect` are evaluated, so a division the scalar program
-- guarded must not be speculated: leave the loop scalar.
case_guarded_division_stays_scalar :: Assertion
case_guarded_division_stays_scalar =
  countVecStores (funBodyOf "guardedDiv" (runner64 vectorizeProg)) @?= 0

-- A loop-invariant division must not be hoisted in front of the loop (it would
-- run even for a zero trip count); it stays inside the loop as a vector op.
-- | A call in the loop body keeps the loop scalar.
--
-- `safeEffect` used to accept every non-`Ext` right-hand side as effect-free,
-- so a call was carried into the vector body and would have run once per vector
-- iteration instead of once per element.
case_call_in_loop_body_keeps_the_loop_scalar :: Assertion
case_call_in_loop_body_keeps_the_loop_scalar =
  countVecStores (funBodyOf "callInLoop" (runner64 vectorizeProg)) @?= 0

-- | An arm writing two scalars keeps the loop scalar, rather than losing one.
--
-- The paired one-write program below vectorizes, so this is the multi-write
-- rejection and not the conditional shape being unsupported outright.
case_multi_write_arm_keeps_the_loop_scalar :: Assertion
case_multi_write_arm_keeps_the_loop_scalar =
  countVecStores (funBodyOf "twoWriteArm" (runner64 vectorizeProg)) @?= 0

case_single_write_arm_still_vectorizes :: Assertion
case_single_write_arm_still_vectorizes =
  assertBool "the one-write conditional must still vectorize"
    (countVecStores (funBodyOf "oneWriteArm" (runner64 vectorizeProg)) > 0)

-- | A cursor that is read by one op and skipped by another is advanced ONCE.
--
-- The read list and the skip list were deduplicated separately, so a cursor in
-- both emitted two bumps and advanced 32 bytes per 16-byte vector iteration.
case_shared_input_cursor_is_bumped_once :: Assertion
case_shared_input_cursor_is_bumped_once =
  let body = funBodyOf "sharedInputConst" (runner64 vectorizeProg)
      inBumps = countBumpsOfRef "sharedloop_buf2_in_loc" body
      outBumps = countBumpsOfRef "sharedloop_buf1_out_loc" body
   in do
        -- The loop vectorizes at all.
        assertBool "expected the loop to vectorize" (countVecStores body > 0)
        -- Every cursor advances the same distance per iteration; the shared
        -- input must not advance twice for appearing in two roles.
        assertBool
          ("buf2 input bumped " ++ show inBumps ++ " times, buf1 output "
             ++ show outBumps)
          (inBumps == outBumps)

-- | A constant write borrows an input cursor to advance, because the scalar
-- loop it replaces advanced one.  The borrow is the nearest preceding read of
-- the same scalar kind, which is only its own buffer's cursor because
-- loopification emits a read for every buffer.  Without that read the borrow
-- would cross buffers, and the loop must stay scalar rather than advance a
-- peer buffer's cursor.
case_cross_buffer_borrow_keeps_the_loop_scalar :: Assertion
case_cross_buffer_borrow_keeps_the_loop_scalar =
  countVecStores (funBodyOf "crossBufferBorrow" (runner64 vectorizeProg)) @?= 0

-- | A conversion from a width to itself computes nothing, so it must not stop
-- the loop it appears in from vectorizing.  A conversion that really changes
-- width still does: every operand of a DAG is loaded with the write's own lane
-- count, so a narrower one would be loaded wrong.
case_identity_width_conversion_still_vectorizes :: Assertion
case_identity_width_conversion_still_vectorizes = do
  countVecStores (funBodyOf "identityConv" (runner64 vectorizeProg)) @?= 2
  countVecStores (funBodyOf "wideningConv" (runner64 vectorizeProg)) @?= 0

case_invariant_division_is_not_hoisted :: Assertion
case_invariant_division_is_not_hoisted =
  let body = funBodyOf "invariantDiv" (runner64 vectorizeProg)
   in do
        countHoistedPartialPrims body @?= 0
        countVecStores body @?= 2

vectorizeProg :: L3.Prog3
vectorizeProg =
  L3.Prog
    M.empty
    (M.fromList
       [ ("intAdd64", intAdd64Fun)
       , ("intSelect", intSelectFun)
       , ("mixedSelect", mixedSelectFun)
       , ("partialUnsupported", partialUnsupportedFun)
       , ("guardedDiv", guardedDivFun)
       , ("invariantDiv", invariantDivFun)
       , ("callInLoop", callInLoopFun)
       , ("twoWriteArm", twoWriteArmFun)
       , ("oneWriteArm", oneWriteArmFun)
       , ("sharedInputConst", sharedInputConstFun)
       , ("crossBufferBorrow", crossBufferBorrowFun)
       , ("identityConv", identityConvFun)
       , ("wideningConv", wideningConvFun)
       ])
    Nothing

-- | A loop body containing a CALL, whose right-hand side is not an `Ext`.
--
-- Vectorizing it would run the call once per vector iteration instead of once
-- per element.  Nothing about a call is visible in the effect whitelist, which
-- only inspected `Ext` forms, so it has to be classified rather than assumed
-- effect-free.
callInLoopFun :: L3.FunDef3
callInLoopFun =
  L3.FunDef
    "callInLoop"
    []
    ([], L3.ProdTy [])
    (loopBody callInLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

callInLoopBody :: L3.Exp3
callInLoopBody =
  L3.mkLets
    [ ("in_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "call_in")
    , ("read_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur")
    , ("x", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_pair"))
    , ("side", [], L3.IntTy W64, L3.AppE "sideEffect" UnknownTailType [] [L3.VarE "x"])
    , ("out_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "call_out")
    , ("write", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur" (L3.VarE "x"))
    , ("bump_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "call_in" (L3.mkLitE64 8))
    , ("bump_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "call_out" (L3.mkLitE64 8))
    ]
    (L3.MkProdE [])

-- | A conditional whose THEN arm writes two scalars.
--
-- Flattening kept only the first write, so the second was silently dropped.
twoWriteArmFun :: L3.FunDef3
twoWriteArmFun =
  L3.FunDef
    "twoWriteArm"
    []
    ([], L3.ProdTy [])
    (loopBody (condWriteLoopBody True))
    (FunMeta TailRec NoInline False [Loopified] Nothing)

-- | The same shape with one write per arm: the false-positive guard.
oneWriteArmFun :: L3.FunDef3
oneWriteArmFun =
  L3.FunDef
    "oneWriteArm"
    []
    ([], L3.ProdTy [])
    (loopBody (condWriteLoopBody False))
    (FunMeta TailRec NoInline False [Loopified] Nothing)

condWriteLoopBody :: Bool -> L3.Exp3
condWriteLoopBody twoWrites =
  L3.mkLets
    [ ("in_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "cond_in")
    , ("read_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur")
    , ("x", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_pair"))
    , ("out_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "cond_out")
      -- Before the conditional: flattening treats the `IfE` as the body's
      -- tail, so anything after it would not be seen.
    , ("bump_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "cond_in" (L3.mkLitE64 8))
    , ("bump_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "cond_out" (L3.mkLitE64 8))
    ]
    (L3.IfE
       (L3.PrimAppE eqIntP64 [L3.VarE "x", L3.mkLitE64 0])
       (L3.mkLets
          ( [ ("w1", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur" (L3.mkLitE64 1)) ]
              ++ [ ("w2", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur" (L3.mkLitE64 2))
                 | twoWrites ] )
          (L3.MkProdE []))
       (L3.mkLets
          [ ("w3", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur" (L3.VarE "x")) ]
          (L3.MkProdE [])))

-- | Two writes from one input cursor, one of which ignores the value.
--
-- An op whose expression reads nothing is attributed to the nearest preceding
-- read's cursor, so that cursor is a READ cursor for the first write and a
-- SKIPPED one for the second.  Both lists emitted a bump, so the cursor
-- advanced twice per vector iteration and the loop walked past its own data.
sharedInputConstFun :: L3.FunDef3
sharedInputConstFun =
  L3.FunDef
    "sharedInputConst"
    []
    ([], L3.ProdTy [])
    (loopBody sharedInputConstBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

-- | Buffer 1 reads both buffers; buffer 2 writes a constant.
--
-- Buffer 2's cursor is therefore a READ cursor for buffer 1's op and the
-- borrowed input of buffer 2's own constant write, which is the shape that
-- advanced it twice per vector iteration.  Cursor names follow the loop buffer
-- name contract because the borrow is only accepted when it stays inside one
-- buffer, which is read off those names.
sharedInputConstBody :: L3.Exp3
sharedInputConstBody =
  L3.mkLets
    [ ("in_cur_a", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "sharedloop_buf1_in_loc")
    , ("read_pair_a", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur_a")
    , ("x", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_pair_a"))
    , ("in_cur_b", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "sharedloop_buf2_in_loc")
    , ("read_pair_b", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur_b")
    , ("y", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_pair_b"))
    , ("out_cur_a", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "sharedloop_buf1_out_loc")
    , ("write_a", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur_a" (L3.PrimAppE addP64 [L3.VarE "x", L3.VarE "y"]))
    , ("out_cur_b", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "sharedloop_buf2_out_loc")
    , ("write_b", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur_b" (L3.mkLitE64 7))
    , ("bump_in_a", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "sharedloop_buf1_in_loc" (L3.mkLitE64 8))
    , ("bump_in_b", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "sharedloop_buf2_in_loc" (L3.mkLitE64 8))
    , ("bump_out_a", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "sharedloop_buf1_out_loc" (L3.mkLitE64 8))
    , ("bump_out_b", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "sharedloop_buf2_out_loc" (L3.mkLitE64 8))
    ]
    (L3.MkProdE [])

-- | A write whose operand carries a conversion from W64 to W64.
identityConvFun :: L3.FunDef3
identityConvFun =
  L3.FunDef
    "identityConv"
    []
    ([], L3.ProdTy [])
    (loopBody identityConvLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

identityConvLoopBody :: L3.Exp3
identityConvLoopBody =
  intWriteLoopBody 8 "idconv_in" "idconv_out" $
    L3.PrimAppE addP64
      [ L3.VarE "x"
      , L3.PrimAppE (IntConvertP (IntPrimWidth W64) W64) [L3.mkLitE64 7] ]

-- | The same write with a conversion that really changes width.
wideningConvFun :: L3.FunDef3
wideningConvFun =
  L3.FunDef
    "wideningConv"
    []
    ([], L3.ProdTy [])
    (loopBody wideningConvLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

wideningConvLoopBody :: L3.Exp3
wideningConvLoopBody =
  intWriteLoopBody 8 "widening_in" "widening_out" $
    L3.PrimAppE addP64
      [ L3.VarE "x"
      , L3.PrimAppE (IntConvertP (IntPrimWidth W32) W64) [L3.LitE (LitWidth W32) 7] ]

-- | The same loop with buffer 2's own read removed, so the constant write's
-- borrowed input cursor would come from buffer 1.
crossBufferBorrowFun :: L3.FunDef3
crossBufferBorrowFun =
  L3.FunDef
    "crossBufferBorrow"
    []
    ([], L3.ProdTy [])
    (loopBody crossBufferBorrowBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

crossBufferBorrowBody :: L3.Exp3
crossBufferBorrowBody =
  L3.mkLets
    [ ("in_cur_a", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "crossloop_buf1_in_loc")
    , ("read_pair_a", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur_a")
    , ("x", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_pair_a"))
    , ("out_cur_a", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "crossloop_buf1_out_loc")
    , ("write_a", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur_a" (L3.PrimAppE addP64 [L3.VarE "x", L3.mkLitE64 1]))
    , ("out_cur_b", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "crossloop_buf2_out_loc")
    , ("write_b", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur_b" (L3.mkLitE64 7))
    , ("bump_in_a", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "crossloop_buf1_in_loc" (L3.mkLitE64 8))
    , ("bump_out_a", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "crossloop_buf1_out_loc" (L3.mkLitE64 8))
    , ("bump_out_b", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "crossloop_buf2_out_loc" (L3.mkLitE64 8))
    ]
    (L3.MkProdE [])

guardedDivFun :: L3.FunDef3
guardedDivFun =
  L3.FunDef
    "guardedDiv"
    []
    ([], L3.ProdTy [])
    (loopBody guardedDivLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

guardedDivLoopBody :: L3.Exp3
guardedDivLoopBody =
  intWriteLoopBody 8 "guard_in" "guard_out" $
    L3.IfE
      (L3.PrimAppE eqIntP64 [L3.VarE "x", L3.mkLitE64 0])
      (L3.mkLitE64 0)
      (L3.PrimAppE divP64 [L3.VarE "x", L3.VarE "k"])

invariantDivFun :: L3.FunDef3
invariantDivFun =
  L3.FunDef
    "invariantDiv"
    []
    ([], L3.ProdTy [])
    (loopBody invariantDivLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

invariantDivLoopBody :: L3.Exp3
invariantDivLoopBody =
  intWriteLoopBody 8 "inv_in" "inv_out" $
    L3.PrimAppE addP64 [L3.VarE "x", L3.PrimAppE divP64 [L3.VarE "k", L3.VarE "m"]]

intAdd64Fun :: L3.FunDef3
intAdd64Fun =
  L3.FunDef
    "intAdd64"
    []
    ([], L3.ProdTy [])
    (loopBody intAdd64LoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

intSelectFun :: L3.FunDef3
intSelectFun =
  L3.FunDef
    "intSelect"
    []
    ([], L3.ProdTy [])
    (loopBody intSelectLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

mixedSelectFun :: L3.FunDef3
mixedSelectFun =
  L3.FunDef
    "mixedSelect"
    []
    ([], L3.ProdTy [])
    (loopBody mixedSelectLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

partialUnsupportedFun :: L3.FunDef3
partialUnsupportedFun =
  L3.FunDef
    "partialUnsupported"
    []
    ([], L3.ProdTy [])
    (loopBody partialUnsupportedLoopBody)
    (FunMeta TailRec NoInline False [Loopified] Nothing)

loopBody :: L3.Exp3 -> L3.Exp3
loopBody body =
  L3.LetE
    ("loop", [], L3.ProdTy [], L3.Ext $ L3.ForE "i" (L3.mkLitE64 8) body)
    (L3.MkProdE [])

intAdd64LoopBody :: L3.Exp3
intAdd64LoopBody =
  intWriteLoopBody 8 "int64_in" "int64_out" (L3.PrimAppE addP64 [L3.VarE "x", L3.mkLitE64 1])

intSelectLoopBody :: L3.Exp3
intSelectLoopBody =
  -- The scalar per-element bump must match IntS W64's actual width (8 bytes,
  -- unconditionally) or the vectorizer correctly refuses to vectorize an
  -- inconsistent loop shape.
  intWriteLoopBody 8 "int_in" "int_out" intSelectExpr

intWriteLoopBody :: Int -> Var -> Var -> L3.Exp3 -> L3.Exp3
intWriteLoopBody = widthWriteLoopBody W64

-- | 'intWriteLoopBody' at an arbitrary integer width.  The per-element scalar
-- bump must equal the scalar's real byte width or the vectorizer correctly
-- refuses the inconsistent loop shape.
widthWriteLoopBody :: IntWidth -> Int -> Var -> Var -> L3.Exp3 -> L3.Exp3
widthWriteLoopBody w bumpBytes inRef outRef writeExpr =
  L3.mkLets
    [ ("in_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor inRef)
    , ("read_pair", [], L3.ProdTy [L3.IntTy w, L3.CursorTy], L3.Ext $ L3.ReadScalar (L3.IntS w) "in_cur")
    , ("x", [], L3.IntTy w, L3.ProjE 0 (L3.VarE "read_pair"))
    , ("out_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor outRef)
    , ("write", [], L3.CursorTy, L3.Ext $ L3.WriteScalar (L3.IntS w) "out_cur" writeExpr)
    , ("bump_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable inRef (L3.mkLitE64 bumpBytes))
    , ("bump_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable outRef (L3.mkLitE64 bumpBytes))
    ]
    (L3.MkProdE [])

--------------------------------------------------------------------------------
-- W32: four lanes per 128-bit register
--------------------------------------------------------------------------------

w32Fun :: Var -> L3.Exp3 -> L3.FunDef3
w32Fun nm body =
  L3.FunDef nm [] ([], L3.ProdTy []) (loopBody body)
            (FunMeta TailRec NoInline False [Loopified] Nothing)

-- out = x + invariant
w32AddLoopBody :: L3.Exp3
w32AddLoopBody =
  widthWriteLoopBody W32 4 "w32_in" "w32_out"
    (L3.PrimAppE (AddP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "k32"])

-- out = x - invariant
w32SubLoopBody :: L3.Exp3
w32SubLoopBody =
  widthWriteLoopBody W32 4 "w32s_in" "w32s_out"
    (L3.PrimAppE (SubP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "k32"])

-- out = if x == sentinel then a else b
w32SelectLoopBody :: L3.Exp3
w32SelectLoopBody =
  widthWriteLoopBody W32 4 "w32e_in" "w32e_out" $
    L3.IfE
      (L3.PrimAppE (EqIntP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "sent32"])
      (L3.VarE "a32")
      (L3.VarE "b32")

-- Unsupported at W32: no packed SSE2 multiply.  Must stay scalar.
w32MulLoopBody :: L3.Exp3
w32MulLoopBody =
  widthWriteLoopBody W32 4 "w32m_in" "w32m_out"
    (L3.PrimAppE (MulP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "k32"])

w32DivLoopBody :: L3.Exp3
w32DivLoopBody =
  widthWriteLoopBody W32 4 "w32d_in" "w32d_out"
    (L3.PrimAppE (DivP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "k32"])

w32ModLoopBody :: L3.Exp3
w32ModLoopBody =
  widthWriteLoopBody W32 4 "w32r_in" "w32r_out"
    (L3.PrimAppE (ModP (IntPrimWidth W32)) [L3.VarE "x", L3.VarE "k32"])

-- A fused loop writing BOTH a W32 and a W64 buffer.  Lane counts differ (4 vs
-- 2), so this must stay entirely scalar rather than risk inconsistent cursor
-- advancement.
mixedWidthLoopBody :: L3.Exp3
mixedWidthLoopBody =
  L3.mkLets
    [ ("in_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "mx_in32")
    , ("rp32", [], L3.ProdTy [L3.IntTy W32, L3.CursorTy], L3.Ext $ L3.ReadScalar (L3.IntS W32) "in_cur")
    , ("x32", [], L3.IntTy W32, L3.ProjE 0 (L3.VarE "rp32"))
    , ("out_cur32", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "mx_out32")
    , ("w32", [], L3.CursorTy, L3.Ext $ L3.WriteScalar (L3.IntS W32) "out_cur32"
        (L3.PrimAppE (AddP (IntPrimWidth W32)) [L3.VarE "x32", L3.VarE "k32"]))
    , ("in_cur64", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "mx_in64")
    , ("rp64", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_cur64")
    , ("x64", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "rp64"))
    , ("out_cur64", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "mx_out64")
    , ("w64", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_cur64"
        (L3.PrimAppE addP64 [L3.VarE "x64", L3.mkLitE64 1]))
    , ("b1", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "mx_in32" (L3.mkLitE64 4))
    , ("b2", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "mx_out32" (L3.mkLitE64 4))
    , ("b3", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "mx_in64" (L3.mkLitE64 8))
    , ("b4", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "mx_out64" (L3.mkLitE64 8))
    ]
    (L3.MkProdE [])

--------------------------------------------------------------------------------
-- W16 (8 lanes) and W8 (16 lanes), and mixed-width fused loops
--------------------------------------------------------------------------------

narrowBin :: IntWidth -> Prim L3.Ty3 -> Var -> Var -> L3.Exp3
narrowBin w prim inRef outRef =
  widthWriteLoopBody w (intWidthBytes w) inRef outRef
    (L3.PrimAppE prim [L3.VarE "x", L3.VarE "kN"])

narrowSelect :: IntWidth -> Var -> Var -> L3.Exp3
narrowSelect w inRef outRef =
  widthWriteLoopBody w (intWidthBytes w) inRef outRef $
    L3.IfE (L3.PrimAppE (EqIntP (IntPrimWidth w)) [L3.VarE "x", L3.VarE "sentN"])
           (L3.VarE "aN") (L3.VarE "bN")

-- | One `ForE` writing several independent scalar buffers of DIFFERENT widths,
-- exactly the shape loopified traversal fusion produces.
mixedWidthsLoopBody :: [IntWidth] -> L3.Exp3
mixedWidthsLoopBody ws =
  L3.mkLets (concatMap perWidth ws ++ concatMap bumps ws) (L3.MkProdE [])
  where
    tag w = toVar ("mx" ++ show (8 * intWidthBytes w))
    inR w = toVar (fromVar (tag w) ++ "_in")
    outR w = toVar (fromVar (tag w) ++ "_out")
    cur w = toVar (fromVar (tag w) ++ "_cur")
    ocur w = toVar (fromVar (tag w) ++ "_ocur")
    rp w = toVar (fromVar (tag w) ++ "_rp")
    xv w = toVar (fromVar (tag w) ++ "_x")
    wv w = toVar (fromVar (tag w) ++ "_w")
    perWidth w =
      [ (cur w, [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor (inR w))
      , (rp w, [], L3.ProdTy [L3.IntTy w, L3.CursorTy], L3.Ext $ L3.ReadScalar (L3.IntS w) (cur w))
      , (xv w, [], L3.IntTy w, L3.ProjE 0 (L3.VarE (rp w)))
      , (ocur w, [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor (outR w))
      , (wv w, [], L3.CursorTy, L3.Ext $ L3.WriteScalar (L3.IntS w) (ocur w)
          (L3.PrimAppE (AddP (IntPrimWidth w)) [L3.VarE (xv w), L3.VarE "kMixed"]))
      ]
    bumps w =
      [ (toVar (fromVar (tag w) ++ "_bi"), [], L3.ProdTy []
        , L3.Ext $ L3.BumpCursorMutable (inR w) (L3.mkLitE64 (intWidthBytes w)))
      , (toVar (fromVar (tag w) ++ "_bo"), [], L3.ProdTy []
        , L3.Ext $ L3.BumpCursorMutable (outR w) (L3.mkLitE64 (intWidthBytes w)))
      ]

narrowProg :: L3.Prog3
narrowProg =
  L3.Prog M.empty
    (M.fromList
       [ ("w16Add",  w32Fun "w16Add"  (narrowBin W16 (AddP (IntPrimWidth W16)) "w16a_in" "w16a_out"))
       , ("w16Sub",  w32Fun "w16Sub"  (narrowBin W16 (SubP (IntPrimWidth W16)) "w16s_in" "w16s_out"))
       , ("w16Mul",  w32Fun "w16Mul"  (narrowBin W16 (MulP (IntPrimWidth W16)) "w16m_in" "w16m_out"))
       , ("w16Div",  w32Fun "w16Div"  (narrowBin W16 (DivP (IntPrimWidth W16)) "w16d_in" "w16d_out"))
       , ("w16Mod",  w32Fun "w16Mod"  (narrowBin W16 (ModP (IntPrimWidth W16)) "w16r_in" "w16r_out"))
       , ("w16Sel",  w32Fun "w16Sel"  (narrowSelect W16 "w16e_in" "w16e_out"))
       , ("w8Add",   w32Fun "w8Add"   (narrowBin W8 (AddP (IntPrimWidth W8)) "w8a_in" "w8a_out"))
       , ("w8Sub",   w32Fun "w8Sub"   (narrowBin W8 (SubP (IntPrimWidth W8)) "w8s_in" "w8s_out"))
       , ("w8Mul",   w32Fun "w8Mul"   (narrowBin W8 (MulP (IntPrimWidth W8)) "w8m_in" "w8m_out"))
       , ("w8Sel",   w32Fun "w8Sel"   (narrowSelect W8 "w8e_in" "w8e_out"))
       , ("mix1632", w32Fun "mix1632" (mixedWidthsLoopBody [W16, W32]))
       , ("mix832",  w32Fun "mix832"  (mixedWidthsLoopBody [W8, W32]))
       , ("mixAll",  w32Fun "mixAll"  (mixedWidthsLoopBody [W8, W16, W32, W64]))
       ])
    Nothing

-- W16: 2 bytes, so 8 lanes fill the register, stride 8, ONE group.
case_w16_add_vectorizes_with_eight_lanes :: Assertion
case_w16_add_vectorizes_with_eight_lanes =
  let body = funBodyOf "w16Add" (runner64 narrowProg)
   in do countVecStoresOf (L3.IntS W16) 8 body @?= 1
         countVecLoadsOf (L3.IntS W16) 8 body @?= 1
         countVecStoresOf (L3.IntS W16) 4 body @?= 0
         countBumpsBy 16 body @?= 2

case_w16_sub_and_select_vectorize :: Assertion
case_w16_sub_and_select_vectorize = do
  countVecStoresOf (L3.IntS W16) 8 (funBodyOf "w16Sub" (runner64 narrowProg)) @?= 1
  countVecStoresOf (L3.IntS W16) 8 (funBodyOf "w16Sel" (runner64 narrowProg)) @?= 1

-- _mm_mullo_epi16 is baseline SSE2, so unlike W32 this DOES vectorize.
case_w16_multiply_vectorizes :: Assertion
case_w16_multiply_vectorizes =
  countVecStoresOf (L3.IntS W16) 8 (funBodyOf "w16Mul" (runner64 narrowProg)) @?= 1

case_w16_divide_and_modulus_stay_scalar :: Assertion
case_w16_divide_and_modulus_stay_scalar = do
  countVecStores (funBodyOf "w16Div" (runner64 narrowProg)) @?= 0
  countVecStores (funBodyOf "w16Mod" (runner64 narrowProg)) @?= 0

-- W8: 1 byte, so 16 lanes fill the register, stride 16, ONE group.
case_w8_add_vectorizes_with_sixteen_lanes :: Assertion
case_w8_add_vectorizes_with_sixteen_lanes =
  let body = funBodyOf "w8Add" (runner64 narrowProg)
   in do countVecStoresOf (L3.IntS W8) 16 body @?= 1
         countVecLoadsOf (L3.IntS W8) 16 body @?= 1
         countVecStoresOf (L3.IntS W8) 8 body @?= 0
         countBumpsBy 16 body @?= 2

case_w8_sub_and_select_vectorize :: Assertion
case_w8_sub_and_select_vectorize = do
  countVecStoresOf (L3.IntS W8) 16 (funBodyOf "w8Sub" (runner64 narrowProg)) @?= 1
  countVecStoresOf (L3.IntS W8) 16 (funBodyOf "w8Sel" (runner64 narrowProg)) @?= 1

-- SSE2 has no 8-bit multiply INSTRUCTION, but unpacking to 16-bit lanes,
-- multiplying with _mm_mullo_epi16, masking to the low 8 bits and repacking
-- computes all sixteen lanes in registers -- and measured ~4.4x faster than
-- the scalar loop, so it is enabled.
case_w8_multiply_vectorizes :: Assertion
case_w8_multiply_vectorizes =
  countVecStoresOf (L3.IntS W8) 16 (funBodyOf "w8Mul" (runner64 narrowProg)) @?= 1

--------------------------------------------------------------------------------
-- Mixed-width fused loops now vectorize under one common logical stride
--------------------------------------------------------------------------------

-- W16+W32: stride 8, so W16 gets 1 group (8 lanes) and W32 gets 2 (4 lanes).
case_mixed_w16_w32_vectorizes :: Assertion
case_mixed_w16_w32_vectorizes =
  let body = funBodyOf "mix1632" (runner64 narrowProg)
   in do countVecStoresOf (L3.IntS W16) 8 body @?= 1
         countVecLoadsOf (L3.IntS W16) 8 body @?= 1
         countVecStoresOf (L3.IntS W32) 4 body @?= 2
         countVecLoadsOf (L3.IntS W32) 4 body @?= 2
         -- 2 cursors per field x groups: W16 1+1, W32 2+2
         countBumpsBy 16 body @?= 6

-- W8+W32: stride 16, so W8 gets 1 group and W32 gets 4.
case_mixed_w8_w32_vectorizes :: Assertion
case_mixed_w8_w32_vectorizes =
  let body = funBodyOf "mix832" (runner64 narrowProg)
   in do countVecStoresOf (L3.IntS W8) 16 body @?= 1
         countVecStoresOf (L3.IntS W32) 4 body @?= 4
         countBumpsBy 16 body @?= 10

-- All four widths: stride 16 -> 1 / 2 / 4 / 8 groups.  Every field covers the
-- same sixteen records, and every 16-byte bump is one full register.
case_mixed_all_four_widths_vectorizes :: Assertion
case_mixed_all_four_widths_vectorizes =
  let body = funBodyOf "mixAll" (runner64 narrowProg)
   in do countVecStoresOf (L3.IntS W8) 16 body @?= 1
         countVecStoresOf (L3.IntS W16) 8 body @?= 2
         countVecStoresOf (L3.IntS W32) 4 body @?= 4
         countVecStoresOf (L3.IntS W64) 2 body @?= 8
         countVecLoadsOf (L3.IntS W8) 16 body @?= 1
         countVecLoadsOf (L3.IntS W16) 8 body @?= 2
         countVecLoadsOf (L3.IntS W32) 4 body @?= 4
         countVecLoadsOf (L3.IntS W64) 2 body @?= 8
         -- (1+2+4+8) groups x (in,out) = 30 full-register bumps
         countBumpsBy 16 body @?= 30

w32Prog :: L3.Prog3
w32Prog =
  L3.Prog M.empty
    (M.fromList
       [ ("w32Add", w32Fun "w32Add" w32AddLoopBody)
       , ("w32Sub", w32Fun "w32Sub" w32SubLoopBody)
       , ("w32Select", w32Fun "w32Select" w32SelectLoopBody)
       , ("w32Mul", w32Fun "w32Mul" w32MulLoopBody)
       , ("w32Div", w32Fun "w32Div" w32DivLoopBody)
       , ("w32Mod", w32Fun "w32Mod" w32ModLoopBody)
       , ("mixedWidth", w32Fun "mixedWidth" mixedWidthLoopBody)
       ])
    Nothing

-- | W32 is 4 bytes, so a 128-bit register holds FOUR of them: stride 4 at 4
-- lanes is ONE group, so one load, one store, and a 16-byte bump per cursor.
-- Compare the W64 case above: 2 groups of 2 lanes for the same 4 elements.
case_w32_add_vectorizes_with_four_lanes :: Assertion
case_w32_add_vectorizes_with_four_lanes =
  let body = funBodyOf "w32Add" (runner64 w32Prog)
   in do
        countVecStoresOf (L3.IntS W32) 4 body @?= 1
        countVecLoadsOf (L3.IntS W32) 4 body @?= 1
        -- never at a lane count that does not tile the register
        countVecStoresOf (L3.IntS W32) 2 body @?= 0
        countVecLoadsOf (L3.IntS W32) 2 body @?= 0
        -- one group x (in, out), each advancing a full 16-byte register
        countBumpsBy 16 body @?= 2

case_w32_sub_vectorizes_with_four_lanes :: Assertion
case_w32_sub_vectorizes_with_four_lanes =
  let body = funBodyOf "w32Sub" (runner64 w32Prog)
   in do
        countVecStoresOf (L3.IntS W32) 4 body @?= 1
        countBumpsBy 16 body @?= 2

case_w32_equality_select_vectorizes :: Assertion
case_w32_equality_select_vectorizes =
  let body = funBodyOf "w32Select" (runner64 w32Prog)
   in do
        countVecStoresOf (L3.IntS W32) 4 body @?= 1
        countBumpsBy 16 body @?= 2

-- | _mm_mullo_epi32 is SSE4.1, but two _mm_mul_epu32 plus shuffles compute the
-- low 32 bits of all four products in registers at baseline SSE2, and measured
-- faster than the scalar loop -- so W32 multiply is enabled via that emulation.
case_w32_multiply_vectorizes :: Assertion
case_w32_multiply_vectorizes =
  countVecStoresOf (L3.IntS W32) 4 (funBodyOf "w32Mul" (runner64 w32Prog)) @?= 1

case_w32_divide_stays_scalar :: Assertion
case_w32_divide_stays_scalar =
  countVecStores (funBodyOf "w32Div" (runner64 w32Prog)) @?= 0

case_w32_modulus_stays_scalar :: Assertion
case_w32_modulus_stays_scalar =
  countVecStores (funBodyOf "w32Mod" (runner64 w32Prog)) @?= 0

-- | A fused loop mixing 4-lane W32 and 2-lane W64 writes VECTORIZES under
-- the common logical stride; it previously stayed scalar under
-- a blanket lane-uniformity rejection.  Stride is max 4 (max 4 2) = 4, so W32
-- takes one 4-lane group and W64 two 2-lane groups -- both covering the same
-- four records, each cursor advancing stride * scalarBytes.
case_mixed_w32_w64_fused_loop_vectorizes :: Assertion
case_mixed_w32_w64_fused_loop_vectorizes =
  let body = funBodyOf "mixedWidth" (runner64 w32Prog)
   in do countVecStoresOf (L3.IntS W32) 4 body @?= 1
         countVecStoresOf (L3.IntS W64) 2 body @?= 2
         countVecLoadsOf (L3.IntS W32) 4 body @?= 1
         countVecLoadsOf (L3.IntS W64) 2 body @?= 2
         -- (1+2) groups x (in,out) = 6 full-register bumps
         countBumpsBy 16 body @?= 6

intSelectExpr :: L3.Exp3
intSelectExpr =
  L3.IfE
    (L3.PrimAppE eqIntP64 [L3.VarE "x", L3.mkLitE64 0])
    (L3.PrimAppE addP64 [L3.VarE "x", L3.mkLitE64 1])
    (L3.VarE "x")

mixedSelectLoopBody :: L3.Exp3
mixedSelectLoopBody =
  L3.mkLets
    [ ("int_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "int_in")
    , ("int_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "int_cur")
    , ("x", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "int_pair"))
    , ("float_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "float_in")
    , ("float_pair", [], L3.ProdTy [L3.FloatTy, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.FloatS "float_cur")
    , ("f", [], L3.FloatTy, L3.ProjE 0 (L3.VarE "float_pair"))
    , ("out_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "float_out")
    , ("write", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.FloatS "out_cur" mixedSelectExpr)
    , ("bump_int", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "int_in" (L3.mkLitE64 4))
    , ("bump_float", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "float_in" (L3.mkLitE64 4))
    , ("bump_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "float_out" (L3.mkLitE64 4))
    ]
    (L3.MkProdE [])

mixedSelectExpr :: L3.Exp3
mixedSelectExpr =
  L3.IfE
    (L3.PrimAppE eqIntP64 [L3.VarE "x", L3.mkLitE64 0])
    (L3.PrimAppE FAddP [L3.VarE "f", L3.FloatE 1.0])
    (L3.VarE "f")

partialUnsupportedLoopBody :: L3.Exp3
partialUnsupportedLoopBody =
  L3.mkLets
    [ ("good", [], L3.ProdTy [], intWriteLoopBody 4 "partial_int_in" "partial_int_out" (L3.PrimAppE addP64 [L3.VarE "x", L3.mkLitE64 1]))
    , ("float_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "partial_float_in")
    , ("float_pair", [], L3.ProdTy [L3.FloatTy, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.FloatS "float_cur")
    , ("f", [], L3.FloatTy, L3.ProjE 0 (L3.VarE "float_pair"))
    , ("float_out_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "partial_float_out")
    , ("bad_write", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.FloatS "float_out_cur" (L3.PrimAppE EqFloatP [L3.VarE "f", L3.FloatE 0.0]))
    , ("bump_float_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "partial_float_in" (L3.mkLitE64 4))
    , ("bump_float_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "partial_float_out" (L3.mkLitE64 4))
    ]
    (L3.MkProdE [])

funBodyOf :: Var -> L3.Prog3 -> L3.Exp3
funBodyOf fn prg =
  case M.lookup fn (fundefs prg) of
    Just fd -> funBody fd
    Nothing -> error $ "Missing function in test program: " ++ sdoc fn

countVecStores :: L3.Exp3 -> Int
countVecStores = countExt p
  where
    p L3.VecStore{} = True
    p _ = False

countVecAdds :: L3.Exp3 -> Int
countVecAdds = countExt p
  where
    p L3.VecAdd{} = True
    p _ = False

-- | Vector stores for one exact @(scalar, lanes)@ shape.  'countVecStores'
-- only counts groups, so it cannot tell a correct 4-lane int32 store from an
-- int64x2 store that would spill 16 bytes into an 8-byte pair of GibInts.
countVecStoresOf :: L3.Scalar -> Int -> L3.Exp3 -> Int
countVecStoresOf scalar lanes = countExt p
  where
    p (L3.VecStore s l _ _) = s == scalar && l == lanes
    p _ = False

countVecLoadsOf :: L3.Scalar -> Int -> L3.Exp3 -> Int
countVecLoadsOf scalar lanes = countExt p
  where
    p (L3.VecLoad s l _) = s == scalar && l == lanes
    p _ = False

-- | Constant cursor bumps of exactly @n@ bytes.  The vectorized loop has to
-- advance one full 128-bit register per group, i.e. lanes * scalar width.
-- | Vector-register bumps of one cursor.
countBumpsOfRef :: Var -> L3.Exp3 -> Int
countBumpsOfRef ref = countExt p
  where
    p (L3.BumpCursorMutable r (L3.LitE _ m)) = r == ref && m == 16
    p _ = False

countBumpsBy :: Int -> L3.Exp3 -> Int
countBumpsBy n = countExt p
  where
    p (L3.BumpCursorMutable _ (L3.LitE _ m)) = m == fromIntegral n
    p _ = False

-- | Count partial (potentially trapping) primitives evaluated outside every
-- loop body, i.e. the positions a loop with a zero trip count would still run.
countHoistedPartialPrims :: L3.Exp3 -> Int
countHoistedPartialPrims ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> countHoistedPartialPrims rhs + countHoistedPartialPrims bod
    L3.Ext (L3.ForE _ bound _) -> countHoistedPartialPrims bound
    L3.Ext (L3.WhileCursor _ bod) -> countHoistedPartialPrims bod
    -- The pass's own `bound / stride` and `bound % stride` binds divide by a
    -- non-zero literal and can never trap; they are not what this counts.
    L3.PrimAppE p args
      | isPartialPrimT p && not (dividesByNonZeroLit args) ->
          1 + sum (map countHoistedPartialPrims args)
      | otherwise -> sum (map countHoistedPartialPrims args)
    L3.IfE a b c -> sum (map countHoistedPartialPrims [a, b, c])
    L3.MkProdE ls -> sum (map countHoistedPartialPrims ls)
    L3.ProjE _ e -> countHoistedPartialPrims e
    _ -> 0

dividesByNonZeroLit :: [L3.Exp3] -> Bool
dividesByNonZeroLit [_, L3.LitE _ n] = n /= 0
dividesByNonZeroLit _ = False

countExt :: (L3.E3Ext () L3.Ty3 -> Bool) -> L3.Exp3 -> Int
countExt p ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> countExt p rhs + countExt p bod
    L3.IfE a b c -> sum (map (countExt p) [a, b, c])
    L3.CaseE scrt brs -> countExt p scrt + sum [countExt p rhs | (_, _, rhs) <- brs]
    L3.AppE _ _ _ args -> sum (map (countExt p) args)
    L3.PrimAppE _ args -> sum (map (countExt p) args)
    L3.MkProdE ls -> sum (map (countExt p) ls)
    L3.ProjE _ e -> countExt p e
    L3.DataConE _ _ args -> sum (map (countExt p) args)
    L3.TimeIt e _ _ -> countExt p e
    L3.WithArenaE _ e -> countExt p e
    L3.SpawnE _ _ args -> sum (map (countExt p) args)
    L3.MapE (_, _, e1) e2 -> countExt p e1 + countExt p e2
    L3.FoldE (_, _, e1) (_, _, e2) e3 -> sum (map (countExt p) [e1, e2, e3])
    L3.Ext ext
      | p ext -> 1 + goExt ext
      | otherwise -> goExt ext
    _ -> 0
  where
    goExt ext =
      case ext of
        L3.ForE _ bound bod -> countExt p bound + countExt p bod
        L3.WhileCursor _ bod -> countExt p bod
        L3.WhileCursorEnd _ _ bod -> countExt p bod
        L3.WriteScalar _ _ rhs -> countExt p rhs
        L3.WriteTagPacked _ rhs -> countExt p rhs
        L3.WriteTaggedCursor _ rhs -> countExt p rhs
        L3.WriteCursorMutable _ rhs -> countExt p rhs
        L3.WriteList _ rhs _ -> countExt p rhs
        L3.WriteVector _ rhs _ -> countExt p rhs
        L3.AddCursor _ rhs -> countExt p rhs
        L3.BumpCursorMutable _ rhs -> countExt p rhs
        L3.AddrOfCursor rhs -> countExt p rhs
        L3.LetAvail _ bod -> countExt p bod
        L3.Assert rhs -> countExt p rhs
        L3.WriteCursorSelectiveIndirection _ _ _ mask -> countExt p mask
        L3.VecBroadcast _ _ rhs -> countExt p rhs
        L3.VecAdd _ _ a b -> countExt p a + countExt p b
        L3.VecSub _ _ a b -> countExt p a + countExt p b
        L3.VecMul _ _ a b -> countExt p a + countExt p b
        L3.VecDiv _ _ a b -> countExt p a + countExt p b
        L3.VecMod _ _ a b -> countExt p a + countExt p b
        L3.VecCmp _ _ _ a b -> countExt p a + countExt p b
        L3.VecSelect _ _ m a b -> sum (map (countExt p) [m, a, b])
        L3.VecStore _ _ _ rhs -> countExt p rhs
        _ -> 0

vectorizeTraversalsTests :: TestTree
vectorizeTraversalsTests = testGroup "VectorizeTraversals" [tests]

tests :: TestTree
tests = $(testGroupGenerator)

-- | Structural test for the partial (division-like) primitives.  Integer
-- primitives carry a width annotation, so `elem` over bare constructors would
-- only ever match one width.
isPartialPrimT :: Prim ty -> Bool
isPartialPrimT p = case p of { DivP{} -> True ; ModP{} -> True ; FDivP -> True ; _ -> False }
