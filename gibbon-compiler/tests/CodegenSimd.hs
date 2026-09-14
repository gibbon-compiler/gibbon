{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Backend-level tests for the SSE2 SIMD lowering in "Gibbon.Passes.Codegen".
--
-- These drive `codegenProg` end-to-end on tiny hand-built L4 programs, so they
-- observe the C text and the lowering errors a real compile would see.
module CodegenSimd
  ( codegenSimdTests
  ) where

import Control.Exception (ErrorCall, evaluate, try)
import qualified Data.List as L
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language (FunMeta(..), FunRec(..), FunInline(..))
import qualified Gibbon.L3.Syntax as L3
import Gibbon.L4.Syntax
import Gibbon.Passes.Codegen (codegenProg, vecHelperName)

--------------------------------------------------------------------------------
-- Harness

config64 :: Config
config64 = defaultConfig

-- | The same, with the 256-bit instruction set selected.
--
-- The register-width check is asked of the ISA this compilation selected, so
-- a lane count is valid or not only relative to one of these.
configAvx2 :: Config
configAvx2 =
  defaultConfig
    { dynflags = gopt_set Opt_SimdIsaAvx2 (dynflags defaultConfig) }

-- | The 128-bit tier that has SSE4.1.
configSse41 :: Config
configSse41 =
  defaultConfig
    { dynflags = gopt_set Opt_SimdIsaSse41 (dynflags defaultConfig) }

-- | An otherwise empty L4 program whose single function body is @tal@.
progWith :: Tail -> Prog
progWith tal =
  Prog
    { infoTable = M.empty
    , symbolTable = M.empty
    , fundefs =
        [ FunDecl
            { funName = "simd_probe"
            , funArgs = []
            , funRetTy = ProdTy []
            , funBody = tal
            , isPure = False
            , funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , mainExp = Nothing
    }

emptyProg :: Prog
emptyProg = (progWith (RetValsT [])) {fundefs = []}

-- | Fully force the generated C so lowering errors surface here.
genC :: Config -> Prog -> IO (Either ErrorCall String)
genC cfg prg = do
  r <- try (codegenProg cfg prg >>= \s -> evaluate (length s) >> pure s)
  pure r

genC' :: Config -> Prog -> IO String
genC' cfg prg = do
  r <- genC cfg prg
  case r of
    Right s -> pure s
    Left e -> assertFailure ("codegenProg unexpectedly failed: " ++ show e)

-- | A one-op body: a binary vector op over two broadcast registers.
binBody :: (L3.Scalar -> Int -> Prim) -> L3.Scalar -> Int -> Tail
binBody mkOp scalar lanes =
  let vty = SimdTy (scalarToTy scalar) lanes
  in LetPrimCallT [("simd_a", vty)] (VecBroadcast scalar lanes) [intTrivW64 1] $
     LetPrimCallT [("simd_b", vty)] (VecBroadcast scalar lanes) [intTrivW64 2] $
     LetPrimCallT [("simd_r", vty)] (mkOp scalar lanes) [VarTriv "simd_a", VarTriv "simd_b"] $
     RetValsT []

-- | A one-op body: broadcast a literal into a @(scalar, lanes)@ register.
broadcastBody :: L3.Scalar -> Int -> Tail
broadcastBody scalar lanes =
  LetPrimCallT
    [("simd_v", SimdTy (scalarToTy scalar) lanes)]
    (VecBroadcast scalar lanes)
    [intTrivW64 1]
    (RetValsT [])

--------------------------------------------------------------------------------
-- F1: the int64x2 scalar-spill helpers must declare 64-bit spill arrays.
--
-- `_mm_storeu_si128` writes 16 bytes into `av` / `bv`; spelling them `GibInt`
-- would be wrong if `GibInt` were ever anything but 8 bytes.  The helper block
-- is emitted unconditionally into every generated .c, so pin the type.

-- `gib_vec_mul_int64x2` is deliberately NOT in this list any more: it computes
-- both lanes in registers via three 32x32->64 multiplies and has no spill array
-- at all.  'case_int64x2_multiply_stays_in_registers' pins that instead -- the
-- stronger property, and the one that made W64 multiply loops stop being
-- slower than the scalar loops they replaced.
spillHelpers :: [String]
spillHelpers =
  ["gib_vec_div_int64x2", "gib_vec_mod_int64x2", "gib_vec_eq_int64x2"]

-- | Body of the named `static inline` helper in the generated C.
helperBody :: String -> String -> String
helperBody = helperBodyN 8

-- | The first @n@ lines from the named `static inline` helper onwards.
-- | The full body of the named `static inline` helper: from its definition
-- line up to the closing brace in column 0.  Unlike 'helperBodyN' this cannot
-- run off the end of one helper and into the next, which matters when the
-- helper carries a long explanatory comment.
helperBodyWhole :: String -> String -> String
helperBodyWhole nam src =
  case L.findIndex isDef ls of
    Nothing -> error $ "helper not found in generated C: " ++ nam
    Just i -> unlines (takeWhileInclusive (/= "}") (drop i ls))
  where
    ls = lines src
    isDef l = nam `L.isInfixOf` l && "static inline" `L.isInfixOf` l
    takeWhileInclusive _ [] = []
    takeWhileInclusive p (x:xs)
      | p x = x : takeWhileInclusive p xs
      | otherwise = [x]

helperBodyN :: Int -> String -> String -> String
helperBodyN n nam src =
  -- Match the DEFINITION, not a mention: these helpers are named in the
  -- explanatory comments above them, and a comment match would silently
  -- return the wrong lines.
  case L.findIndex (\l -> nam `L.isInfixOf` l && "static inline" `L.isInfixOf` l) ls of
    Nothing -> error $ "helper not found in generated C: " ++ nam
    Just i -> unlines (take n (drop i ls))
  where
    ls = lines src

case_int64x2_spill_arrays_are_64_bit_at_64_bit :: Assertion
case_int64x2_spill_arrays_are_64_bit_at_64_bit = do
  src <- genC' config64 emptyProg
  mapM_
    (\h -> do
       let b = helperBody h src
       assertBool (h ++ ": spill arrays must be int64_t, got:\n" ++ b)
         ("int64_t av[2], bv[2];" `L.isInfixOf` b)
       assertBool (h ++ ": spill arrays must not be GibInt, got:\n" ++ b)
         (not ("GibInt av[2]" `L.isInfixOf` b)))
    spillHelpers

-- The packed 64-bit multiply must stay in registers.
--
-- It used to store both operands to `int64_t av[2], bv[2]`, multiply lane by
-- lane and reassemble, paying a store-forwarding stall per multiply -- which
-- made a multiply-heavy W64 vectorized loop several times SLOWER than the
-- scalar loop it replaced.  A regression back to that shape would be silent
-- (the answers stay correct), so assert the absence of the spill array.
case_int64x2_multiply_stays_in_registers :: Assertion
case_int64x2_multiply_stays_in_registers = do
  src <- genC' config64 emptyProg
  let b = helperBodyWhole "gib_vec_mul_int64x2" src
  assertBool ("gib_vec_mul_int64x2 must not spill to a scalar array, got:\n" ++ b)
    (not ("int64_t av[2], bv[2];" `L.isInfixOf` b))
  assertBool ("gib_vec_mul_int64x2 must use packed 32x32->64 multiplies, got:\n" ++ b)
    ("_mm_mul_epu32" `L.isInfixOf` b)

--------------------------------------------------------------------------------
-- F2: `ITERS:` / `SIZE:` are printed from GibInt-typed RTS getters.

timedProg :: Prog
timedProg =
  progWith
    (LetTimedT
       True
       []
       (RetValsT [])
       (RetValsT []))

-- | Just the ITERS:/SIZE: printf lines, so a failure report is readable.
paramPrints :: String -> String
paramPrints src =
  unlines (filter (\l -> "ITERS: " `L.isInfixOf` l || "SIZE: " `L.isInfixOf` l) (lines src))

case_iters_and_size_use_percent_ld_at_64_bit :: Assertion
case_iters_and_size_use_percent_ld_at_64_bit = do
  src <- genC' config64 timedProg
  let got = paramPrints src
  assertBool ("ITERS: must still print with %ld at 64-bit, got:\n" ++ got)
    ("printf(\"ITERS: %ld\\n\"" `L.isInfixOf` src)
  assertBool ("SIZE: must still print with %ld at 64-bit, got:\n" ++ got)
    ("printf(\"SIZE: %ld\\n\"" `L.isInfixOf` src)

--------------------------------------------------------------------------------
-- F3: lowering must reject a SIMD op whose lanes do not tile a 128-bit
-- register at the active integer width.

-- | The mirror image: 4 lanes of 8-byte `GibInt` is a 256-bit vector, which
-- this SSE2 backend cannot express either.
-- @(intS64, 4)@ is the AVX2 tiling of a 64-bit scalar and is now accepted;
-- what must still be refused is a count that fills NEITHER register.  The
-- hazard this guards against is unchanged: a lane count that does not tile
-- the register emits a short or overlong memory access, silently.
case_lane_count_filling_no_register_is_rejected :: Assertion
case_lane_count_filling_no_register_is_rejected = do
  r <- genC config64 (progWith (broadcastBody L3.intS64 3))
  case r of
    Left e ->
      assertBool ("error must explain the register invariant, got: " ++ show e)
        ("does not fill a 128-bit register" `L.isInfixOf` show e)
    Right _ -> assertFailure "codegen accepted (intS64,3)"

-- | And every combination the vectorizer can actually produce must still lower.
-- This is the false-positive guard for the assertion above.
case_all_currently_valid_lane_counts_still_lower :: Assertion
case_all_currently_valid_lane_counts_still_lower = do
  mapM_
    (\(cfg, cfgName, scalar, lanes) -> do
       r <- genC cfg (progWith (broadcastBody scalar lanes))
       case r of
         Right _ -> pure ()
         Left e ->
           assertFailure $
             "valid combination rejected: " ++ cfgName ++ " " ++ show (scalar, lanes) ++ ": " ++ show e)
    [ (config64, "64-bit", L3.intS64, 2)
    , (config64, "64-bit", L3.SymS, 2)
    , (config64, "64-bit", L3.FloatS, 4)
    , (config64, "64-bit", L3.CharS, 16)
    , (config64, "64-bit", L3.BoolS, 16)
    ]

--------------------------------------------------------------------------------
-- The W32 capability matrix, and vectorizer/backend agreement
--------------------------------------------------------------------------------

-- | The helper name the backend would emit, or an error call if it refuses.
vecHelperNameOrError :: L3.VecOp -> L3.Scalar -> String
vecHelperNameOrError op s =
  fromVar (vecHelperName op s (L3.simdLanes L3.simdRegisterBytes s))

-- | The baseline 128-bit register width.
--
-- Most assertions below pin the SSE2 semantics explicitly, which are still
-- reachable via --simd-baseline-sse2.  The AVX2 width is covered by
-- 'case_lane_counts_are_derived_from_scalar_width',
-- 'case_w32_scalar_is_four_bytes_and_vector_is_sixteen' and
-- 'case_only_register_filling_lane_counts_are_valid', each of which checks
-- both widths.
sseBytes :: Int
sseBytes = L3.simdRegisterBytes

allScalars :: [L3.Scalar]
allScalars = [ L3.IntS L3.W8, L3.IntS L3.W16, L3.IntS L3.W32, L3.IntS L3.W64
             , L3.SymS, L3.FloatS, L3.CharS, L3.BoolS ]

allVecOps :: [L3.VecOp]
allVecOps = [minBound .. maxBound]

-- | Lane counts are a property of the scalar's real byte width AND the
-- register width the compilation targets.  Both widths are checked: an AVX2
-- build must double every count, and a baseline build must not change.
case_lane_counts_are_derived_from_scalar_width :: Assertion
case_lane_counts_are_derived_from_scalar_width = do
  let sse = L3.simdLanes L3.simdRegisterBytes
      avx = L3.simdLanes L3.simdRegisterBytesAvx2
  assertEqual "L3.W64" 2 (sse (L3.IntS L3.W64))
  assertEqual "L3.W32" 4 (sse (L3.IntS L3.W32))
  assertEqual "L3.W16" 8 (sse (L3.IntS L3.W16))
  assertEqual "L3.W8" 16 (sse (L3.IntS L3.W8))
  assertEqual "Float" 4 (sse L3.FloatS)
  assertEqual "Sym" 2 (sse L3.SymS)
  assertEqual "Char" 16 (sse L3.CharS)
  assertEqual "Bool" 16 (sse L3.BoolS)
  sequence_ [ assertEqual ("AVX2 doubles " ++ show s) (2 * sse s) (avx s)
            | s <- allScalars ]

case_w32_scalar_is_four_bytes_and_vector_is_sixteen :: Assertion
case_w32_scalar_is_four_bytes_and_vector_is_sixteen = do
  assertEqual "L3.W32 lane bytes" 4 (L3.simdScalarBytes (L3.IntS L3.W32))
  assertEqual "L3.W64 lane bytes" 8 (L3.simdScalarBytes (L3.IntS L3.W64))
  -- Lanes times scalar bytes is the register width, at BOTH widths: this is
  -- the invariant every cursor bump depends on.
  sequence_
    [ assertEqual (show (rb, s) ++ " must fill the register")
                  rb (L3.simdLanes rb s * L3.simdScalarBytes s)
    | rb <- [L3.simdRegisterBytes, L3.simdRegisterBytesAvx2]
    , s <- allScalars ]

-- | Every nameable lane count fills exactly one register, at each width.
case_only_register_filling_lane_counts_are_valid :: Assertion
case_only_register_filling_lane_counts_are_valid = do
  sequence_
    [ assertEqual (show (rb, s, n)) (n == L3.simdLanes rb s)
                  (L3.simdLanesValid rb s n)
    | rb <- [L3.simdRegisterBytes, L3.simdRegisterBytesAvx2]
    , s <- allScalars, n <- [1,2,4,8,16,32,64] ]
  -- 'simdLanesValidAny' is the backend's pure check: it accepts a lane count
  -- that fills EITHER register, and nothing else.
  sequence_
    [ assertEqual ("any " ++ show (s, n))
        (n == L3.simdLanes L3.simdRegisterBytes s
           || n == L3.simdLanes L3.simdRegisterBytesAvx2 s)
        (L3.simdLanesValidAny s n)
    | s <- allScalars, n <- [1,2,4,8,16,32,64] ]

-- | @(IntS W64, 4)@ is a 256-bit tiling: valid under AVX2, invalid under
-- baseline SSE2.  It must never be accepted at the SSE2 width -- that stale
-- mapping dates from the @--int32@ era, when a "W64" integer could physically
-- be 4 bytes, and it would lower a W64 node with 32-bit helpers.
case_w64_with_four_lanes_is_width_specific :: Assertion
case_w64_with_four_lanes_is_width_specific = do
  assertBool "(IntS W64, 4) must not tile a 128-bit register"
             (not (L3.simdLanesValid L3.simdRegisterBytes (L3.IntS L3.W64) 4))
  assertBool "(IntS W64, 4) must tile a 256-bit register"
             (L3.simdLanesValid L3.simdRegisterBytesAvx2 (L3.IntS L3.W64) 4)
  -- A count that fills neither register is invalid however it is asked.
  assertBool "(IntS W64, 3) fills no register"
             (not (L3.simdLanesValidAny (L3.IntS L3.W64) 3))

case_w32_with_wrong_lane_counts_is_invalid :: Assertion
case_w32_with_wrong_lane_counts_is_invalid = do
  -- 4 fills a 128-bit register and 8 fills a 256-bit one; nothing else is a
  -- W32 tiling at all.
  sequence_ [ assertBool ("(IntS L3.W32, " ++ show n ++ ") must be invalid")
                         (not (L3.simdLanesValidAny (L3.IntS L3.W32) n))
            | n <- [1, 2, 16, 32] ]
  sequence_ [ assertBool ("(IntS L3.W32, " ++ show n ++ ") must be valid somewhere")
                         (L3.simdLanesValidAny (L3.IntS L3.W32) n)
            | n <- [4, 8] ]

-- | The L3.W32 row of the matrix, stated explicitly.
case_w32_capability_matrix :: Assertion
case_w32_capability_matrix = do
  sequence_ [ assertBool (L3.vecOpName op ++ " must be packed-capable at L3.W32")
                         (L3.simdCapable op (L3.IntS L3.W32))
            | op <- [ L3.VecOpBroadcast, L3.VecOpLoad, L3.VecOpStore
                    , L3.VecOpAdd, L3.VecOpSub, L3.VecOpEq, L3.VecOpSelect ]
                    ++ L3.orderedCmps ]
  assertBool "mul IS capable at W32 (two _mm_mul_epu32 + shuffles, baseline SSE2)"
             (L3.simdCapable L3.VecOpMul (L3.IntS L3.W32))
  sequence_ [ assertBool (L3.vecOpName op ++ " must NOT be capable at L3.W32 "
                            ++ "(no packed SSE2 implementation; loop stays scalar)")
                         (not (L3.simdCapable op (L3.IntS L3.W32)))
            | op <- [ L3.VecOpDiv, L3.VecOpMod ] ]

-- | W64 keeps every operation it had BEFORE ordered comparisons existed.  The
-- four new ordered comparisons are deliberately excluded: SSE2 has no packed
-- signed 64-bit compare (even _mm_cmpgt_epi64 is SSE4.2), so a W64 ordered
-- comparison must leave its loop scalar.  A blanket `True` row would have
-- silently claimed them.
case_w64_capability_matrix :: Assertion
case_w64_capability_matrix = do
  sequence_ [ assertBool (L3.vecOpName op ++ " must remain capable at W64")
                         (L3.simdCapable op (L3.IntS L3.W64))
            | op <- allVecOps
            , op /= L3.VecOpMul
            , op `notElem` L3.orderedCmps ]
  sequence_ [ assertBool (L3.vecOpName op ++ " must NOT be capable at W64")
                         (not (L3.simdCapable op (L3.IntS L3.W64)))
            | op <- L3.orderedCmps ]
  -- Packed 64-bit multiply is a de-optimization, not an acceleration: seven
  -- instructions for two lanes against one `imul` per lane.  Measured 0.55x
  -- against the scalar loop.  Pin it OFF so it cannot be re-enabled silently.
  assertBool "multiply must NOT be capable at W64"
             (not (L3.simdCapable L3.VecOpMul (L3.IntS L3.W64)))

-- | W16/W8 packed SIMD is enabled.  What must stay off is the set of
-- operations SSE2 cannot do packed at those widths; see
-- 'case_capability_matrix_all_widths' for the full row-by-row matrix.
case_w16_and_w8_unsupported_ops_stay_off :: Assertion
case_w16_and_w8_unsupported_ops_stay_off = do
  sequence_ [ assertBool (show w ++ " is SIMD-enabled") (L3.simdScalarEnabled (L3.IntS w))
            | w <- [L3.W16, L3.W8] ]
  sequence_ [ assertBool ("W16 " ++ L3.vecOpName op ++ " must stay scalar")
                         (not (L3.simdCapable op (L3.IntS L3.W16)))
            | op <- [L3.VecOpDiv, L3.VecOpMod] ]
  assertBool "W8 mul IS capable (unpack to 16-bit, _mm_mullo_epi16, mask, repack)"
             (L3.simdCapable L3.VecOpMul (L3.IntS L3.W8))
  sequence_ [ assertBool ("W8 " ++ L3.vecOpName op ++ " must stay scalar")
                         (not (L3.simdCapable op (L3.IntS L3.W8)))
            | op <- [L3.VecOpDiv, L3.VecOpMod] ]

-- | An unsupported (op, scalar) must not even be nameable as a helper, so a
-- backend "yes" can never silently appear for something the vectorizer refuses.
case_unsupported_combinations_have_no_helper_name :: Assertion
case_unsupported_combinations_have_no_helper_name =
  sequence_
    [ do r <- try (evaluate (length (show (vecHelperNameOrError op s))))
         let lanes = L3.simdLanes L3.simdRegisterBytes s
         case (L3.simdCapable op s && L3.simdLanesValid L3.simdRegisterBytes s lanes, r) of
           (True, Right _) -> pure ()
           (False, Left (_ :: ErrorCall)) -> pure ()
           (True, Left e) -> assertFailure $ "capable but unnameable: " ++ show (op, s) ++ ": " ++ show e
           (False, Right _) -> assertFailure $ "incapable but nameable: " ++ show (op, s)
    | op <- allVecOps, s <- allScalars ]

-- | Helper names are derived from the typed op and the scalar's real width.
case_helper_names_are_derived_from_width :: Assertion
case_helper_names_are_derived_from_width = do
  assertEqual "L3.W32 add" "gib_vec_add_int32x4"
              (vecHelperNameOrError L3.VecOpAdd (L3.IntS L3.W32))
  assertEqual "L3.W64 add" "gib_vec_add_int64x2"
              (vecHelperNameOrError L3.VecOpAdd (L3.IntS L3.W64))
  assertEqual "L3.W32 select" "gib_vec_select_int32x4"
              (vecHelperNameOrError L3.VecOpSelect (L3.IntS L3.W32))

--------------------------------------------------------------------------------
-- The extended W16 / W8 capability matrix and the common logical stride
--------------------------------------------------------------------------------

-- | The full matrix, stated row by row so a silent change to any cell fails.
case_capability_matrix_all_widths :: Assertion
case_capability_matrix_all_widths = do
  let expect w ops =
        sequence_ [ assertEqual (show w ++ " " ++ L3.vecOpName op)
                                (op `elem` ops) (L3.simdCapable op (L3.IntS w))
                  | op <- allVecOps ]
      -- Data movement, add/sub, and the FULL comparison family (equality plus
      -- the four ordered comparisons) with select.
      movement = [ L3.VecOpBroadcast, L3.VecOpLoad, L3.VecOpStore
                 , L3.VecOpAdd, L3.VecOpSub, L3.VecOpEq, L3.VecOpSelect ]
                 ++ L3.orderedCmps
  -- W64: the grandfathered row MINUS the ordered comparisons (SSE2 cannot do
  -- those packed at 64 bits) and MINUS multiply, which at two lanes costs
  -- more than the scalar `imul`s it replaces -- see the W64 note in
  -- 'L3.simdCapable'.  Divide and modulus stay: they still spill, but a
  -- tens-of-cycles division swamps the spill where a 3-cycle multiply does
  -- not.
  expect L3.W64 (filter (\o -> o /= L3.VecOpMul && o `notElem` L3.orderedCmps) allVecOps)
  -- W32: no packed multiply (_mm_mullo_epi32 is SSE4.1), no divide/modulus.
  expect L3.W32 (L3.VecOpMul : movement)
  -- W16: additionally a GENUINE packed multiply, _mm_mullo_epi16, baseline SSE2.
  expect L3.W16 (L3.VecOpMul : movement)
  -- W8: no multiply at all in SSE2, no divide/modulus.
  expect L3.W8 (L3.VecOpMul : movement)

case_all_integer_widths_are_simd_enabled :: Assertion
case_all_integer_widths_are_simd_enabled =
  sequence_ [ assertBool (show w) (L3.simdScalarEnabled (L3.IntS w))
            | w <- [L3.W8, L3.W16, L3.W32, L3.W64] ]

case_w16_and_w8_lane_counts :: Assertion
case_w16_and_w8_lane_counts = do
  assertEqual "W16 lanes" 8 (L3.simdLanes sseBytes (L3.IntS L3.W16))
  assertEqual "W8 lanes" 16 (L3.simdLanes sseBytes (L3.IntS L3.W8))
  assertEqual "W16 lane bytes" 2 (L3.simdScalarBytes (L3.IntS L3.W16))
  assertEqual "W8 lane bytes" 1 (L3.simdScalarBytes (L3.IntS L3.W8))
  sequence_ [ assertEqual ("register fill " ++ show w) 16
                          (L3.simdLanes sseBytes (L3.IntS w) * L3.simdScalarBytes (L3.IntS w))
            | w <- [L3.W8, L3.W16, L3.W32, L3.W64] ]

case_w16_w8_wrong_lane_counts_are_invalid :: Assertion
case_w16_w8_wrong_lane_counts_are_invalid = do
  sequence_ [ assertBool ("(W16," ++ show n ++ ")") (not (L3.simdLanesValid sseBytes (L3.IntS L3.W16) n))
            | n <- [2, 4, 16] ]
  sequence_ [ assertBool ("(W8," ++ show n ++ ")") (not (L3.simdLanesValid sseBytes (L3.IntS L3.W8) n))
            | n <- [2, 4, 8] ]
  assertBool "(W16,8) is valid" (L3.simdLanesValid sseBytes (L3.IntS L3.W16) 8)
  assertBool "(W8,16) is valid" (L3.simdLanesValid sseBytes (L3.IntS L3.W8) 16)

-- | The common logical stride, over every scalar-width combination the
-- codegen must support.  Each row asserts stride, per-scalar groups, and the
-- bytes each field cursor advances -- which must always be @stride * scalarBytes@.
case_logical_stride_and_groups :: Assertion
case_logical_stride_and_groups =
  sequence_
    [ do let scalars = map L3.IntS ws
             stride = L3.simdLogicalStride sseBytes scalars
         assertEqual (show ws ++ " stride") expStride stride
         assertBool  (show ws ++ " stride must tile every scalar")
                     (L3.simdStrideValid sseBytes stride scalars)
         sequence_
           [ do let s = L3.IntS w
                    g = L3.simdGroups sseBytes stride s
                assertEqual (show ws ++ " " ++ show w ++ " groups") expG g
                -- groups * lanes == stride, so the cursor advance is exact
                assertEqual (show ws ++ " " ++ show w ++ " covers the stride")
                            stride (g * L3.simdLanes sseBytes s)
                assertEqual (show ws ++ " " ++ show w ++ " bytes advanced")
                            expBytes (g * L3.simdLanes sseBytes s * L3.simdScalarBytes s)
           | (w, expG, expBytes) <- perScalar ]
    | (ws, expStride, perScalar) <-
        [ ([L3.W64],                     4,  [(L3.W64, 2, 32)])
        , ([L3.W32],                     4,  [(L3.W32, 1, 16)])
        , ([L3.W16],                     8,  [(L3.W16, 1, 16)])
        , ([L3.W8],                     16,  [(L3.W8,  1, 16)])
        , ([L3.W16, L3.W32],             8,  [(L3.W16, 1, 16), (L3.W32, 2, 32)])
        , ([L3.W8,  L3.W32],            16,  [(L3.W8,  1, 16), (L3.W32, 4, 64)])
        , ([L3.W8, L3.W16, L3.W32, L3.W64], 16,
             [(L3.W8, 1, 16), (L3.W16, 2, 32), (L3.W32, 4, 64), (L3.W64, 8, 128)])
        ] ]

-- | W64-only loops must keep their historical stride of 4: adding W16/W8
-- packed support must not change any accepted W64 output.
case_w64_only_stride_is_unchanged :: Assertion
case_w64_only_stride_is_unchanged = do
  assertEqual "W64 stride" 4 (L3.simdLogicalStride sseBytes [L3.IntS L3.W64])
  assertEqual "W64 groups" 2 (L3.simdGroups sseBytes 4 (L3.IntS L3.W64))
  assertEqual "empty stride floor" 4 (L3.simdLogicalStride sseBytes [])

case_w16_w8_helper_names :: Assertion
case_w16_w8_helper_names = do
  assertEqual "W16 mul" "gib_vec_mul_int16x8"
              (vecHelperNameOrError L3.VecOpMul (L3.IntS L3.W16))
  assertEqual "W16 add" "gib_vec_add_int16x8"
              (vecHelperNameOrError L3.VecOpAdd (L3.IntS L3.W16))
  assertEqual "W8 add" "gib_vec_add_int8x16"
              (vecHelperNameOrError L3.VecOpAdd (L3.IntS L3.W8))
  assertEqual "W8 select" "gib_vec_select_int8x16"
              (vecHelperNameOrError L3.VecOpSelect (L3.IntS L3.W8))

--------------------------------------------------------------------------------
-- Emitted C for the W16 / W8 helpers
--------------------------------------------------------------------------------

narrowC :: L3.Scalar -> IO String
narrowC s = genC' config64 (progWith (broadcastBody s (L3.simdLanes sseBytes s)))

case_w16_helpers_use_packed_intrinsics :: Assertion
case_w16_helpers_use_packed_intrinsics = do
  c <- narrowC (L3.IntS L3.W16)
  sequence_
    [ do let d = helperDef nm c
         assertBool (nm ++ " must use " ++ i ++ ":\n" ++ d) (i `L.isInfixOf` d)
    | (nm, i) <- [ ("gib_vec_broadcast_int16x8", "_mm_set1_epi16")
                 , ("gib_vec_load_int16x8",      "_mm_loadu_si128")
                 , ("gib_vec_store_int16x8",     "_mm_storeu_si128")
                 , ("gib_vec_add_int16x8",       "_mm_add_epi16")
                 , ("gib_vec_sub_int16x8",       "_mm_sub_epi16")
                 , ("gib_vec_mul_int16x8",       "_mm_mullo_epi16")
                 , ("gib_vec_eq_int16x8",        "_mm_cmpeq_epi16") ] ]
  assertBool "W16 broadcast must take GibInt16"
             ("GibInt16 x" `L.isInfixOf` helperDef "gib_vec_broadcast_int16x8" c)

case_w8_helpers_use_packed_intrinsics :: Assertion
case_w8_helpers_use_packed_intrinsics = do
  c <- narrowC (L3.IntS L3.W8)
  sequence_
    [ do let d = helperDef nm c
         assertBool (nm ++ " must use " ++ i ++ ":\n" ++ d) (i `L.isInfixOf` d)
    | (nm, i) <- [ ("gib_vec_broadcast_int8x16", "_mm_set1_epi8")
                 , ("gib_vec_load_int8x16",      "_mm_loadu_si128")
                 , ("gib_vec_store_int8x16",     "_mm_storeu_si128")
                 , ("gib_vec_add_int8x16",       "_mm_add_epi8")
                 , ("gib_vec_sub_int8x16",       "_mm_sub_epi8")
                 , ("gib_vec_eq_int8x16",        "_mm_cmpeq_epi8") ] ]
  let bc = helperDef "gib_vec_broadcast_int8x16" c
  assertBool "W8 broadcast must take GibInt8" ("GibInt8 x" `L.isInfixOf` bc)
  -- Plain `char` has implementation-defined signedness; a negative Int8 would
  -- broadcast the wrong bit pattern on a platform where it is unsigned.
  assertBool ("W8 broadcast must convert through signed char:\n" ++ bc)
             ("signed char" `L.isInfixOf` bc)

case_narrow_helpers_have_no_scalar_lane_spills :: Assertion
case_narrow_helpers_have_no_scalar_lane_spills =
  sequence_
    [ do c <- narrowC s
         sequence_
           [ do let d = helperDef nm c
                assertBool (nm ++ " must not declare a scalar lane array:\n" ++ d)
                  (not (any (`L.isInfixOf` d)
                        ["int8_t av[", "int16_t av[", "int32_t av[", "int64_t av["]))
                assertBool (nm ++ " must not reassemble lanes:\n" ++ d)
                  (not (any (`L.isInfixOf` d)
                        ["_mm_set_epi8", "_mm_set_epi16", "_mm_set_epi32", "_mm_set_epi64x"]))
                assertBool (nm ++ " must not mention the infrastructure GibInt:\n" ++ d)
                  (not ("GibInt " `L.isInfixOf` d))
           | nm <- names ]
    | (s, names) <-
        [ (L3.IntS L3.W16, [ "gib_vec_broadcast_int16x8", "gib_vec_load_int16x8"
                           , "gib_vec_store_int16x8", "gib_vec_add_int16x8"
                           , "gib_vec_sub_int16x8", "gib_vec_mul_int16x8"
                           , "gib_vec_eq_int16x8", "gib_vec_select_int16x8" ])
        , (L3.IntS L3.W8,  [ "gib_vec_broadcast_int8x16", "gib_vec_load_int8x16"
                           , "gib_vec_store_int8x16", "gib_vec_add_int8x16"
                           , "gib_vec_sub_int8x16", "gib_vec_eq_int8x16"
                           , "gib_vec_mul_int8x16", "gib_vec_select_int8x16" ]) ] ]

-- | Unsupported narrow operations must emit no helper at all.
case_unsupported_narrow_helpers_are_not_emitted :: Assertion
case_unsupported_narrow_helpers_are_not_emitted = do
  c <- narrowC (L3.IntS L3.W16)
  sequence_ [ assertBool (nm ++ " must not be emitted") (not (nm `L.isInfixOf` c))
            | nm <- [ "gib_vec_div_int16x8", "gib_vec_mod_int16x8"
                    , "gib_vec_div_int8x16", "gib_vec_mod_int8x16"
                    , "gib_vec_div_int32x4", "gib_vec_mod_int32x4" ] ]

case_unsupported_narrow_vector_ir_is_rejected :: Assertion
case_unsupported_narrow_vector_ir_is_rejected =
  sequence_
    [ do r <- genC config64 (progWith (binBody mk s (L3.simdLanes sseBytes s)))
         case r of
           Left e -> assertBool ("must name the unsupported combination: " ++ show e)
                                ("unsupported SIMD operation" `L.isInfixOf` show e)
           Right c -> assertFailure ("codegen accepted " ++ lbl ++ ":\n" ++ take 400 c)
    | (mk, lbl, s) <- [ (VecDiv, "VecDiv at W32", L3.IntS L3.W32)
                      , (VecDiv, "VecDiv at W16", L3.IntS L3.W16)
                      , (VecMod, "VecMod at W16", L3.IntS L3.W16)
                      , (VecDiv, "VecDiv at W8",  L3.IntS L3.W8) ] ]

case_w16_w8_register_types :: Assertion
case_w16_w8_register_types =
  sequence_
    [ do r <- genC config64 (progWith (broadcastBody s (L3.simdLanes sseBytes s)))
         case r of
           Right c -> assertBool (show s ++ " must declare __m128i") ("__m128i" `L.isInfixOf` c)
           Left e -> assertFailure (show s ++ " failed to lower: " ++ show e)
    | s <- [L3.IntS L3.W16, L3.IntS L3.W8] ]

--------------------------------------------------------------------------------
-- Emitted C for the W32 helpers
--------------------------------------------------------------------------------

-- | The generated C, from any program (the helper prelude is emitted always).
w32C :: IO String
w32C = genC' config64 (progWith (broadcastBody (L3.IntS L3.W32) 4))

-- | Extract one `static inline ... name(...) { ... }` definition.
helperDef :: String -> String -> String
helperDef nm c =
  case dropWhile (\l -> not ((nm ++ "(") `L.isInfixOf` l)) (lines c) of
    [] -> error ("no definition of " ++ nm ++ " in generated C")
    (l:rest) -> unlines (l : takeWhile (/= "}") rest)

case_w32_broadcast_takes_gibint32_not_gibint :: Assertion
case_w32_broadcast_takes_gibint32_not_gibint = do
  c <- w32C
  let d = helperDef "gib_vec_broadcast_int32x4" c
  assertBool ("broadcast must take GibInt32:\n" ++ d) ("GibInt32 x" `L.isInfixOf` d)
  assertBool ("broadcast must not take the infrastructure GibInt:\n" ++ d)
             (not ("(GibInt x)" `L.isInfixOf` d))
  assertBool ("broadcast must be packed:\n" ++ d) ("_mm_set1_epi32" `L.isInfixOf` d)

case_w32_load_store_are_unaligned_128_bit :: Assertion
case_w32_load_store_are_unaligned_128_bit = do
  c <- w32C
  let ld = helperDef "gib_vec_load_int32x4" c
      st = helperDef "gib_vec_store_int32x4" c
  assertBool ("load must be unaligned 128-bit:\n" ++ ld) ("_mm_loadu_si128" `L.isInfixOf` ld)
  assertBool ("store must be unaligned 128-bit:\n" ++ st) ("_mm_storeu_si128" `L.isInfixOf` st)
  assertBool "load must return __m128i" ("__m128i gib_vec_load_int32x4" `L.isInfixOf` c)

case_w32_arithmetic_uses_packed_intrinsics :: Assertion
case_w32_arithmetic_uses_packed_intrinsics = do
  c <- w32C
  sequence_
    [ do let d = helperDef nm c
         assertBool (nm ++ " must use " ++ intrin ++ ":\n" ++ d) (intrin `L.isInfixOf` d)
    | (nm, intrin) <- [ ("gib_vec_add_int32x4", "_mm_add_epi32")
                      , ("gib_vec_sub_int32x4", "_mm_sub_epi32")
                      , ("gib_vec_eq_int32x4", "_mm_cmpeq_epi32") ] ]

case_w32_select_uses_bitwise_mask :: Assertion
case_w32_select_uses_bitwise_mask = do
  c <- w32C
  let d = helperDef "gib_vec_select_int32x4" c
  sequence_ [ assertBool (i ++ " missing from select:\n" ++ d) (i `L.isInfixOf` d)
            | i <- ["_mm_or_si128", "_mm_and_si128", "_mm_andnot_si128"] ]

-- | THE performance-critical assertion: no supported W32 helper may spill the
-- register to a scalar array and loop over lanes.  A helper that does that is
-- slower than the scalar loop it replaced, and calling it SIMD is a lie.
case_supported_w32_helpers_have_no_scalar_lane_spills :: Assertion
case_supported_w32_helpers_have_no_scalar_lane_spills = do
  c <- w32C
  sequence_
    [ do let d = helperDef nm c
         assertBool (nm ++ " must not declare a scalar lane array:\n" ++ d)
                    (not ("int32_t av[" `L.isInfixOf` d) && not ("int64_t av[" `L.isInfixOf` d))
         assertBool (nm ++ " must not reassemble lanes with _mm_set_epi32:\n" ++ d)
                    (not ("_mm_set_epi32" `L.isInfixOf` d))
         assertBool (nm ++ " must not mention the infrastructure GibInt:\n" ++ d)
                    (not ("GibInt " `L.isInfixOf` d) || "GibInt32 " `L.isInfixOf` d)
    | nm <- [ "gib_vec_broadcast_int32x4", "gib_vec_load_int32x4"
            , "gib_vec_store_int32x4", "gib_vec_add_int32x4"
            , "gib_vec_sub_int32x4", "gib_vec_eq_int32x4"
            , "gib_vec_select_int32x4" ] ]

-- | The lane-spilling W32 mul/div/mod helpers are gone entirely, so no name
-- survives that implies SIMD performance while looping over lanes.
case_w32_mul_div_mod_helpers_are_not_emitted :: Assertion
case_w32_mul_div_mod_helpers_are_not_emitted = do
  c <- w32C
  sequence_ [ assertBool (nm ++ " must not be emitted (no packed SSE2 impl)")
                         (not (nm `L.isInfixOf` c))
            | nm <- [ "gib_vec_div_int32x4", "gib_vec_mod_int32x4" ] ]
  assertBool "W32 packed multiply IS emitted" ("gib_vec_mul_int32x4" `L.isInfixOf` c)

-- | Manually malformed W32 vector IR must be rejected loudly by the backend.
case_w32_mul_vector_ir_is_rejected :: Assertion
case_w32_mul_vector_ir_is_rejected = do
  r <- genC config64 (progWith (binBody VecDiv (L3.IntS L3.W32) 4))
  case r of
    Left e -> assertBool ("must name the unsupported combination, got: " ++ show e)
                         ("unsupported SIMD operation" `L.isInfixOf` show e)
    Right c -> assertFailure ("codegen accepted VecMul at (IntS W32, 4):\n" ++ c)

case_w32_wrong_lane_count_is_rejected :: Assertion
case_w32_wrong_lane_count_is_rejected = do
  -- A lane count is valid against the SELECTED register width, not against
  -- either width the backend can emit helpers for.  So 4 is right at sse2 and
  -- wrong at avx2, and 8 the other way round; the rest are wrong at both.
  sequence_
    [ do r <- genC cfg (progWith (broadcastBody (L3.IntS L3.W32) n))
         case r of
           Left e -> assertBool ("must explain the register invariant, got: " ++ show e)
                                (("does not fill a " ++ bits ++ "-bit register")
                                   `L.isInfixOf` show e)
           Right _ -> assertFailure ("codegen accepted (IntS W32, " ++ show n
                                       ++ ") at " ++ bits ++ " bits")
    | (cfg, bits, ns) <- [(config64, "128", [2, 8, 16, 32]), (configAvx2, "256", [2, 4, 16, 32])]
    , n <- ns ]
  sequence_
    [ do r <- genC cfg (progWith (broadcastBody (L3.IntS L3.W32) n))
         case r of
           Left e -> assertFailure ("codegen rejected valid (IntS W32, " ++ show n
                                      ++ "): " ++ show e)
           Right _ -> pure ()
    | (cfg, n) <- [(config64, 4), (configAvx2, 8)] ]

case_w32_simd_register_type_is_m128i :: Assertion
case_w32_simd_register_type_is_m128i = do
  c <- w32C
  assertBool "the W32 vector binding must be declared __m128i"
             ("__m128i" `L.isInfixOf` c)

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Which instruction sequence the helpers use is Gibbon's choice, not the C
-- preprocessor's.
--------------------------------------------------------------------------------

-- | The first line of the baseline W32 multiply body.
--
-- Specific to W32: the W64 multiply helper uses @_mm_mul_epu32@ too, at every
-- ISA, so the bare intrinsic name does not distinguish the two sequences.
w32BaselineMul :: String
w32BaselineMul = "__m128i even = _mm_mul_epu32(a, b);"

-- | At baseline SSE2 the emitted multiply is the _mm_mul_epu32 sequence.
case_sse2_emits_the_baseline_multiply :: Assertion
case_sse2_emits_the_baseline_multiply = do
  src <- genC' config64 emptyProg
  assertBool "expected the baseline W32 _mm_mul_epu32 sequence"
    (w32BaselineMul `L.isInfixOf` src)
  assertBool "must not emit the SSE4.1 multiply at baseline SSE2"
    (not ("return _mm_mullo_epi32" `L.isInfixOf` src))
  assertBool "must not emit the SSE4.1 64-bit compare at baseline SSE2"
    (not ("return _mm_cmpeq_epi64" `L.isInfixOf` src))

-- | At the SSE4.1 tier it is the single instruction, and only that.
case_sse41_emits_the_single_instruction_multiply :: Assertion
case_sse41_emits_the_single_instruction_multiply = do
  src <- genC' configSse41 emptyProg
  assertBool "expected _mm_mullo_epi32 at the SSE4.1 tier"
    ("return _mm_mullo_epi32" `L.isInfixOf` src)
  assertBool "expected _mm_cmpeq_epi64 at the SSE4.1 tier"
    ("return _mm_cmpeq_epi64" `L.isInfixOf` src)
  assertBool "the baseline W32 multiply sequence must not also be emitted"
    (not (w32BaselineMul `L.isInfixOf` src))

-- | And the generated C never asks the preprocessor which one to use.
--
-- Inferring the instruction set from `__SSE4_1__` is what VW-17 forbids: the
-- C compiler's own target, which -mavx2 and -march=native also set, decided
-- what Gibbon emitted while Gibbon reported something else.
case_generated_c_does_not_consult_the_preprocessor_for_sse41 :: Assertion
case_generated_c_does_not_consult_the_preprocessor_for_sse41 =
  mapM_
    (\(cfg, nm) -> do
       src <- genC' cfg emptyProg
       assertBool (nm ++ ": generated C must not branch on __SSE4_1__")
         (not ("__SSE4_1__" `L.isInfixOf` src)))
    [(config64, "sse2"), (configSse41, "sse4.1"), (configAvx2, "avx2")]

-- | A binary compiled for an instruction set above the x86-64 baseline checks
-- for it once, at the top of main, before anything else runs.  Without that a
-- pre-AVX2 machine takes SIGILL at whatever instruction the C compiler put
-- first, with no diagnostic.
case_avx2_binary_checks_the_cpu_at_startup :: Assertion
case_avx2_binary_checks_the_cpu_at_startup = do
  c <- genC' configAvx2 emptyProg
  assertBool "expected a startup ISA check"
    ("__builtin_cpu_supports(\"avx2\")" `L.isInfixOf` c)
  -- One definition and one call: a startup branch, not a per-loop one.
  2 @=? length (filter ("gib_require_simd_isa" `L.isInfixOf`) (lines c))
  assertBool "the check must name the flag that selected the ISA"
    ("--opt-vectorization" `L.isInfixOf` c || "--simd-isa=avx2" `L.isInfixOf` c)

case_sse41_binary_checks_for_sse41 :: Assertion
case_sse41_binary_checks_for_sse41 = do
  c <- genC' configSse41 emptyProg
  assertBool "expected an sse4.1 startup check"
    ("__builtin_cpu_supports(\"sse4.1\")" `L.isInfixOf` c)

-- | SSE2 is the x86-64 baseline, so a baseline build gets no check at all.
case_baseline_binary_has_no_startup_check :: Assertion
case_baseline_binary_has_no_startup_check = do
  c <- genC' config64 emptyProg
  assertBool "a baseline build must not emit a CPU check"
    (not ("gib_require_simd_isa" `L.isInfixOf` c))

codegenSimdTests :: TestTree
codegenSimdTests = testGroup "CodegenSimd" [tests]

tests :: TestTree
tests = $(testGroupGenerator)
