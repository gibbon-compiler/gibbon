{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-- | The timing-output contract (VW-25).
--
-- All backends must expose the same deterministic timing metadata for the same
-- source construct:
--
-- @
--   iterated     (flg == True)   ITER TIMES: / ITERS: / SIZE: / BATCHTIME: / SELFTIMED:
--   non-iterated (flg == False)  SELFTIMED:   -- and nothing else
-- @
--
-- `ITERS:` and `SIZE:` are deterministic run configuration, so
-- "OutputCompare" compares them like any other output.  Their /absence/ from
-- the non-iterated form is therefore part of the output contract, not
-- something normalization is allowed to paper over.
--
-- Before this was fixed, the C backend alone printed `SIZE:` for a
-- non-iterated timed expression, while "Gibbon.L1.Interp",
-- "Gibbon.L2.Interp", "Gibbon.L4.Interp" and the Racket @time@ macro in
-- @gibbon/main.rkt@ all printed `SELFTIMED:` alone.  Once the harness stopped
-- discarding timing diffs (VW-03) that made every non-iterated @(time ..)@
-- example unmatchable against its Racket-generated answer.
module TimingOutputContract
  ( timingOutputContractTests
  ) where

import           Control.Exception ( ErrorCall, evaluate, try )
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.List as L
import qualified Data.Map as M

import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.TH

import           Gibbon.Common
import           Gibbon.Language ( FunMeta(..), FunRec(..), FunInline(..) )
import           Gibbon.L1.Interp ()
import           Gibbon.L1.Syntax ( emptyDD )
import qualified Gibbon.L1.Syntax as L1
import           Gibbon.L4.Syntax
import           Gibbon.Passes.Codegen ( codegenProg )

import           OutputCompare ( compareNormalized )

--------------------------------------------------------------------------------
-- Codegen harness (an L4 program whose body is just the timed form)

timedProg :: Bool -> Prog
timedProg flg =
  Prog
    { infoTable = M.empty
    , symbolTable = M.empty
    , fundefs =
        [ FunDecl
            { funName = "timing_probe"
            , funArgs = []
            , funRetTy = ProdTy []
            , funBody = LetTimedT flg [] (RetValsT []) (RetValsT [])
            , isPure = False
            , funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , mainExp = Nothing
    }

genC :: Prog -> IO String
genC prg = do
  r <- try (codegenProg defaultConfig prg >>= \s -> evaluate (length s) >> pure s)
  case r of
    Right s              -> pure s
    Left (e :: ErrorCall) -> assertFailure ("codegenProg failed: " ++ show e)

-- | How many times a printf of this record appears in the generated C.
printfCount :: String -> String -> Int
printfCount record src =
  length (filter (needle `L.isInfixOf`) (lines src))
  where needle = "printf(\"" ++ record

-- | How many lines contain a call to this RTS function.
callCount :: String -> String -> Int
callCount fn src = length (filter ((fn ++ "();") `L.isInfixOf`) (lines src))

timingArrayCount :: String -> Int
timingArrayCount src =
  length (filter ("gib_print_timing_array" `L.isInfixOf`) (lines src))

--------------------------------------------------------------------------------
-- The C backend

case_non_iterated_codegen_emits_only_selftimed :: Assertion
case_non_iterated_codegen_emits_only_selftimed = do
  src <- genC (timedProg False)
  1 @=? printfCount "SELFTIMED:" src
  assertEqual "non-iterated must not print SIZE:"      0 (printfCount "SIZE:" src)
  assertEqual "non-iterated must not print ITERS:"     0 (printfCount "ITERS:" src)
  assertEqual "non-iterated must not print BATCHTIME:" 0 (printfCount "BATCHTIME:" src)
  assertEqual "non-iterated must not print ITER TIMES" 0 (timingArrayCount src)

case_iterated_codegen_emits_all_five_records :: Assertion
case_iterated_codegen_emits_all_five_records = do
  src <- genC (timedProg True)
  assertEqual "iterated must print ITER TIMES" 1 (timingArrayCount src)
  assertEqual "iterated must print ITERS:"     1 (printfCount "ITERS:" src)
  assertEqual "iterated must print SIZE:"      1 (printfCount "SIZE:" src)
  assertEqual "iterated must print BATCHTIME:" 1 (printfCount "BATCHTIME:" src)
  assertEqual "iterated must print SELFTIMED:" 1 (printfCount "SELFTIMED:" src)

-- | The deterministic echo still goes through the GibInt-typed RTS getters.
case_iterated_codegen_keeps_percent_ld_getters :: Assertion
case_iterated_codegen_keeps_percent_ld_getters = do
  src <- genC (timedProg True)
  assertBool "ITERS: must read gib_get_iters_param() with %ld"
    ("printf(\"ITERS: %ld\\n\", gib_get_iters_param());" `L.isInfixOf` src)
  assertBool "SIZE: must read gib_get_size_param() with %ld"
    ("printf(\"SIZE: %ld\\n\", gib_get_size_param());" `L.isInfixOf` src)

-- | Region-chunk reclamation is bracketed around each timed iteration.
--
-- A benchmark iteration rewinds to its output region's first chunk and
-- re-grows it, and `gib_grow_region_on_heap` overwrites the link to the
-- previous iteration's chunk chain, stranding it.  Memory therefore grew by
-- one whole output value per iteration (929 MB/iteration for a 100M-element
-- list, i.e. 94 GB over 101 iterations -- an OOM kill).
--
-- The calls are emitted unconditionally; whether they do anything is decided
-- by -D_GIBBON_REGIONRESET at C-compile time, so that the pre-existing
-- behaviour stays exactly recoverable.
case_iterated_codegen_brackets_region_chunk_reclaim :: Assertion
case_iterated_codegen_brackets_region_chunk_reclaim = do
  src <- genC (timedProg True)
  assertEqual "iterated must open a region-chunk bracket"
    1 (callCount "gib_region_chunk_save_state" src)
  assertEqual "iterated must close the region-chunk bracket"
    1 (callCount "gib_region_chunk_restore_state" src)

-- | The non-iterated form has no loop, so nothing to bracket.  Emitting the
-- calls there would free chunks that nothing is about to re-grow.
case_non_iterated_codegen_has_no_region_chunk_bracket :: Assertion
case_non_iterated_codegen_has_no_region_chunk_bracket = do
  src <- genC (timedProg False)
  assertEqual "non-iterated must not open a region-chunk bracket"
    0 (callCount "gib_region_chunk_save_state" src)
  assertEqual "non-iterated must not close one"
    0 (callCount "gib_region_chunk_restore_state" src)

-- | The reclaim must sit AFTER the closing clock_gettime.
--
-- This is a measurement-fidelity requirement, not tidiness: freeing inside the
-- timed window would charge the benchmark for work the un-fixed compiler never
-- did.  Reported times must be unchanged by this feature.
case_region_chunk_restore_is_outside_the_timed_window :: Assertion
case_region_chunk_restore_is_outside_the_timed_window = do
  src <- genC (timedProg True)
  let ls        = lines src
      idxOf nee = L.findIndex (nee `L.isInfixOf`) ls
  case (idxOf "gib_region_chunk_save_state", idxOf "clock_gettime(CLOCK_MONOTONIC_RAW, &begin",
        idxOf "clock_gettime(CLOCK_MONOTONIC_RAW, &end", idxOf "gib_region_chunk_restore_state") of
    (Just saveIx, Just beginIx, Just endIx, Just restoreIx) -> do
      assertBool "save_state must precede the opening clock_gettime"
        (saveIx < beginIx)
      assertBool "restore_state must follow the closing clock_gettime"
        (restoreIx > endIx)
    other -> assertFailure ("missing a landmark in generated C: " ++ show other)

-- | Reclaim is skipped on the final iteration, whose result outlives the loop
-- and is consumed by the code after it.  It shares the existing guard that the
-- bump-allocator restore already uses for the same reason.
case_region_chunk_reclaim_skips_the_last_iteration :: Assertion
case_region_chunk_reclaim_skips_the_last_iteration = do
  src <- genC (timedProg True)
  -- Look BACKWARDS from the call for the nearest guard line.  Matching on the
  -- emitted text, not the source text: the pretty-printer spaces the operator
  -- out to `gib_get_iters_param() - 1`.
  let ls = lines src
      isGuard l = "gib_get_iters_param()" `L.isInfixOf` l && "!=" `L.isInfixOf` l
      guarded needle =
        case L.findIndex (needle `L.isInfixOf`) ls of
          Nothing -> False
          Just ix -> any isGuard (take 4 (reverse (take ix ls)))
  assertBool "save_state must sit under the != iters-1 guard"
    (guarded "gib_region_chunk_save_state")
  assertBool "restore_state must sit under the != iters-1 guard"
    (guarded "gib_region_chunk_restore_state")

--------------------------------------------------------------------------------
-- The interpreters, which are the reference the C backend must match.
--
-- These run the real interpreter and read its captured log, rather than
-- asserting against a copy of the emitter's source text.

-- | @let x = <timed> 42 in x@
timedL1 :: Bool -> L1.Prog1
timedL1 flg =
  L1.Prog emptyDD M.empty
    (Just ( L1.LetE ("x", [], L1.IntTy L1.W64, L1.TimeIt (L1.mkLitE64 42) (L1.IntTy L1.W64) flg)
                    (L1.VarE "x")
          , L1.IntTy L1.W64 ))

interpLog :: Bool -> IO [String]
interpLog flg = do
  (_, _v, logs) <- L1.gInterpProg () (RunConfig 1 1 dbgLvl False) (timedL1 flg)
  pure (lines (BL.unpack logs))

recordsIn :: [String] -> [String]
recordsIn = concatMap tag
  where
    tag l = [ r | r <- ["ITER TIMES:", "ITERS:", "SIZE:", "BATCHTIME:", "SELFTIMED:"]
                , r `L.isPrefixOf` l ]

case_l1_interpreter_non_iterated_emits_only_selftimed :: Assertion
case_l1_interpreter_non_iterated_emits_only_selftimed = do
  ls <- interpLog False
  ["SELFTIMED:"] @=? recordsIn ls

case_l1_interpreter_iterated_emits_iters_and_size :: Assertion
case_l1_interpreter_iterated_emits_iters_and_size = do
  ls <- interpLog True
  ["ITERS:", "SIZE:", "BATCHTIME:"] @=? recordsIn ls

--------------------------------------------------------------------------------
-- Agreement, through the real comparator (not a copy of it).
--
-- The literal strings below are transcribed from actual runs: the Racket
-- column from `racket -A .racket_sandbox <prog>.gib`, the Gibbon column from
-- the compiled executable.

cmp :: String -> String -> Maybe String
cmp = compareNormalized "answer file"

racketNonIter, gibbonNonIter :: String
racketNonIter = "SELFTIMED: 0.0\n42\n"
gibbonNonIter = "SELFTIMED: 2.790000e-07\n42\n"

racketIter, gibbonIter :: String
racketIter = "ITERS: 1\nSIZE: 1\nBATCHTIME: 0.0\n42\n"
gibbonIter = "ITER TIMES: [0.000000]\nITERS: 1\nSIZE: 1\n\
             \BATCHTIME: 7.600000e-08\nSELFTIMED: 7.600000e-08\n42\n"

case_non_iterated_compiled_output_matches_the_reference :: Assertion
case_non_iterated_compiled_output_matches_the_reference =
  case cmp racketNonIter gibbonNonIter of
    Nothing  -> pure ()
    Just msg -> assertFailure ("non-iterated forms must agree:\n" ++ msg)

case_iterated_compiled_output_matches_the_reference :: Assertion
case_iterated_compiled_output_matches_the_reference =
  case cmp racketIter gibbonIter of
    Nothing  -> pure ()
    Just msg -> assertFailure ("iterated forms must agree:\n" ++ msg)

-- | A stray `SIZE:` on the non-iterated form must still be a mismatch, i.e.
-- the oracle must not be weakened to accept it.
case_stray_size_on_non_iterated_output_still_fails :: Assertion
case_stray_size_on_non_iterated_output_still_fails =
  assertBool "an extra SIZE: line must not be silently ignored"
    (cmp racketNonIter ("SIZE: 1\n" ++ gibbonNonIter) /= Nothing)

case_wrong_size_on_iterated_output_still_fails :: Assertion
case_wrong_size_on_iterated_output_still_fails = do
  assertBool "SIZE: 25 vs SIZE: 1 must fail"
    (cmp racketIter (replaceFirst "SIZE: 1" "SIZE: 25" gibbonIter) /= Nothing)
  assertBool "ITERS: 9 vs ITERS: 1 must fail"
    (cmp racketIter (replaceFirst "ITERS: 1" "ITERS: 9" gibbonIter) /= Nothing)
  assertBool "a missing SIZE: line must fail"
    (cmp racketIter (deleteLine "SIZE: 1" gibbonIter) /= Nothing)

-- | Program values are still compared; the contract change cannot hide one.
case_program_value_is_still_compared :: Assertion
case_program_value_is_still_compared = do
  assertBool "a wrong value under non-iterated timing must fail"
    (cmp racketNonIter "SELFTIMED: 2.790000e-07\n43\n" /= Nothing)
  assertBool "a wrong value under iterated timing must fail"
    (cmp racketIter (replaceFirst "42" "43" gibbonIter) /= Nothing)

replaceFirst :: String -> String -> String -> String
replaceFirst needle new = unlines . go . lines
  where
    go [] = []
    go (l:ls) | l == needle = new : ls
              | otherwise   = l : go ls

deleteLine :: String -> String -> String
deleteLine needle = unlines . filter (/= needle) . lines

--------------------------------------------------------------------------------

timingOutputContractTests :: TestTree
timingOutputContractTests = $(testGroupGenerator)
