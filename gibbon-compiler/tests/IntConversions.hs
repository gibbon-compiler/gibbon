{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Explicit integer-width conversions (@toInt8@ .. @toInt64@) and the
-- width-carrying @intToFloat@, from source text down to generated C.
--
-- The semantics under test: for destination width N, the conversion returns
-- the unique signed N-bit two's-complement value congruent to the operand
-- modulo 2^N.  Truncating, deterministic, never saturating, never an overflow
-- report.  See 'narrowToIntWidth', which is the single Haskell statement of
-- that rule shared by the interpreters.
--
-- Three things are checked separately here, because passing one proves
-- nothing about the others:
--
--   * L0 inference -- in particular that the DESTINATION context never
--     selects the SOURCE width (@toInt8 300@ converts an Int64 literal);
--   * L1/L2/L3 validation, including malformed IR whose annotation and
--     operand disagree;
--   * L4/codegen, that the emitted C binds the destination typedef and calls
--     the destination's RTS helper exactly once.
module IntConversions (intConversionsTests) where

import Control.Exception (ErrorCall, SomeException, evaluate, try)
import Control.Monad.Except (runExcept)
import Control.Monad.State.Strict (evalStateT)
import Data.Bits ((.&.), testBit)
import Data.List (isInfixOf)
import qualified Data.List as L
import qualified Data.Map as M
import System.Directory (getTemporaryDirectory, removeFile)
import System.FilePath ((</>))

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Compiler (Config(..), Input(..), defaultConfig, parseInput,
                        passesThroughL3, CompileState(..))
import Gibbon.DynFlags
import Gibbon.Language (FunMeta(..), FunRec(..), FunInline(..))
import Gibbon.L1.Syntax
import qualified Gibbon.L1.Interp as L1I
import qualified Gibbon.L1.Typecheck as L1
import qualified Gibbon.L2.Syntax as L2
import qualified Gibbon.L2.Typecheck as L2
import qualified Gibbon.L3.Syntax as L3
import qualified Gibbon.L3.Typecheck as L3
import qualified Gibbon.L4.Syntax as L4
import Gibbon.Passes.Codegen (codegenProg)

--------------------------------------------------------------------------------
-- Harness: source text -> production L3
--------------------------------------------------------------------------------

srcToL3With :: [GeneralFlag] -> String -> IO L3.Prog3
srcToL3With dflagOpts src = do
  tmp <- getTemporaryDirectory
  let fp = tmp </> ("gibbon-intconv-" ++ show (abs (hashStr (show dflagOpts ++ src))) ++ ".hs")
  writeFile fp src
  let dflags0 = dynflags defaultConfig
      dflags1 = foldl (flip gopt_set) dflags0 dflagOpts
      cfg = defaultConfig { dynflags = dflags1 }
  ((l0, cnt0), _fp') <- parseInput cfg Haskell fp
  removeFile fp
  evalStateT (passesThroughL3 cfg l0)
             (CompileState { cnt = cnt0, result = Nothing } :: CompileState Var)
  where
    hashStr :: String -> Int
    hashStr = foldl (\acc c -> acc * 33 + fromEnum c) 5381

forceL3 :: IO L3.Prog3 -> IO (Either String L3.Prog3)
forceL3 act = do
  r <- try (act >>= \p -> evaluate (length (sdoc p)) >> pure p)
  pure $ case r of
           Left (e :: SomeException) -> Left (show e)
           Right p -> Right p

okL3 :: String -> String -> IO L3.Prog3
okL3 lbl src = do
  r <- forceL3 (srcToL3With [Opt_Packed] src)
  case r of
    Left e  -> assertFailure (lbl ++ ": expected this to reach L3, but it failed:\n" ++ e)
    Right p -> pure p

badL3 :: String -> String -> IO String
badL3 lbl src = do
  r <- forceL3 (srcToL3With [Opt_Packed] src)
  case r of
    Left e  -> pure e
    Right p -> assertFailure (lbl ++ ": expected this to fail, but it reached L3:\n" ++ sdoc p)

--------------------------------------------------------------------------------
-- Inspecting an L3 program
--------------------------------------------------------------------------------

subExps :: L3.Exp3 -> [L3.Exp3]
subExps ex = ex : rest
  where
    rest =
      case ex of
        LetE (_,_,_,rhs) b -> subExps rhs ++ subExps b
        IfE a b c  -> subExps a ++ subExps b ++ subExps c
        MkProdE ls -> concatMap subExps ls
        ProjE _ e  -> subExps e
        CaseE sc brs -> subExps sc ++ concatMap (\(_,_,r) -> subExps r) brs
        DataConE _ _ args -> concatMap subExps args
        AppE _ _ _ args   -> concatMap subExps args
        PrimAppE _ args   -> concatMap subExps args
        TimeIt e _ _   -> subExps e
        WithArenaE _ e -> subExps e
        SpawnE _ _ args -> concatMap subExps args
        Ext e3 -> case e3 of { L3.WriteScalar _ _ rhs -> subExps rhs ; _ -> [] }
        _ -> []

l3Exps :: L3.Prog3 -> [L3.Exp3]
l3Exps Prog{fundefs,mainExp} =
  concatMap (subExps . funBody) (M.elems fundefs) ++ maybe [] (subExps . fst) mainExp

-- | Every (source, destination) pair appearing on a conversion in the program.
-- Structural, via 'intConvertWidths' -- never an equality test against a
-- particular annotated constructor.
l3ConvWidths :: L3.Prog3 -> [(IntWidth, IntWidth)]
l3ConvWidths p = [ ws | PrimAppE pr _ <- l3Exps p, Just ws <- [intConvertWidths pr] ]

-- | The source widths carried by every intToFloat in the program.
l3IntToFloatWidths :: L3.Prog3 -> [IntWidth]
l3IntToFloatWidths p =
  [ intPrimWidth a | PrimAppE (IntToFloatP a) _ <- l3Exps p ]

--------------------------------------------------------------------------------
-- The semantic rule itself
--------------------------------------------------------------------------------

-- Independent restatement of the spec, deliberately NOT calling
-- 'narrowToIntWidth', so a bug in that function cannot make its own tests pass.
specNarrow :: IntWidth -> Integer -> Integer
-- Derived bitwise rather than by modular reduction, so it is genuinely a
-- second implementation: mask off the low N bits of the (conceptually
-- infinite) two's-complement representation, then read the top retained bit as
-- the sign.  'Data.Bits' on 'Integer' uses two's-complement semantics for
-- negatives, which is exactly the representation being modelled.
specNarrow w n
  | testBit low (bits - 1) = low - modulus   -- top retained bit set => negative
  | otherwise              = low
  where
    bits = 8 * intWidthBytes w
    modulus = 2 ^ bits
    low = n .&. (modulus - 1)                -- the low N bits, in [0, 2^N)

case_narrow_matches_spec :: Assertion
case_narrow_matches_spec =
  sequence_ [ assertEqual (show (w, n)) (specNarrow w n) (narrowToIntWidth w n)
            | w <- [W8, W16, W32, W64]
            , n <- interestingInputs ]

-- | The boundary set required of every destination width, plus the
-- destination-independent values.
interestingInputs :: [Integer]
interestingInputs =
  concat [ [ lo, hi, lo - 1, hi + 1, modulus, modulus + 1, negate modulus - 1 ]
         | w <- [W8, W16, W32]
         , let bits = 8 * toInteger (intWidthBytes w)
               modulus = 2 ^ bits
               lo = negate (2 ^ (bits - 1))
               hi = 2 ^ (bits - 1) - 1 ]
  ++ [ -1, 0, 1, 2, 42 ]
  ++ [ negate (2 ^ (63 :: Int)), 2 ^ (63 :: Int) - 1 ]   -- INT64_MIN / INT64_MAX

case_narrow_is_identity_at_w64 :: Assertion
case_narrow_is_identity_at_w64 =
  sequence_ [ assertEqual (show n) n (narrowToIntWidth W64 n)
            | n <- interestingInputs
            , n >= negate (2 ^ (63::Int)), n <= 2 ^ (63::Int) - 1 ]

-- | Worked examples of two's-complement narrowing, pinned by exact value.
case_narrow_named_examples :: Assertion
case_narrow_named_examples = do
  assertEqual "toInt8 127"   127    (narrowToIntWidth W8 127)
  assertEqual "toInt8 128"   (-128) (narrowToIntWidth W8 128)
  assertEqual "toInt8 255"   (-1)   (narrowToIntWidth W8 255)
  assertEqual "toInt8 256"   0      (narrowToIntWidth W8 256)
  assertEqual "toInt8 -128"  (-128) (narrowToIntWidth W8 (-128))
  assertEqual "toInt8 -129"  127    (narrowToIntWidth W8 (-129))
  assertEqual "toInt8 300"   44     (narrowToIntWidth W8 300)
  assertEqual "W16 128->W8"  (-128) (narrowToIntWidth W8 128)
  assertEqual "W32 32768->W16" (-32768) (narrowToIntWidth W16 32768)
  assertEqual "W32 65535->W16" (-1)  (narrowToIntWidth W16 65535)
  assertEqual "W64 2147483648->W32" (-2147483648) (narrowToIntWidth W32 2147483648)
  assertEqual "W64 4294967295->W32" (-1) (narrowToIntWidth W32 4294967295)
  -- Widening sign-extends: the W8 value -1 is -1 at every wider width.
  assertEqual "widen -1" (-1) (narrowToIntWidth W16 (narrowToIntWidth W8 255))

--------------------------------------------------------------------------------
-- The L1 interpreter agrees with the rule
--------------------------------------------------------------------------------

interpConv :: IntWidth -> Integer -> IO Integer
interpConv dst n = do
  (v, _log, _s) <-
    runInterpM (L1I.applyPrim defaultRunConfig
                              (IntConvertP (IntPrimWidth W64) dst :: Prim Ty1)
                              [VInt (fromInteger n) :: Value Exp1])
               ()
  case v of
    VInt i -> pure (toInteger i)
    other  -> assertFailure ("interpreter returned a non-integer: " ++ show other)

case_l1_interp_matches_spec :: Assertion
case_l1_interp_matches_spec =
  sequence_ [ do got <- interpConv w n
                 assertEqual (show (w, n)) (specNarrow w n) got
            | w <- [W8, W16, W32, W64]
            , n <- interestingInputs
            , n >= negate (2 ^ (63::Int)), n <= 2 ^ (63::Int) - 1 ]

--------------------------------------------------------------------------------
-- L0 inference
--------------------------------------------------------------------------------

-- | All four destination names, from an unconstrained (defaulted-W64) literal.
case_all_four_destinations :: Assertion
case_all_four_destinations =
  sequence_
    [ do p <- okL3 nm ("module M where\ngibbon_main = printint (" ++ nm ++ " 7)\n")
         assertEqual (nm ++ ": source must default to W64, destination is the name's")
                     [(W64, dst)] (l3ConvWidths p)
    | (nm, dst) <- [("toInt8",W8),("toInt16",W16),("toInt32",W32),("toInt64",W64)] ]

-- | All four concrete source widths, read off the operand.
case_all_four_sources :: Assertion
case_all_four_sources =
  sequence_
    [ do let src = unlines
               [ "module M where"
               , "gibbon_main = let x :: " ++ tyname
               , "                  x = 3"
               , "              in printint (toInt8 x)" ]
         p <- okL3 tyname src
         assertEqual (tyname ++ ": source width must come from the operand")
                     [(w, W8)] (l3ConvWidths p)
    | (tyname, w) <- [("Int8",W8),("Int16",W16),("Int32",W32),("Int64",W64)] ]

-- | @toInt8 300@ is a conversion OF AN INT64 LITERAL.  If the destination were
-- pushed inward the literal would be typed Int8 and rejected as out of range,
-- which is exactly the bug this guards.
case_destination_never_selects_source :: Assertion
case_destination_never_selects_source = do
  p <- okL3 "wide-literal" "module M where\ngibbon_main = printint (toInt8 300)\n"
  assertEqual "source stays W64" [(W64, W8)] (l3ConvWidths p)

-- | Even when the RESULT is demanded at the destination width, the source is
-- still the operand's own.
case_destination_context_does_not_leak_inward :: Assertion
case_destination_context_does_not_leak_inward = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let y :: Int8"
                    , "                  y = toInt8 300"
                    , "              in printint y" ]
  p <- okL3 "annotated-result" src
  assertEqual "source stays W64" [(W64, W8)] (l3ConvWidths p)

-- | Unconstrained homogeneous arithmetic resolves at W64 first, and the
-- conversion applies to its result.
case_unconstrained_arithmetic_source :: Assertion
case_unconstrained_arithmetic_source = do
  p <- okL3 "arith" "module M where\ngibbon_main = printint (toInt8 (200 + 100))\n"
  assertEqual "source is the arithmetic's own W64" [(W64, W8)] (l3ConvWidths p)

case_negative_literal_source :: Assertion
case_negative_literal_source = do
  p <- okL3 "negative" "module M where\ngibbon_main = printint (toInt8 (0 - 129))\n"
  assertEqual "source stays W64" [(W64, W8)] (l3ConvWidths p)

-- | A function parameter is a metavariable when the body is checked; it must
-- be constrained to an integer rather than rejected.
case_metavariable_source :: Assertion
case_metavariable_source = do
  let src = unlines [ "module M where"
                    , "narrow x = toInt8 x"
                    , "gibbon_main = printint (narrow 300)" ]
  p <- okL3 "metavar" src
  assertEqual "unconstrained metavariable defaults to W64" [(W64, W8)] (l3ConvWidths p)

-- | A rigid narrow parameter supplies its own width.
case_function_argument_source :: Assertion
case_function_argument_source = do
  let src = unlines [ "module M where"
                    , "narrow :: Int16 -> Int8"
                    , "narrow x = toInt8 x"
                    , "gibbon_main = let y :: Int16"
                    , "                  y = 300"
                    , "              in printint (narrow y)" ]
  p <- okL3 "rigid-arg" src
  assertEqual "source is Int16" [(W16, W8)] (l3ConvWidths p)

case_same_width_conversion :: Assertion
case_same_width_conversion = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let y :: Int16"
                    , "                  y = 300"
                    , "              in printint (toInt16 y)" ]
  p <- okL3 "same-width" src
  assertEqual "W16 -> W16 is legal and value-preserving" [(W16, W16)] (l3ConvWidths p)

case_nested_conversions :: Assertion
case_nested_conversions = do
  p <- okL3 "nested" "module M where\ngibbon_main = printint (toInt16 (toInt8 255))\n"
  assertEqual "inner W64->W8, outer W8->W16"
              [(W64, W8), (W8, W16)] (L.sortOn snd (l3ConvWidths p))

-- | Assigning a narrow conversion where a wider type is required is an error:
-- no implicit widening in an assignment context.
case_destination_mismatch_rejected :: Assertion
case_destination_mismatch_rejected = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let x :: Int16"
                    , "                  x = toInt8 5"
                    , "              in printint x" ]
  e <- badL3 "mismatch" src
  assertBool ("expected a width mismatch, got:\n" ++ e)
             ("IntTy W8" `isInfixOf` e && "IntTy W16" `isInfixOf` e)

case_non_integer_operand_rejected :: Assertion
case_non_integer_operand_rejected = do
  e <- badL3 "bool" "module M where\ngibbon_main = printint (toInt8 True)\n"
  assertBool ("expected a typed diagnostic, got:\n" ++ e)
             ("toInt8 expects an integer operand" `isInfixOf` e)

case_float_operand_rejected :: Assertion
case_float_operand_rejected = do
  e <- badL3 "float" "module M where\ngibbon_main = printint (toInt8 (1.5 .+. 1.0))\n"
  assertBool ("expected a typed diagnostic, got:\n" ++ e)
             ("toInt8 expects an integer operand" `isInfixOf` e)

-- | Literal range checking still applies to the literal's OWN source width.
case_explicit_narrow_literal_still_range_checked :: Assertion
case_explicit_narrow_literal_still_range_checked = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let x :: Int8"
                    , "                  x = 128"
                    , "              in printint x" ]
  e <- badL3 "range" src
  assertBool ("expected a literal range error, got:\n" ++ e)
             ("out of range for Int8" `isInfixOf` e)

-- | Arithmetic stays homogeneous even with conversions nearby: mixing an
-- Int8 conversion result with an Int64 operand is still a type error.
case_mixed_width_arithmetic_still_rejected :: Assertion
case_mixed_width_arithmetic_still_rejected = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let a :: Int8"
                    , "                  a = toInt8 5"
                    , "                  b :: Int64"
                    , "                  b = 5"
                    , "              in printint (a + b)" ]
  e <- badL3 "mixed" src
  assertBool ("expected a mixed-width arithmetic error, got:\n" ++ e)
             ("Integer widths do not match" `isInfixOf` e
              || "IntTy W8" `isInfixOf` e)

--------------------------------------------------------------------------------
-- intToFloat carries its source width
--------------------------------------------------------------------------------

case_int_to_float_all_widths :: Assertion
case_int_to_float_all_widths =
  sequence_
    [ do let src = unlines
               [ "module M where"
               , "gibbon_main = let x :: " ++ tyname
               , "                  x = 3"
               , "              in printfloat (intToFloat x)" ]
         p <- okL3 tyname src
         assertEqual (tyname ++ ": intToFloat must record its source width")
                     [w] (l3IntToFloatWidths p)
    | (tyname, w) <- [("Int8",W8),("Int16",W16),("Int32",W32),("Int64",W64)] ]

case_int_to_float_literal_defaults_w64 :: Assertion
case_int_to_float_literal_defaults_w64 = do
  p <- okL3 "itof-lit" "module M where\ngibbon_main = printfloat (intToFloat 3)\n"
  assertEqual "unconstrained literal defaults to W64" [W64] (l3IntToFloatWidths p)

case_int_to_float_rejects_non_integer :: Assertion
case_int_to_float_rejects_non_integer = do
  e <- badL3 "itof-bool" "module M where\ngibbon_main = printfloat (intToFloat True)\n"
  assertBool ("expected a typed diagnostic, got:\n" ++ e)
             ("intToFloat expects an integer operand" `isInfixOf` e)

-- | floatToInt stays Float -> Int64 only.  Demanding a narrow result must be a
-- type error, not an inferred narrow destination.
case_float_to_int_is_w64_only :: Assertion
case_float_to_int_is_w64_only = do
  let src = unlines [ "module M where"
                    , "gibbon_main = let x :: Int8"
                    , "                  x = floatToInt 1.5"
                    , "              in printint x" ]
  e <- badL3 "ftoi" src
  assertBool ("expected floatToInt to stay W64, got:\n" ++ e)
             ("IntTy W8" `isInfixOf` e || "IntTy W64" `isInfixOf` e)

--------------------------------------------------------------------------------
-- Unresolved annotations must not cross L0 -> L1
--------------------------------------------------------------------------------

case_unresolved_conversion_source_is_an_ice :: Assertion
case_unresolved_conversion_source_is_an_ice = do
  r <- try (evaluate (intPrimWidth IntPrimUnresolved))
  case r of
    Left (e :: ErrorCall) ->
      assertBool ("expected the unresolved-width ICE, got: " ++ show e)
                 ("unresolved width" `isInfixOf` show e)
    Right w -> assertFailure ("an unresolved annotation silently produced " ++ show w)

-- | An unresolved SOURCE is reported by 'intPrimAnnOf', which is what
-- 'toL1Prim' consults, so the L0 -> L1 ICE covers conversions automatically.
case_conversion_is_width_sensitive :: Assertion
case_conversion_is_width_sensitive = do
  let pr = IntConvertP IntPrimUnresolved W8 :: Prim Ty1
  assertBool "conversions must be width-sensitive" (isWidthSensitivePrim pr)
  assertEqual "the unresolved source must be visible to toL1Prim"
              (Just IntPrimUnresolved) (intPrimAnnOf pr)
  assertBool "intToFloat must be width-sensitive"
             (isWidthSensitivePrim (IntToFloatP IntPrimUnresolved :: Prim Ty1))

-- | 'setIntPrimAnn' replaces only the source; the destination is fixed.
case_set_ann_preserves_destination :: Assertion
case_set_ann_preserves_destination =
  assertEqual "destination survives annotation normalisation"
              (IntConvertP (IntPrimWidth W16) W8 :: Prim Ty1)
              (setIntPrimWidth W16 (IntConvertP IntPrimUnresolved W8))

--------------------------------------------------------------------------------
-- Malformed IR is rejected at L1, L2 and L3
--------------------------------------------------------------------------------

-- A program whose conversion claims source @annSrc@ but is applied to a
-- literal of width @actualSrc@.
malformedProg :: IntWidth -> IntWidth -> IntWidth -> Prog1
malformedProg annSrc actualSrc dst =
  Prog { ddefs = M.empty, fundefs = M.empty
       , mainExp = Just ( PrimAppE (IntConvertP (IntPrimWidth annSrc) dst)
                                   [LitE (LitWidth actualSrc) 1]
                        , IntTy dst ) }

wellFormedProg :: IntWidth -> IntWidth -> Prog1
wellFormedProg src dst =
  Prog { ddefs = M.empty, fundefs = M.empty
       , mainExp = Just ( PrimAppE (IntConvertP (IntPrimWidth src) dst)
                                   [LitE (LitWidth src) 1]
                        , IntTy dst ) }

-- | Run L1's typechecker and report whether it accepted the program.  'tcProg'
-- reports errors by raising, so force the result inside 'try'.
tcL1 :: Prog1 -> IO (Either String Prog1)
tcL1 p = do
  r <- try (evaluate (fst (defaultRunPassM (L1.tcProg p)))
              >>= \q -> evaluate (length (sdoc q)) >> pure q)
  pure $ case r of
           Left (e :: SomeException) -> Left (show e)
           Right q -> Right q

case_l1_accepts_well_formed_conversions :: Assertion
case_l1_accepts_well_formed_conversions =
  sequence_ [ do r <- tcL1 (wellFormedProg s d)
                 case r of
                   Right{} -> pure ()
                   Left e -> assertFailure (show (s,d) ++ ": " ++ e)
            | s <- [W8,W16,W32,W64], d <- [W8,W16,W32,W64] ]

case_l1_rejects_annotation_operand_mismatch :: Assertion
case_l1_rejects_annotation_operand_mismatch = do
  r <- tcL1 (malformedProg W8 W64 W8)
  case r of
    Left _  -> pure ()
    Right _ -> assertFailure "L1 accepted a conversion whose operand width contradicts its annotation"

-- | The wrong RESULT width must also be caught: claiming the result is the
-- source width rather than the destination.
case_l1_rejects_wrong_result_width :: Assertion
case_l1_rejects_wrong_result_width =
  do let p = Prog { ddefs = M.empty, fundefs = M.empty
                  , mainExp = Just ( PrimAppE (IntConvertP (IntPrimWidth W64) W8)
                                              [LitE (LitWidth W64) 1]
                                   , IntTy W64 ) }
     r <- tcL1 p
     case r of
       Left _  -> pure ()
       Right _ -> assertFailure "L1 accepted a conversion whose result width is the source, not the destination"

-- | primArgsTy/primRetTy are what L2 and L3 validate against, so check them
-- directly for all 16 combinations rather than only through one level.
case_prim_types_for_all_combinations :: Assertion
case_prim_types_for_all_combinations =
  sequence_ [ do assertEqual (show (s,d) ++ " argument")
                            [IntTy s :: Ty1]
                            (primArgsTy (IntConvertP (IntPrimWidth s) d))
                 assertEqual (show (s,d) ++ " result")
                            (IntTy d :: Ty1)
                            (primRetTy (IntConvertP (IntPrimWidth s) d))
            | s <- [W8,W16,W32,W64], d <- [W8,W16,W32,W64] ]

case_int_to_float_prim_types :: Assertion
case_int_to_float_prim_types =
  sequence_ [ do assertEqual (show w ++ " argument")
                            [IntTy w :: Ty1] (primArgsTy (IntToFloatP (IntPrimWidth w)))
                 assertEqual (show w ++ " result")
                            (FloatTy :: Ty1) (primRetTy (IntToFloatP (IntPrimWidth w)))
            | w <- [W8,W16,W32,W64] ]

case_float_to_int_prim_types :: Assertion
case_float_to_int_prim_types = do
  assertEqual "argument" [FloatTy :: Ty1] (primArgsTy FloatToIntP)
  assertEqual "result is W64 only" (IntTy W64 :: Ty1) (primRetTy FloatToIntP)

-- | The whole production pipeline, all 16 combinations, reaching a
-- typechecked L3 with both widths intact.
case_all_16_combinations_reach_l3 :: Assertion
case_all_16_combinations_reach_l3 =
  sequence_
    [ do let src = unlines
               [ "module M where"
               , "gibbon_main = let x :: " ++ sname
               , "                  x = 1"
               , "                  y :: " ++ dname
               , "                  y = " ++ conv ++ " x"
               , "              in printint y" ]
         p <- okL3 (sname ++ "->" ++ dname) src
         assertEqual (sname ++ "->" ++ dname ++ ": both widths must survive to L3")
                     [(s, d)] (l3ConvWidths p)
    | (sname, s) <- [("Int8",W8),("Int16",W16),("Int32",W32),("Int64",W64)]
    , (dname, d, conv) <- [ ("Int8",W8,"toInt8"), ("Int16",W16,"toInt16")
                          , ("Int32",W32,"toInt32"), ("Int64",W64,"toInt64") ] ]

--------------------------------------------------------------------------------
-- L4 / codegen
--------------------------------------------------------------------------------

convProg :: IntWidth -> IntWidth -> L4.Prog
convProg src dst =
  L4.Prog
    { L4.infoTable = M.empty
    , L4.symbolTable = M.empty
    , L4.fundefs =
        [ L4.FunDecl
            { L4.funName = "conv_probe"
            , L4.funArgs = [("x", L4.IntTy src)]
            , L4.funRetTy = L4.IntTy dst
            , L4.funBody =
                L4.LetPrimCallT [("out", L4.IntTy dst)] (L4.IntConvertP src dst)
                                [L4.VarTriv "x"]
                                (L4.RetValsT [L4.VarTriv "out"])
            , L4.isPure = True
            , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , L4.mainExp = Nothing
    }

probeFun :: L4.Prog -> L4.FunDecl
probeFun p =
  case L4.fundefs p of
    (f:_) -> f
    []    -> error "probeFun: no functions in the probe program"

genC :: L4.Prog -> IO (Either ErrorCall String)
genC prg = try (codegenProg defaultConfig prg >>= \s -> evaluate (length s) >> pure s)

genC' :: L4.Prog -> IO String
genC' prg = do
  r <- genC prg
  case r of
    Right s -> pure s
    Left e  -> assertFailure ("codegenProg unexpectedly failed: " ++ show e)

destHelper :: IntWidth -> String
destHelper W8  = "gib_int_to_int8"
destHelper W16 = "gib_int_to_int16"
destHelper W32 = "gib_int_to_int32"
destHelper W64 = "gib_int_to_int64"

destTypedef :: IntWidth -> String
destTypedef W8  = "GibInt8"
destTypedef W16 = "GibInt16"
destTypedef W32 = "GibInt32"
destTypedef W64 = "GibInt64"

-- | Emitted C for all 16 combinations: the destination typedef binds the
-- result, the destination's helper is called exactly once, and the operand
-- appears exactly once inside it.
case_codegen_emits_destination_helper_and_type :: Assertion
case_codegen_emits_destination_helper_and_type =
  sequence_
    [ do c <- genC' (convProg s d)
         let body = probeBody c
         assertBool (show (s,d) ++ ": result must bind " ++ destTypedef d
                       ++ "\n" ++ body)
                    ((destTypedef d ++ " out") `isInfixOf` body)
         assertEqual (show (s,d) ++ ": exactly one helper call\n" ++ body)
                     1 (countOccurrences (destHelper d ++ "(") body)
         -- The operand appears exactly once in the function's own body (past
         -- its parameter list), so the conversion cannot be re-evaluating it.
         assertEqual (show (s,d) ++ ": operand evaluated once\n" ++ body)
                     1 (countTokens "x" (dropWhile (/= '{') body))
         -- The operand is widened through the exact source typedef, never
         -- through the infrastructure GibInt.
         assertBool (show (s,d) ++ ": operand must be cast at its source width\n" ++ body)
                    (("(" ++ destTypedef s ++ ")") `isInfixOf` body)
         assertBool (show (s,d) ++ ": must not route the result through GibInt\n" ++ body)
                    (not ("GibInt out" `isInfixOf` body))
    | s <- [W8,W16,W32,W64], d <- [W8,W16,W32,W64] ]

-- | The text of the @conv_probe@ FUNCTION DEFINITION (not its prototype):
-- from its opening line down to the closing brace in column 0.
probeBody :: String -> String
probeBody c =
  case dropWhile (not . isDefLine) (lines c) of
    [] -> error "probeBody: no conv_probe definition in the generated C"
    (l:rest) -> unlines (l : takeWhile (/= "}") rest)
  where
    isDefLine l = "conv_probe(" `isInfixOf` l && not (";" `L.isSuffixOf` trim l)
    trim = L.dropWhileEnd (== ' ')

countOccurrences :: String -> String -> Int
countOccurrences needle hay = length (filter (needle `L.isPrefixOf`) (L.tails hay))

-- | Occurrences of an identifier as a whole C token.
countTokens :: String -> String -> Int
countTokens tok hay = length (filter (== tok) (cTokens hay))
  where
    cTokens [] = []
    cTokens cs@(c:rest)
      | isIdentChar c = let (w, cs') = span isIdentChar cs in w : cTokens cs'
      | otherwise     = cTokens rest
    isIdentChar c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_")

-- | A conversion whose L4 destination disagrees with the type of the variable
-- it binds is a codegen error, not silently emitted.
case_codegen_rejects_destination_mismatch :: Assertion
case_codegen_rejects_destination_mismatch = do
  let bad = (convProg W64 W8)
        { L4.fundefs =
            [ (probeFun (convProg W64 W8))
                { L4.funRetTy = L4.IntTy W16
                , L4.funBody =
                    L4.LetPrimCallT [("out", L4.IntTy W16)] (L4.IntConvertP W64 W8)
                                    [L4.VarTriv "x"]
                                    (L4.RetValsT [L4.VarTriv "out"])
                } ] }
  r <- genC bad
  case r of
    Left _  -> pure ()
    Right c -> assertFailure ("codegen accepted a destination/binder mismatch:\n" ++ c)

intConversionsTests :: TestTree
intConversionsTests = $(testGroupGenerator)
