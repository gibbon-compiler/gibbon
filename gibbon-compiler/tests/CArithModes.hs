{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The three global @--c-arithmetic@ modes
-- ('Gibbon.Common.CArithMode') -- CLI parsing/propagation and generated-C
-- shape.  Companion to "IntArithmetic" (which pins interpreter semantics,
-- unaffected by this flag) and "IntArithmeticC" (generated-C correctness,
-- also mode-independent since it only ever exercises the 'ArithPortable'
-- default).  This module is the one place that exercises all three modes
-- against the actual CLI parser and against 'codegenProg', at all four
-- widths, including that a mode change never leaks into an unrelated
-- 'codegenProg' call.
module CArithModes (cArithModesTests) where

import Control.Exception (evaluate)
import Data.List (isInfixOf)
import qualified Data.Map as M

import Options.Applicative (execParserPure, defaultPrefs, info, helper, renderFailure, ParserResult(..))

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language (IntWidth(..), FunMeta(..), FunRec(..), FunInline(..))
import Gibbon.Compiler (defaultConfig, configWithArgs, int32TombstoneOption)
import qualified Gibbon.L4.Syntax as L4
import Gibbon.Passes.Codegen (codegenProg)

--------------------------------------------------------------------------------
-- 'parseCArithMode' / 'cArithModeOptionString': the pure core
--------------------------------------------------------------------------------

case_parse_portable :: Assertion
case_parse_portable = Right ArithPortable @=? parseCArithMode "portable"

case_parse_wrapv :: Assertion
case_parse_wrapv = Right ArithWrapv @=? parseCArithMode "wrapv"

case_parse_unsafe :: Assertion
case_parse_unsafe = Right ArithUnsafe @=? parseCArithMode "unsafe"

-- | Only the three exact spellings are accepted: no abbreviation, no
-- case-folding, no synonym.
case_parse_rejects_everything_else :: Assertion
case_parse_rejects_everything_else =
  mapM_ (\s -> assertBool ("expected " ++ show s ++ " to be rejected") (isLeft (parseCArithMode s)))
        ["Portable", "WRAPV", "safe", "wrap", "", "portablex", " portable", "portable "]
  where isLeft (Left _) = True
        isLeft (Right _) = False

case_parse_rejects_invalid_names_the_bad_value :: Assertion
case_parse_rejects_invalid_names_the_bad_value =
  case parseCArithMode "yolo" of
    Left msg -> assertBool ("message should quote the bad value, got: " ++ msg)
                            ("\"yolo\"" `isInfixOf` msg)
    Right m -> assertFailure ("expected rejection, got: " ++ show m)

case_option_string_roundtrips :: Assertion
case_option_string_roundtrips =
  mapM_ (\m -> Right m @=? parseCArithMode (cArithModeOptionString m))
        [ArithPortable, ArithWrapv, ArithUnsafe]

--------------------------------------------------------------------------------
-- Config default
--------------------------------------------------------------------------------

case_default_config_is_portable :: Assertion
case_default_config_is_portable = ArithPortable @=? cArithMode defaultConfig

--------------------------------------------------------------------------------
-- The real CLI parser (same technique as IntWidthsCompat's
-- case_cli_rejects_int32_flag): 'configWithArgs' end to end, not a
-- hand-rolled stand-in.
--------------------------------------------------------------------------------

parseArgv :: [String] -> ParserResult (Config, [FilePath])
parseArgv = execParserPure defaultPrefs (info (helper <*> int32TombstoneOption <*> configWithArgs) mempty)

-- | Absent entirely, the CLI must resolve to the same default as
-- 'defaultConfig' -- not a second, independently-drifting default.
case_cli_default_is_portable :: Assertion
case_cli_default_is_portable =
  case parseArgv ["--toC", "f.hs"] of
    Success (cfg, _) -> ArithPortable @=? cArithMode cfg
    other -> assertFailure ("expected a successful parse, got: " ++ show (fmap (const ()) other))

case_cli_parses_each_mode :: Assertion
case_cli_parses_each_mode =
  mapM_ check [("portable", ArithPortable), ("wrapv", ArithWrapv), ("unsafe", ArithUnsafe)]
  where
    check (spelling, expected) =
      case parseArgv ["--toC", "--c-arithmetic=" ++ spelling, "f.hs"] of
        Success (cfg, _) -> assertEqual spelling expected (cArithMode cfg)
        other -> assertFailure (spelling ++ ": expected a successful parse, got: " ++ show (fmap (const ()) other))

-- | Reject with a nonzero-exit 'Failure' (not a silent fallback to the
-- default) and an actionable message.
case_cli_rejects_invalid_c_arithmetic :: Assertion
case_cli_rejects_invalid_c_arithmetic =
  case parseArgv ["--toC", "--c-arithmetic=bogus", "f.hs"] of
    Failure failure -> do
      let (msg, _) = renderFailure failure "gibbon"
      assertBool ("expected the parseCArithMode diagnostic, got:\n" ++ msg)
                 ("invalid --c-arithmetic value \"bogus\"" `isInfixOf` msg)
    other -> assertFailure ("expected --c-arithmetic=bogus to be rejected, got: " ++ show (fmap (const ()) other))

-- | Precedence for a repeated occurrence: measured (not assumed) against the
-- real parser. A single-valued 'option' in optparse-applicative consumes
-- exactly one occurrence; a second one is left over and rejected as an
-- "Invalid option", NOT silently taken as "last wins" -- the same behaviour
-- every other valued Gibbon flag already has (e.g. a repeated --cc). This
-- test pins that measured behaviour so a future change to it (e.g. a
-- refactor onto 'many' that would silently start accepting, and
-- last-wins-ing, repeats) cannot land unnoticed.
case_cli_repeated_flag_is_rejected_not_last_wins :: Assertion
case_cli_repeated_flag_is_rejected_not_last_wins =
  case parseArgv ["--toC", "--c-arithmetic=wrapv", "--c-arithmetic=unsafe", "f.hs"] of
    Failure failure -> do
      let (msg, _) = renderFailure failure "gibbon"
      assertBool ("expected an 'Invalid option' rejection, got:\n" ++ msg)
                 ("Invalid option" `isInfixOf` msg)
    other -> assertFailure ("expected a repeated --c-arithmetic to be rejected, got: " ++ show (fmap (const ()) other))

-- | Two independent parses of different argv must not influence each other.
-- 'configWithArgs' is a pure, side-effect-free 'Options.Applicative.Parser'
-- (no top-level mutable state anywhere in its construction), so this is
-- mostly a regression guard against a future refactor accidentally routing
-- the mode through something stateful.
case_no_flag_leakage_between_invocations :: Assertion
case_no_flag_leakage_between_invocations = do
  let unsafeCfg = case parseArgv ["--toC", "--c-arithmetic=unsafe", "f.hs"] of
                    Success (cfg, _) -> cfg
                    other -> error ("unsafe parse failed: " ++ show (fmap (const ()) other))
      plainCfg  = case parseArgv ["--toC", "f.hs"] of
                    Success (cfg, _) -> cfg
                    other -> error ("plain parse failed: " ++ show (fmap (const ()) other))
  ArithUnsafe  @=? cArithMode unsafeCfg
  ArithPortable @=? cArithMode plainCfg

--------------------------------------------------------------------------------
-- Generated-C shape: a minimal one-primitive L4 probe, mirroring
-- IntArithmetic's 'arithProg'/'genC'/'probeBody' technique.
--------------------------------------------------------------------------------

-- | @out = op(x, y)@ at width @w@, both operands and the result at that
-- width -- the ordinary (non-cursor) case.
arithProbe :: IntWidth -> (IntWidth -> L4.Prim) -> L4.Prog
arithProbe w mkPrim =
  L4.Prog
    { L4.infoTable = M.empty
    , L4.symbolTable = M.empty
    , L4.fundefs =
        [ L4.FunDecl
            { L4.funName = "arith_probe"
            , L4.funArgs = [("x", L4.IntTy w), ("y", L4.IntTy w)]
            , L4.funRetTy = L4.IntTy w
            , L4.funBody =
                L4.LetPrimCallT [("out", L4.IntTy w)] (mkPrim w)
                                [L4.VarTriv "x", L4.VarTriv "y"]
                                (L4.RetValsT [L4.VarTriv "out"])
            , L4.isPure = True
            , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , L4.mainExp = Nothing
    }

-- | @out = c + n@ -- 'AddP' overloaded for cursor arithmetic (a 'CursorTy'
-- result), which 'isCursorTriv' must keep native REGARDLESS of
-- 'CArithMode'.
cursorAddProbe :: L4.Prog
cursorAddProbe =
  L4.Prog
    { L4.infoTable = M.empty
    , L4.symbolTable = M.empty
    , L4.fundefs =
        [ L4.FunDecl
            { L4.funName = "cursor_add_probe"
            , L4.funArgs = [("c", L4.CursorTy), ("n", L4.IntTy W64)]
            , L4.funRetTy = L4.CursorTy
            , L4.funBody =
                L4.LetPrimCallT [("out", L4.CursorTy)] (L4.AddP W64)
                                [L4.VarTriv "c", L4.VarTriv "n"]
                                (L4.RetValsT [L4.VarTriv "out"])
            , L4.isPure = True
            , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , L4.mainExp = Nothing
    }

-- | @out = c1 - c2@ -- 'SubP' overloaded for cursor arithmetic (an 'IntTy'
-- result but two CURSOR operands), the sibling overload to 'cursorAddProbe'.
cursorSubProbe :: L4.Prog
cursorSubProbe =
  L4.Prog
    { L4.infoTable = M.empty
    , L4.symbolTable = M.empty
    , L4.fundefs =
        [ L4.FunDecl
            { L4.funName = "cursor_sub_probe"
            , L4.funArgs = [("c1", L4.CursorTy), ("c2", L4.CursorTy)]
            , L4.funRetTy = L4.IntTy W64
            , L4.funBody =
                L4.LetPrimCallT [("out", L4.IntTy W64)] (L4.SubP W64)
                                [L4.VarTriv "c1", L4.VarTriv "c2"]
                                (L4.RetValsT [L4.VarTriv "out"])
            , L4.isPure = True
            , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , L4.mainExp = Nothing
    }

genC :: Config -> L4.Prog -> IO String
genC cfg prg = do
  s <- codegenProg cfg prg
  _ <- evaluate (length s)
  pure s

-- | The text of one function DEFINITION (not its prototype), by name.
probeBody :: String -> String -> String
probeBody name c =
  case dropWhile (not . isDefLine) (lines c) of
    [] -> error ("probeBody: no " ++ name ++ " definition in the generated C:\n" ++ c)
    (l:rest) -> unlines (l : takeWhile (/= "}") rest)
  where
    -- A definition line for `name` has the form "<ty> name(" at the start
    -- of the line, as opposed to a mid-line call or the ";"-terminated
    -- forward declaration.
    isDefLine l = (name ++ "(") `isInfixOf` l && not (';' `elem` l)

cfgWith :: CArithMode -> Config
cfgWith m = defaultConfig { cArithMode = m }

allModes :: [CArithMode]
allModes = [ArithPortable, ArithWrapv, ArithUnsafe]

allWidths :: [IntWidth]
allWidths = [W8, W16, W32, W64]

helperName :: String -> IntWidth -> String
helperName op w = "gib_" ++ op ++ "_" ++ suffix
  where suffix = case w of W8 -> "i8"; W16 -> "i16"; W32 -> "i32"; W64 -> "i64"

-- | Portable emits the deterministic helper for every op, at every width --
-- never a bare operator.
case_portable_emits_deterministic_helpers :: Assertion
case_portable_emits_deterministic_helpers =
  sequence_
    [ do c <- genC (cfgWith ArithPortable) (arithProbe w mkPrim)
         let body = probeBody "arith_probe" c
         assertBool (op ++ " " ++ show w ++ ": expected " ++ helperName op w ++ " in:\n" ++ body)
                    (helperName op w `isInfixOf` body)
    | (op, mkPrim) <- [("add", L4.AddP), ("sub", L4.SubP), ("mul", L4.MulP),
                       ("div", L4.DivP), ("mod", L4.ModP), ("exp", L4.ExpP)]
    , w <- allWidths
    ]

-- | wrapv/unsafe both emit a native operator for add/sub/mul, at every
-- width, and NEVER call the portable helper for those three ops.
case_wrapv_and_unsafe_emit_native_add_sub_mul :: Assertion
case_wrapv_and_unsafe_emit_native_add_sub_mul =
  sequence_
    [ do c <- genC (cfgWith mode) (arithProbe w mkPrim)
         let body = probeBody "arith_probe" c
         assertBool (show mode ++ " " ++ op ++ " " ++ show w ++ ": expected native '" ++ [opChar] ++ "' in:\n" ++ body)
                    (nativeOpPresent opChar body)
         assertBool (show mode ++ " " ++ op ++ " " ++ show w ++ ": must NOT call " ++ helperName op w ++ ":\n" ++ body)
                    (not (helperName op w `isInfixOf` body))
    | mode <- [ArithWrapv, ArithUnsafe]
    , (op, mkPrim, opChar) <- [("add", L4.AddP, '+'), ("sub", L4.SubP, '-'), ("mul", L4.MulP, '*')]
    , w <- allWidths
    ]
  where
    -- "out = x <op> y;" -- look for the operator between the two operand
    -- names on the assignment line, not merely anywhere in the body (the
    -- declaration line itself contains no operator to false-positive on).
    nativeOpPresent opChar body = any (\l -> opChar `elem` l && "out" `isInfixOf` l && '=' `elem` l) (lines body)

-- | Division, remainder and exponentiation are UNAFFECTED by the mode in
-- every case -- always the guarded helper, never a native '/'/'%'.
case_div_mod_exp_always_use_the_guarded_helper :: Assertion
case_div_mod_exp_always_use_the_guarded_helper =
  sequence_
    [ do c <- genC (cfgWith mode) (arithProbe w mkPrim)
         let body = probeBody "arith_probe" c
         assertBool (show mode ++ " " ++ op ++ " " ++ show w ++ ": expected " ++ helperName op w ++ " in:\n" ++ body)
                    (helperName op w `isInfixOf` body)
    | mode <- allModes
    , (op, mkPrim) <- [("div", L4.DivP), ("mod", L4.ModP), ("exp", L4.ExpP)]
    , w <- allWidths
    ]

-- | Cursor arithmetic (the AddP/SubP overload for CursorTy operands/result)
-- stays the native pointer operator in EVERY mode -- a cursor was never
-- routed through the portable helper to begin with, so there is nothing for
-- 'CArithMode' to change here. This is the direct regression guard for
-- "restore simple pointer arithmetic for cursors": it already is simple
-- pointer arithmetic, unconditionally.
case_cursor_arithmetic_is_native_in_every_mode :: Assertion
case_cursor_arithmetic_is_native_in_every_mode =
  sequence_
    [ do addC <- genC (cfgWith mode) cursorAddProbe
         let addBody = probeBody "cursor_add_probe" addC
         assertBool (show mode ++ ": cursor add expected native '+':\n" ++ addBody)
                    (any (\l -> '+' `elem` l && "out" `isInfixOf` l && '=' `elem` l) (lines addBody))
         assertBool (show mode ++ ": cursor add must not call any gib_add_i*:\n" ++ addBody)
                    (not (any (\w -> helperName "add" w `isInfixOf` addBody) allWidths))
         subC <- genC (cfgWith mode) cursorSubProbe
         let subBody = probeBody "cursor_sub_probe" subC
         assertBool (show mode ++ ": cursor sub expected native '-':\n" ++ subBody)
                    (any (\l -> '-' `elem` l && "out" `isInfixOf` l && '=' `elem` l) (lines subBody))
         assertBool (show mode ++ ": cursor sub must not call any gib_sub_i*:\n" ++ subBody)
                    (not (any (\w -> helperName "sub" w `isInfixOf` subBody) allWidths))
    | mode <- allModes
    ]

-- | Two sequential 'codegenProg' calls with DIFFERENT configs must produce
-- DIFFERENTLY-shaped output -- proving the mode is read from the 'Config'
-- passed to that specific call, not from any process-wide state left over
-- from a previous call (the "no hidden global mutable state" requirement).
case_mode_does_not_leak_across_codegen_calls :: Assertion
case_mode_does_not_leak_across_codegen_calls = do
  cPortable1 <- genC (cfgWith ArithPortable) (arithProbe W32 L4.AddP)
  cWrapv     <- genC (cfgWith ArithWrapv)    (arithProbe W32 L4.AddP)
  cPortable2 <- genC (cfgWith ArithPortable) (arithProbe W32 L4.AddP)
  let b1 = probeBody "arith_probe" cPortable1
      bw = probeBody "arith_probe" cWrapv
      b2 = probeBody "arith_probe" cPortable2
  assertBool "portable#1 should call gib_add_i32" (helperName "add" W32 `isInfixOf` b1)
  assertBool "wrapv should NOT call gib_add_i32, sandwiched between two portable calls"
             (not (helperName "add" W32 `isInfixOf` bw))
  assertBool "portable#2 (after wrapv) should still call gib_add_i32 -- no leakage"
             (helperName "add" W32 `isInfixOf` b2)

cArithModesTests :: TestTree
cArithModesTests = $(testGroupGenerator)
