{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deterministic integer arithmetic semantics for @Int8@\/@Int16@\/@Int32@\/@Int64@.
--
-- = The semantics table
--
-- For a width @N@ (8, 16, 32 or 64) let @modulus = 2^N@ and let @wrap x@ be
-- the unique signed @N@-bit two's-complement value congruent to @x@ modulo
-- @modulus@ -- that is, 'narrowToIntWidth'.  Then, for operands already
-- normalized to width @N@:
--
-- +-----------------+--------------------------------------------------------+
-- | @a + b@         | @wrap (a + b)@                                         |
-- +-----------------+--------------------------------------------------------+
-- | @a - b@         | @wrap (a - b)@                                         |
-- +-----------------+--------------------------------------------------------+
-- | @a * b@         | @wrap (a * b)@                                         |
-- +-----------------+--------------------------------------------------------+
-- | @negate a@      | @wrap (0 - a)@; in particular @negate MIN == MIN@      |
-- +-----------------+--------------------------------------------------------+
-- | @a ^ b@, @b>=0@ | repeated modular multiplication: @wrap (a^b)@          |
-- +-----------------+--------------------------------------------------------+
-- | @a ^ b@, @b<0@  | @wrap 1@ (total, never an exception -- see below)      |
-- +-----------------+--------------------------------------------------------+
-- | @a \/ b@        | truncates toward zero (C @\/@, Haskell @quot@), then   |
-- |                 | @wrap@; so @MIN \/ -1 == MIN@                          |
-- +-----------------+--------------------------------------------------------+
-- | @a % b@         | sign of the DIVIDEND (C @%@, Haskell @rem@), then      |
-- |                 | @wrap@; so @MIN % -1 == 0@                             |
-- +-----------------+--------------------------------------------------------+
-- | @a \/ 0@, @a%0@ | deterministic runtime diagnostic, never C undefined    |
-- |                 | behaviour and never an uncontrolled host exception     |
-- +-----------------+--------------------------------------------------------+
--
-- Every one of the eight rows must hold identically in: the L1\/L2
-- interpreter, the L4 interpreter, scalar generated C, SIMD generated C, and
-- under GCC and Clang at @-O0@, @-O2@ and @-O3@.  This module pins the
-- interpreter half; 'IntArithmeticC' pins the generated-C half.
--
-- = Why the negative-exponent row reads the way it does
--
-- It is not a free choice, it is the least-bad reconciliation of two
-- pre-existing behaviours that did not agree.  Measured before any change:
--
--   * the L1 interpreter used Haskell @(^)@, which /throws/ @Negative
--     exponent@ -- an uncontrolled exception, not a value;
--   * the C helper @gib_expll@ returned @1@ for a negative exponent for every
--     base except @2@, where it evaluated @1 << pow@ with a negative shift
--     count, which is undefined behaviour (it returned @-2147483648@ here).
--
-- So @1@ is what compiled code already produced in the general case, and it is
-- total.  It is adopted for all bases and all widths, and the interpreter is
-- moved onto it.  @0^0 == 1@, which both sides already agreed on.
module IntArithmetic (intArithmeticTests) where

import Control.Exception (ErrorCall, SomeException, evaluate, try)
import Data.List (isInfixOf)
import qualified Data.List as L
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Compiler (defaultConfig)
import Gibbon.L1.Syntax as L1
import Gibbon.L1.Interp ()
import qualified Gibbon.L4.Syntax as L4
import Gibbon.Passes.Codegen (codegenProg)

--------------------------------------------------------------------------------
-- Driving the interpreter
--------------------------------------------------------------------------------

-- | A whole program whose main expression is one width-annotated binary
-- primitive applied to two literals of that same width.
binProg :: IntWidth -> (IntPrimAnn -> Prim Ty1) -> Integer -> Integer -> Prog1
binProg w mkPrim a b =
  Prog emptyDD M.empty
       (Just ( PrimAppE (mkPrim (IntPrimWidth w))
                        [LitE (LitWidth w) a, LitE (LitWidth w) b]
             , IntTy w ))

-- | Interpret and render.  The interpreter's value type is width-erased
-- ('VInt Int'), so the ANNOTATION is what has to carry the width; that is
-- exactly what these tests are checking.
runBin :: IntWidth -> (IntPrimAnn -> Prim Ty1) -> Integer -> Integer -> String
runBin w mkPrim a b =
  gInterpNoLogs () (RunConfig 1 1 dbgLvl False) (binProg w mkPrim a b)

-- | Assert one row of the table.
expectBin :: String -> IntWidth -> (IntPrimAnn -> Prim Ty1)
          -> Integer -> Integer -> Integer -> Assertion
expectBin lbl w mkPrim a b expected =
  assertEqual (lbl ++ " " ++ show (w, a, b)) (show expected) (runBin w mkPrim a b)

-- | Assert that evaluation fails with a controlled, recognisable diagnostic
-- rather than succeeding or dying with a raw host arithmetic exception.
expectDiagnostic :: String -> [String] -> String -> Assertion
expectDiagnostic lbl needles s = do
  -- Force the whole string: 'evaluate' alone would stop at WHNF and miss an
  -- exception buried in the tail.
  r <- try (evaluate (length s) >> pure s) :: IO (Either SomeException String)
  case r of
    Right v -> assertFailure (lbl ++ ": expected a runtime diagnostic, got " ++ show v)
    Left e ->
      let msg = show e
      in assertBool (lbl ++ ": diagnostic did not mention " ++ show needles
                         ++ "; it was: " ++ msg)
                    (any (`isInfixOf` msg) needles)

-- | Signed range endpoints, derived here independently of 'intWidthRange' so a
-- bug in that function cannot make its own tests pass.
loOf, hiOf :: IntWidth -> Integer
loOf w = negate (2 ^ (8 * toInteger (intWidthBytes w) - 1))
hiOf w = 2 ^ (8 * toInteger (intWidthBytes w) - 1) - 1

allWidths :: [IntWidth]
allWidths = [W8, W16, W32, W64]

--------------------------------------------------------------------------------
-- Add / subtract / multiply / negate: the wraparound boundary
--------------------------------------------------------------------------------

case_wrap_max_plus_one :: Assertion
case_wrap_max_plus_one =
  sequence_ [ expectBin "MAX+1" w AddP (hiOf w) 1 (loOf w) | w <- allWidths ]

case_wrap_min_minus_one :: Assertion
case_wrap_min_minus_one =
  sequence_ [ expectBin "MIN-1" w SubP (loOf w) 1 (hiOf w) | w <- allWidths ]

-- Operand order matters for subtraction, so pin the mirrored case too.
case_wrap_sub_operand_order :: Assertion
case_wrap_sub_operand_order =
  sequence_ [ expectBin "1-MIN" w SubP 1 (loOf w) (loOf w + 1) | w <- allWidths ]

case_wrap_min_times_neg_one :: Assertion
case_wrap_min_times_neg_one =
  sequence_ [ expectBin "MIN*-1" w MulP (loOf w) (-1) (loOf w) | w <- allWidths ]

case_wrap_max_times_two :: Assertion
case_wrap_max_times_two =
  sequence_ [ expectBin "MAX*2" w MulP (hiOf w) 2 (-2) | w <- allWidths ]

-- Negation is represented as @0 - a@, so it follows subtraction.
case_wrap_negate_min :: Assertion
case_wrap_negate_min =
  sequence_ [ expectBin "negate MIN" w SubP 0 (loOf w) (loOf w) | w <- allWidths ]

case_wrap_identities :: Assertion
case_wrap_identities = sequence_ $ concat
  [ [ expectBin "a+0" w AddP (hiOf w) 0 (hiOf w)
    , expectBin "a-0" w SubP (loOf w) 0 (loOf w)
    , expectBin "a*1" w MulP (loOf w) 1 (loOf w)
    , expectBin "a*0" w MulP (loOf w) 0 0
    , expectBin "0-0" w SubP 0 0 0
    ]
  | w <- allWidths ]

-- Both signs, and a product that overflows the lane in each direction.
case_wrap_multiply_signs :: Assertion
case_wrap_multiply_signs = sequence_ $ concat
  [ [ expectBin "neg*neg" w MulP (-3) (-4) 12
    , expectBin "neg*pos" w MulP (-3) 4 (-12)
    , expectBin "pos*neg" w MulP 3 (-4) (-12)
    , expectBin "MIN*MIN" w MulP (loOf w) (loOf w) (wrapRef w (loOf w * loOf w))
    , expectBin "MAX*MAX" w MulP (hiOf w) (hiOf w) (wrapRef w (hiOf w * hiOf w))
    ]
  | w <- allWidths ]

-- | Modular power oracle: reduce at every step so the intermediate never
-- grows.  Written independently of the implementation; 'case_exp_oracles_agree'
-- checks it against the direct @b^e@ oracle wherever the direct one is
-- affordable, so neither can drift alone.
powRef :: IntWidth -> Integer -> Integer -> Integer
powRef w b e
  | e < 0 = wrapRef w 1
  | otherwise = wrapRef w (go (wrapRef w b) e 1)
  where
    modulus = 2 ^ (8 * toInteger (intWidthBytes w))
    go _ 0 acc = acc
    go base k acc =
      let acc' = if odd k then (acc * base) `mod` modulus else acc
      in go ((base * base) `mod` modulus) (k `div` 2) acc'

-- An oracle derived from the definition, not from 'narrowToIntWidth'.
wrapRef :: IntWidth -> Integer -> Integer
wrapRef w n =
  let bits = 8 * toInteger (intWidthBytes w)
      m = n `mod` (2 ^ bits)
  in if m < 2 ^ (bits - 1) then m else m - 2 ^ bits

--------------------------------------------------------------------------------
-- Division and remainder: sign matrix and the two singular cases
--------------------------------------------------------------------------------

-- C's `/` truncates toward zero and `%` takes the dividend's sign.  Haskell's
-- `div`/`mod` do NOT: they floor, giving -3 and 2 for (-7,3).  This matrix is
-- what stops `div`/`mod` being substituted by accident.
case_div_rem_sign_matrix :: Assertion
case_div_rem_sign_matrix = sequence_ $ concat
  [ [ expectBin "7/3"     w DivP   7    3    2
    , expectBin "7%3"     w ModP   7    3    1
    , expectBin "-7/3"    w DivP (-7)   3  (-2)
    , expectBin "-7%3"    w ModP (-7)   3  (-1)
    , expectBin "7/-3"    w DivP   7  (-3) (-2)
    , expectBin "7%-3"    w ModP   7  (-3)   1
    , expectBin "-7/-3"   w DivP (-7) (-3)   2
    , expectBin "-7%-3"   w ModP (-7) (-3) (-1)
    ]
  | w <- allWidths ]

case_div_min_by_neg_one :: Assertion
case_div_min_by_neg_one =
  sequence_ [ expectBin "MIN/-1" w DivP (loOf w) (-1) (loOf w) | w <- allWidths ]

case_rem_min_by_neg_one :: Assertion
case_rem_min_by_neg_one =
  sequence_ [ expectBin "MIN%-1" w ModP (loOf w) (-1) 0 | w <- allWidths ]

-- The diagnostic must be one WE raise, naming the operation, not whatever the
-- host runtime happens to throw.  Haskell's own "divide by zero" would satisfy
-- a laxer needle while leaving the semantics uncontrolled, so it is not
-- accepted here.
case_div_by_zero_diagnostic :: Assertion
case_div_by_zero_diagnostic =
  sequence_ [ expectDiagnostic ("div by zero " ++ show w)
                               ["Gibbon: integer division by zero"]
                               (runBin w DivP 7 0)
            | w <- allWidths ]

case_rem_by_zero_diagnostic :: Assertion
case_rem_by_zero_diagnostic =
  sequence_ [ expectDiagnostic ("rem by zero " ++ show w)
                               ["Gibbon: integer remainder by zero"]
                               (runBin w ModP 7 0)
            | w <- allWidths ]

--------------------------------------------------------------------------------
-- Exponentiation
--------------------------------------------------------------------------------

case_exp_zero_exponent :: Assertion
case_exp_zero_exponent = sequence_ $ concat
  [ [ expectBin "a^0" w ExpP (loOf w) 0 1
    , expectBin "0^0" w ExpP 0 0 1
    ]
  | w <- allWidths ]

case_exp_small :: Assertion
case_exp_small = sequence_ $ concat
  [ [ expectBin "3^3" w ExpP 3 3 27
    , expectBin "(-3)^3" w ExpP (-3) 3 (-27)
    , expectBin "(-3)^2" w ExpP (-3) 2 9
    ]
  | w <- allWidths ]

-- Base 2 is the case the old C helper special-cased with a shift, and where it
-- was wrong even at W64: gib_expll(2,31) returned -2147483648 and
-- gib_expll(2,40) returned 256.
case_exp_powers_of_two :: Assertion
case_exp_powers_of_two = sequence_
  [ expectBin "2^k" w ExpP 2 k (wrapRef w (2 ^ k))
  | w <- allWidths, k <- [0, 1, 7, 8, 15, 16, 30, 31, 32, 40, 62, 63, 64, 65] ]

case_exp_wraps_repeatedly :: Assertion
case_exp_wraps_repeatedly = sequence_
  [ expectBin "b^e wraps" w ExpP b e (wrapRef w (b ^ e))
  | w <- allWidths
  , (b, e) <- [(3, 20), (7, 11), (-3, 21), (-7, 10), (10, 19), (127, 9)] ]

case_exp_negative_exponent :: Assertion
case_exp_negative_exponent = sequence_ $ concat
  [ [ expectBin "3^-1" w ExpP 3 (-1) 1
    , expectBin "2^-1" w ExpP 2 (-1) 1
    , expectBin "0^-5" w ExpP 0 (-5) 1
    ]
  | w <- allWidths ]

-- A large exponent must terminate promptly.  The old helper looped `pow`
-- times, so this would have run for ~2^40 iterations.
case_exp_large_exponent_terminates :: Assertion
case_exp_large_exponent_terminates =
  sequence_ [ expectBin "3^bigE" w ExpP 3 e (powRef w 3 e)
            | w <- allWidths, e <- [1099511627776, 4294967296] ]

-- The two oracles must agree wherever both are affordable, so a bug in the
-- modular one cannot hide behind the huge-exponent test.
case_exp_oracles_agree :: Assertion
case_exp_oracles_agree = sequence_
  [ assertEqual (show (w, b, e)) (wrapRef w (b ^ e)) (powRef w b e)
  | w <- allWidths, b <- [0, 1, 2, 3, -3, 7, -7, 10, 127, -128], e <- [0 .. 40 :: Integer] ]

--------------------------------------------------------------------------------
-- L4 / codegen: every width-annotated integer primitive must reach its own
-- deterministic RTS helper, and nothing else may.
--------------------------------------------------------------------------------

-- | A one-primitive probe function: @out = op(x, y)@ at the given width.
arithProg :: IntWidth -> (IntWidth -> L4.Prim) -> L4.Prog
arithProg w mkPrim = arithProgWith w mkPrim (L4.IntTy w)

-- | As 'arithProg', but the result binding's type is chosen by the caller, so
-- a deliberately malformed program can be built.
arithProgWith :: IntWidth -> (IntWidth -> L4.Prim) -> L4.Ty -> L4.Prog
arithProgWith w mkPrim outTy =
  L4.Prog
    { L4.infoTable = M.empty
    , L4.symbolTable = M.empty
    , L4.fundefs =
        [ L4.FunDecl
            { L4.funName = "arith_probe"
            , L4.funArgs = [("x", L4.IntTy w), ("y", L4.IntTy w)]
            , L4.funRetTy = outTy
            , L4.funBody =
                L4.LetPrimCallT [("out", outTy)] (mkPrim w)
                                [L4.VarTriv "x", L4.VarTriv "y"]
                                (L4.RetValsT [L4.VarTriv "out"])
            , L4.isPure = True
            , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , L4.mainExp = Nothing
    }

genC :: L4.Prog -> IO (Either ErrorCall String)
genC prg = try (codegenProg defaultConfig prg >>= \s -> evaluate (length s) >> pure s)

genC' :: L4.Prog -> IO String
genC' prg = do
  r <- genC prg
  case r of
    Right s -> pure s
    Left e  -> assertFailure ("codegenProg unexpectedly failed: " ++ show e)

-- | The text of the @arith_probe@ FUNCTION DEFINITION, not its prototype.
probeBody :: String -> String
probeBody c =
  case dropWhile (not . isDefLine) (lines c) of
    [] -> error "probeBody: no arith_probe definition in the generated C"
    (l:rest) -> unlines (l : takeWhile (/= "}") rest)
  where
    isDefLine l = "arith_probe(" `isInfixOf` l && not (";" `L.isSuffixOf` trim l)
    trim = L.dropWhileEnd (== ' ')

countOccurrences :: String -> String -> Int
countOccurrences needle hay = length (filter (needle `L.isPrefixOf`) (L.tails hay))

countTokens :: String -> String -> Int
countTokens tok hay = length (filter (== tok) (cTokens hay))
  where
    cTokens [] = []
    cTokens cs@(c:rest)
      | isIdentChar c = let (w, cs') = span isIdentChar cs in w : cTokens cs'
      | otherwise     = cTokens rest
    isIdentChar ch = ch `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_")

typedefOf :: IntWidth -> String
typedefOf W8  = "GibInt8"
typedefOf W16 = "GibInt16"
typedefOf W32 = "GibInt32"
typedefOf W64 = "GibInt64"

suffixOf :: IntWidth -> String
suffixOf W8  = "i8"
suffixOf W16 = "i16"
suffixOf W32 = "i32"
suffixOf W64 = "i64"

-- The six width-annotated integer primitives, with the RTS helper each must
-- reach and the bare C operator each must NOT emit.
arithOps :: [(String, IntWidth -> L4.Prim, String)]
arithOps =
  [ ("add", L4.AddP, "+")
  , ("sub", L4.SubP, "-")
  , ("mul", L4.MulP, "*")
  , ("div", L4.DivP, "/")
  , ("mod", L4.ModP, "%")
  , ("exp", L4.ExpP, "^")
  ]

-- | All 24 combinations: the result binds the exact width typedef, the
-- width's own helper is called exactly once, each operand appears exactly once
-- (so nothing is evaluated twice), and the bare C operator is gone.
case_codegen_emits_width_helper :: Assertion
case_codegen_emits_width_helper = sequence_
  [ do c <- genC' (arithProg w mk)
       let body = probeBody c
           fn = "gib_" ++ nm ++ "_" ++ suffixOf w
           ctx = "\n" ++ body
       assertBool (show (nm, w) ++ ": result must bind " ++ typedefOf w ++ ctx)
                  ((typedefOf w ++ " out") `isInfixOf` body)
       assertEqual (show (nm, w) ++ ": exactly one call to " ++ fn ++ ctx)
                   1 (countOccurrences (fn ++ "(") body)
       -- Each operand appears exactly once inside the body, so a Triv is never
       -- duplicated -- the reason the helpers are inline functions, not macros.
       assertEqual (show (nm, w) ++ ": lhs evaluated once" ++ ctx)
                   1 (countTokens "x" (dropWhile (/= '{') body))
       assertEqual (show (nm, w) ++ ": rhs evaluated once" ++ ctx)
                   1 (countTokens "y" (dropWhile (/= '{') body))
       -- No bare C operator on the binding, and no fallback to the
       -- width-erased infrastructure integer.
       assertBool (show (nm, w) ++ ": must not emit the bare operator " ++ op ++ ctx)
                  (not ((" " ++ op ++ " ") `isInfixOf` bindingLine body))
       assertBool (show (nm, w) ++ ": must not bind a width-erased GibInt" ++ ctx)
                  (not ("GibInt out" `isInfixOf` body))
  | (nm, mk, op) <- arithOps, w <- allWidths ]
  where
    bindingLine b = case filter ("out" `isInfixOf`) (lines b) of
                      (l:_) -> l
                      []    -> ""

-- | A primitive whose annotated width disagrees with the width of the variable
-- it binds is a codegen error.  This is the "width erased or assumed W64" bug
-- class: it must fail loudly rather than pick a default.
case_codegen_rejects_width_mismatch :: Assertion
case_codegen_rejects_width_mismatch = sequence_
  [ do r <- genC (arithProgWith w mk (L4.IntTy w'))
       case r of
         Left _  -> pure ()
         Right c -> assertFailure $ show (nm, w, w')
                      ++ ": codegen accepted a primitive/binder width mismatch:\n" ++ c
  | (nm, mk, _) <- arithOps, w <- allWidths, w' <- allWidths, w /= w' ]

-- | 'AddP' and 'SubP' are overloaded: Lower also uses them for CURSOR
-- arithmetic.  A pointer is not a modular integer, so those must keep C's
-- native operator -- @gib_add_i64@ would not even accept one.
case_codegen_keeps_cursor_arithmetic_native :: Assertion
case_codegen_keeps_cursor_arithmetic_native = sequence_
  [ do c <- genC' (cursorProg mk)
       let body = probeBody c
       assertBool (nm ++ ": cursor arithmetic must stay a native operator\n" ++ body)
                  ((" " ++ op ++ " ") `isInfixOf` body)
       assertEqual (nm ++ ": cursor arithmetic must not call the integer helper\n" ++ body)
                   0 (countOccurrences ("gib_" ++ nm ++ "_i64(") body)
  | (nm, mk, op) <- [("add", L4.AddP, "+"), ("sub", L4.SubP, "-")] ]
  where
    cursorProg mk =
      L4.Prog
        { L4.infoTable = M.empty
        , L4.symbolTable = M.empty
        , L4.fundefs =
            [ L4.FunDecl
                { L4.funName = "arith_probe"
                , L4.funArgs = [("x", L4.CursorTy), ("y", L4.IntTy W64)]
                , L4.funRetTy = L4.CursorTy
                , L4.funBody =
                    L4.LetPrimCallT [("out", L4.CursorTy)] (mk W64)
                                    [L4.VarTriv "x", L4.VarTriv "y"]
                                    (L4.RetValsT [L4.VarTriv "out"])
                , L4.isPure = True
                , L4.funMeta = FunMeta NotRec NoInline False [] Nothing
                }
            ]
        , L4.mainExp = Nothing
        }

--------------------------------------------------------------------------------

intArithmeticTests :: TestTree
intArithmeticTests = $(testGroupGenerator)
