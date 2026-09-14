{-# LANGUAGE TemplateHaskell #-}

-- | Backend invariants that the generated C cannot show on its own.
--
-- Two kinds live here.  One is determinism: generated C must be a function of
-- the program, not of the run, and 'Var' compares on an interned 'Symbol'
-- whose id comes from the intern cache, so anything enumerating a @M.Map Var@
-- leaks the order names happened to be interned in.  The other is agreement
-- between a binding's declared type and what is bound to it, which the
-- emitted C cast hides from the C compiler as well.
module CodegenInvariants
  ( codegenInvariantsTests
  ) where

import Control.Exception (ErrorCall, evaluate, try)
import qualified Data.List as L
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language (FunMeta(..), FunRec(..), FunInline(..), IntWidth(..))
import Gibbon.L4.Syntax
import Gibbon.Passes.Codegen (codegenProg)

-- | Two probe cursors whose 'Var' order is the reverse of their name order.
--
-- Which pairs invert cannot be predicted: an interned id comes from the
-- intern cache's per-bucket counter, so it depends on the name's hash and on
-- how many names hashing alongside it were interned first.  So the pair is
-- searched for rather than assumed, and not finding one is a failure -- that
-- would mean this test had quietly become vacuous.
invertedProbePair :: IO (Var, Var)
invertedProbePair = do
  vs <- mapM (\n -> let v = toVar n in evaluate (length (fromVar v)) >> pure v) names
  case [ (a, b)
       | a <- vs, b <- vs
       , a < b
       , fromVar a > fromVar b
       ] of
    (p:_) -> pure p
    [] ->
      assertFailure
        "no probe pair interned out of name order; this test cannot show anything"
  where
    names = [ "det_probe_" ++ [c1, c2] | c1 <- ['a' .. 'h'], c2 <- ['a' .. 'h'] ]

-- | A function taking both cursors, timing a body that uses neither.
--
-- A timed block saves and restores every mutable cursor in scope, so both
-- arguments get a @saved_@ declaration and the two orders become observable.
timedProbeProg :: Var -> Var -> Prog
timedProbeProg v1 v2 =
  Prog
    { infoTable = M.empty
    , symbolTable = M.empty
    , fundefs =
        [ FunDecl
            { funName = "determinism_probe"
            , funArgs = [(v1, MutCursorTy), (v2, MutCursorTy)]
            , funRetTy = ProdTy []
            , funBody = LetTimedT False [] (RetValsT []) (RetValsT [])
            , isPure = False
            , funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , mainExp = Nothing
    }

-- | A function body binding @vr :: rty@ to a trivial of a different type.
--
-- The emitted C casts the trivial to the declared type, so a mismatch here is
-- invisible to the C compiler too.
mistypedTrivProg :: Ty -> Triv -> Prog
mistypedTrivProg rty rhs =
  Prog
    { infoTable = M.empty
    , symbolTable = M.empty
    , fundefs =
        [ FunDecl
            { funName = "triv_probe"
            , funArgs = []
            , funRetTy = ProdTy []
            , funBody = LetTrivT ("triv_probe_v", rty, rhs) (RetValsT [])
            , isPure = False
            , funMeta = FunMeta NotRec NoInline False [] Nothing
            }
        ]
    , mainExp = Nothing
    }

-- | Line on which @v@'s save is declared.
savedAt :: String -> Var -> Int
savedAt src v =
  case L.findIndex (("saved_" ++ fromVar v) `L.isInfixOf`) (lines src) of
    Just i -> i
    Nothing -> error $ "no save emitted for " ++ fromVar v ++ " in:\n" ++ src

--------------------------------------------------------------------------------

-- | The timed block's saves come out in name order, not in map order.
--
-- @firstInMap@ is the one a @M.Map Var@ would enumerate first and the one that
-- sorts SECOND by name, so emitting in map order and emitting in name order
-- give opposite answers here.
case_timed_saves_are_emitted_in_name_order :: Assertion
case_timed_saves_are_emitted_in_name_order = do
  (firstInMap, firstByName) <- invertedProbePair
  src <- codegenProg defaultConfig (timedProbeProg firstInMap firstByName)
  assertBool
    "the timed block's saved cursors must be emitted in name order"
    (savedAt src firstByName < savedAt src firstInMap)

-- | A narrowing the C cast would perform silently is refused.
case_mistyped_let_triv_is_refused :: Assertion
case_mistyped_let_triv_is_refused = do
  r <- try (codegenProg defaultConfig (mistypedTrivProg (IntTy W32) (intTrivW64 1))
              >>= \src -> evaluate (length src))
  case r :: Either ErrorCall Int of
    Right _ -> assertFailure "expected a W64 trivial bound at W32 to be refused"
    Left e ->
      assertBool ("unexpected message: " ++ show e)
        ("would reinterpret it" `L.isInfixOf` show e)

-- | A binding whose types agree still compiles, so the check is not blanket.
case_well_typed_let_triv_is_accepted :: Assertion
case_well_typed_let_triv_is_accepted = do
  src <- codegenProg defaultConfig (mistypedTrivProg (IntTy W64) (intTrivW64 1))
  assertBool "expected the binding to be emitted"
    ("triv_probe_v" `L.isInfixOf` src)

codegenInvariantsTests :: TestTree
codegenInvariantsTests = $(testGroupGenerator)
