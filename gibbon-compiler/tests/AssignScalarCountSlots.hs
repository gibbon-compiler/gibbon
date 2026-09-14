{-# LANGUAGE TemplateHaskell #-}

module AssignScalarCountSlots
  ( assignScalarCountSlotsTests
  ) where

import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3
import Gibbon.Passes.AssignScalarCountSlots

-- A producer that builds from scratch takes only its own output arrays.
abiBuilder :: Maybe [AbiRole]
abiBuilder = Just [AbiOutEnd, AbiOutCur]

-- The pass is opt-in; without the flag it must be the identity.
runner :: Bool -> L3.Prog3 -> L3.Prog3
runner enabled prg =
  fst $ runPassM cfg 0 (assignScalarCountSlots prg)
  where
    base = dynflags defaultConfig
    cfg | enabled = defaultConfig
            { dynflags = gopt_set Opt_DeferScalarCounts
                           (gopt_set Opt_StoreScalarFieldCounts base) }
        | otherwise = defaultConfig
            { dynflags = gopt_set Opt_StoreScalarFieldCounts base }

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

case_disabled_by_default :: Assertion
case_disabled_by_default = do
  let out = runner False oneProducerProg
  countBrackets out @?= (0, 0)

case_brackets_the_outermost_call :: Assertion
case_brackets_the_outermost_call =
  countBrackets (runner True oneProducerProg) @?= (1, 1)

-- The bind belongs at the outermost call, once per production.  Bracketing a
-- recursive step would rebind -- and so zero -- a counter that is still
-- accumulating, losing every element written so far in that chunk.
case_does_not_bracket_the_recursive_call :: Assertion
case_does_not_bracket_the_recursive_call =
  case M.lookup "mkList" (L3.fundefs (runner True oneProducerProg)) of
    Just fd -> countBracketsExp (L3.funBody fd) @?= (0, 0)
    Nothing -> assertFailure "missing mkList"

-- Slot = base + cursor-array position.  With one producer at base 0 the tag
-- buffer keeps slot 0 and the Int buffer keeps slot 1.
case_rebases_slots_from_positions :: Assertion
case_rebases_slots_from_positions =
  slotsOf "mkList" (runner True oneProducerProg) @?= [0, 0, 1]

-- The property that makes a producer calling another producer safe: two
-- producers must never share a slot, or the inner one's bind would reset the
-- outer one's live counter.
case_two_producers_get_disjoint_slots :: Assertion
case_two_producers_get_disjoint_slots = do
  let out = runner True twoProducerProg
      a = slotsOf "mkA" out
      b = slotsOf "mkB" out
  assertBool ("slot ranges overlap: mkA=" ++ show a ++ " mkB=" ++ show b)
    (null [ s | s <- a, s `elem` b ])

case_two_producers_are_both_bracketed :: Assertion
case_two_producers_are_both_bracketed =
  countBrackets (runner True twoProducerProg) @?= (2, 2)

-- Mutual recursion is the case where "the outermost call" is not well defined:
-- a bracket around mkB's call inside mkA would sit on a recursive step.  Both
-- must fall back to the per-element bump (slot -1) rather than be guessed at.
case_mutually_recursive_producers_keep_the_bump :: Assertion
case_mutually_recursive_producers_keep_the_bump = do
  let out = runner True mutualProg
  countBrackets out @?= (0, 0)
  assertBool "expected every slot to be the no-deferred-slot sentinel"
    (all (== (-1)) (slotsOf "mkA" out ++ slotsOf "mkB" out))

-- | A producer owns the slots @[base, base + osLen)@ and no others.
--
-- A bump position at or past the cursor-array length would rebase onto the
-- next producer's range and add this function's elements to that producer's
-- footers -- a count that is too large, which is the direction that makes a
-- loopified consumer write past the end of a chunk.  The out-of-range footer
-- must keep the per-element bump instead.
--
-- The in-range positions are asserted to still rebase, so this cannot pass by
-- the producer having been refused a base altogether.
case_out_of_range_bump_position_keeps_the_bump :: Assertion
case_out_of_range_bump_position_keeps_the_bump = do
  let out = runner True outOfRangeProg
  slotsOf "mkList" out @?= [0, 0, 1, -1]

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- | Coverage must impose the same ARGUMENT condition as emission.
--
-- 'bracketFor' needs the end-array argument to be literally a variable.  When
-- it is not, 'spliceCalls' emits no bind and no finalize -- so if coverage
-- still certifies the producer, 'rebaseBumps' rewrites its bumps onto an
-- absolute slot that is never bound, the footers stay zero, and a loopified
-- consumer reads a trip count of zero and silently produces empty output.
-- Emission is (0, 0) either way; what this pins is that the SLOTS are the
-- no-deferred-slot sentinel rather than a real, never-bound base.
case_non_var_end_argument_is_not_covered :: Assertion
case_non_var_end_argument_is_not_covered = do
  let out = runner True nonVarEndArgProg
  countBrackets out @?= (0, 0)
  assertBool "a call bracketFor cannot bracket must not be certified covered"
    (all (== (-1)) (slotsOf "mkList" out))

-- The same program with a plain variable at the end-array position is still
-- covered, so the refusal above is about the argument and nothing else.
case_var_end_argument_is_still_covered :: Assertion
case_var_end_argument_is_still_covered =
  countBrackets (runner True oneProducerProg) @?= (1, 1)

nonVarEndArgProg :: L3.Prog3
nonVarEndArgProg =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [("mkList", producerFun "mkList" ["mkList"])])
          (Just (nonVarCallMain, L3.ProdTy []))

nonVarCallMain :: L3.Exp3
nonVarCallMain =
  L3.mkLets
    [ ("m_mkList", [], L3.ProdTy []
      , L3.AppE "mkList" UnknownTailType []
          [ L3.ProjE 0 (L3.MkProdE [L3.VarE "outEnds"])
          , L3.VarE "outCurs" ]) ]
    (L3.MkProdE [])

listDDef :: L3.DDef3
listDDef =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons = [("Nil", []), ("Cons", [(False, L3.IntTy W64), (True, L3.PackedTy "List" ())])]
    , memLayout = FullyFactored
    }

-- A producer's SoA ABI: it builds from scratch, so it takes only its own
-- output arrays -- [outEnds, outCurs], two buffers each (tag + Int).
producerFun :: Var -> [Var] -> L3.FunDef3
producerFun name callees =
  L3.FunDef name ["outEnds", "outCurs"]
    (replicate 2 (L3.CursorArrayTy 2), L3.ProdTy [])
    (producerBody name callees)
    (FunMeta Rec NoInline False [] abiBuilder)

producerBody :: Var -> [Var] -> L3.Exp3
producerBody _self callees =
  L3.mkLets
    [ ("out_dcon_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" 0))
    , ("out_int_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" 1))
    ]
    (L3.IfE (L3.PrimAppE eqIntP64 [L3.mkLitE64 0, L3.mkLitE64 0]) nilBranch consBranch)
  where
    -- The Nil branch writes only a tag: position 0, and no Int-buffer count.
    nilBranch =
      L3.mkLets
        [ ("nil_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
        , ("nil_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Nil" "nil_cur")
        , ("nil_count", [], L3.ProdTy [], L3.Ext $ L3.ScalarCountBump "Nil" [("outEnds", 0)])
        ]
        (L3.MkProdE [])

    -- Cons writes both buffers: positions 0 and 1.
    consBranch =
      L3.mkLets
        ([ ("cons_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
         , ("cons_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "cons_cur")
         , ("cons_count", [], L3.ProdTy [], L3.Ext $ L3.ScalarCountBump "Cons" [("outEnds", 0), ("outEnds", 1)])
         ]
         ++ [ (toVar ("call_" ++ fromVar c), [], L3.ProdTy []
              , L3.AppE c UnknownTailType [] (map L3.VarE ["outEnds", "outCurs"]))
            | c <- callees ])
        (L3.MkProdE [])

-- A producer whose Cons branch bumps position 2 as well -- one past the end of
-- its own two-buffer output array.
outOfRangeProg :: L3.Prog3
outOfRangeProg =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [("mkList", withExtraBump (producerFun "mkList" ["mkList"]))])
          (Just (callMain ["mkList"], L3.ProdTy []))
  where
    withExtraBump fd = fd { L3.funBody = addBump (L3.funBody fd) }
    addBump ex =
      case ex of
        L3.LetE b bod -> L3.LetE b (addBump bod)
        L3.IfE a b c -> L3.IfE a b (addBump c)
        _ ->
          L3.mkLets
            [ ("extra_count", [], L3.ProdTy []
              , L3.Ext $ L3.ScalarCountBump "Cons" [("outEnds", 2)]) ]
            ex

oneProducerProg :: L3.Prog3
oneProducerProg =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [("mkList", producerFun "mkList" ["mkList"])])
          (Just (callMain ["mkList"], L3.ProdTy []))

twoProducerProg :: L3.Prog3
twoProducerProg =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [ ("mkA", producerFun "mkA" ["mkA"])
                      , ("mkB", producerFun "mkB" ["mkB"]) ])
          (Just (callMain ["mkA", "mkB"], L3.ProdTy []))

mutualProg :: L3.Prog3
mutualProg =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [ ("mkA", producerFun "mkA" ["mkB"])
                      , ("mkB", producerFun "mkB" ["mkA"]) ])
          (Just (callMain ["mkA"], L3.ProdTy []))

callMain :: [Var] -> L3.Exp3
callMain fns =
  L3.mkLets
    [ (toVar ("m_" ++ fromVar f), [], L3.ProdTy []
      , L3.AppE f UnknownTailType [] (map L3.VarE ["outEnds", "outCurs"]))
    | f <- fns ]
    (L3.MkProdE [])

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

countBrackets :: L3.Prog3 -> (Int, Int)
countBrackets L3.Prog{L3.fundefs, L3.mainExp} =
  foldr add (0, 0) $
    map (countBracketsExp . L3.funBody) (M.elems fundefs)
      ++ maybe [] (\(e, _) -> [countBracketsExp e]) mainExp
  where add (a, b) (c, d) = (a + c, b + d)

countBracketsExp :: L3.Exp3 -> (Int, Int)
countBracketsExp = go
  where
    go ex =
      case ex of
        L3.LetE (_, _, _, rhs) bod -> add (go rhs) (go bod)
        L3.IfE a b c -> add (go a) (add (go b) (go c))
        L3.CaseE s brs -> foldr (add . (\(_, _, r) -> go r)) (go s) brs
        L3.MkProdE ls -> foldr (add . go) (0, 0) ls
        L3.ProjE _ e -> go e
        L3.PrimAppE _ as -> foldr (add . go) (0, 0) as
        L3.Ext (L3.ScalarCountBind{}) -> (1, 0)
        L3.Ext (L3.ScalarCountFinalize{}) -> (0, 1)
        L3.Ext (L3.ForE _ b bod) -> add (go b) (go bod)
        L3.Ext (L3.WhileCursor _ bod) -> go bod
        _ -> (0, 0)
    add (a, b) (c, d) = (a + c, b + d)

-- Every bump slot in a function, in traversal order.
slotsOf :: Var -> L3.Prog3 -> [Int]
slotsOf name L3.Prog{L3.fundefs} =
  maybe [] (go . L3.funBody) (M.lookup name fundefs)
  where
    go ex =
      case ex of
        L3.LetE (_, _, _, rhs) bod -> go rhs ++ go bod
        L3.IfE a b c -> go a ++ go b ++ go c
        L3.CaseE s brs -> go s ++ concat [ go r | (_, _, r) <- brs ]
        L3.MkProdE ls -> concatMap go ls
        L3.ProjE _ e -> go e
        L3.PrimAppE _ as -> concatMap go as
        L3.Ext (L3.ScalarCountBump _ fs) -> map snd fs
        L3.Ext (L3.ForE _ b bod) -> go b ++ go bod
        L3.Ext (L3.WhileCursor _ bod) -> go bod
        _ -> []

assignScalarCountSlotsTests :: TestTree
assignScalarCountSlotsTests = $(testGroupGenerator)
