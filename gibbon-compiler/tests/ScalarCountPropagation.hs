{-# LANGUAGE TemplateHaskell #-}

module ScalarCountPropagation
  ( scalarCountPropagationTests
  ) where

import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3
import Gibbon.Passes.ScalarCountPropagation
import Gibbon.Passes.LoopifyTraversals
  ( CountsGateReason(..), countGuaranteedTyCons, countsGateReason
  , unattributedPackedTyCons, writtenDataCons )
import qualified Data.Set as S


-- The cursorized calling convention these hand-built functions stand for.
-- Cursorize records it; a function without it has no convention to read, so
-- the passes under test decline rather than fall back to argument order.
abiTraversal :: Maybe [AbiRole]
abiTraversal = Just [AbiInEnd, AbiOutEnd, AbiOutCur, AbiInCur]

-- A producer that builds from scratch takes only its own output arrays.
abiBuilder :: Maybe [AbiRole]
abiBuilder = Just [AbiOutEnd, AbiOutCur]

runnerEnabled :: L3.Prog3 -> L3.Prog3
runnerEnabled prg =
  fst $
    runPassM
      (defaultConfig {dynflags = gopt_set Opt_StoreScalarFieldCounts (dynflags defaultConfig)})
      0
      (propagateScalarCounts prg)

runnerDisabled :: L3.Prog3 -> L3.Prog3
runnerDisabled prg =
  fst $ defaultPackedRunPassM $ propagateScalarCounts prg

case_disabled_by_default :: Assertion
case_disabled_by_default =
  countCopies (runnerDisabled propagationProg) @?= 0

case_inserts_one_copy_after_producer_call :: Assertion
case_inserts_one_copy_after_producer_call =
  countCopies (runnerEnabled propagationProg) @?= 1

case_does_not_rewrite_recursive_body :: Assertion
case_does_not_rewrite_recursive_body =
  case M.lookup "producer" (fundefs (runnerEnabled propagationProg)) of
    Just fd -> countCopiesExp (funBody fd) @?= 0
    Nothing -> assertFailure "missing producer function"

propagationProg :: L3.Prog3
propagationProg =
  L3.Prog
    (M.fromList [("List", listDDef)])
    (M.fromList [("producer", producerFun)])
    (Just (mainBody, L3.ProdTy []))

listDDef :: L3.DDef3
listDDef =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons =
        [ ("Nil", [])
        , ("Cons", [(False, L3.IntTy W64), (False, L3.FloatTy), (True, L3.PackedTy "List" ())])
        ]
    , memLayout = FullyFactored
    }

-- | A cursorized, shape-preserving SoA map: each constructor branch writes its
-- own tag exactly once and recurses once per packed field.  Matching the SoA
-- cursor ABI alone is deliberately not enough for the pass to propagate
-- counts, so the fixture has to be a real map.
producerFun :: L3.FunDef3
producerFun =
  L3.FunDef
    "producer"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ( replicate 4 (L3.CursorArrayTy 3)
    , L3.ProdTy []
    )
    producerBody
    (FunMeta Rec NoInline False [] abiTraversal)

producerBody :: L3.Exp3
producerBody =
  L3.mkLets
    [ ("in_dcon_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" 1))
    , ("dcur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "in_dcon_loc")
    ]
    (L3.CaseE
      (L3.VarE "dcur")
      [ ("Nil", [], tagOnlyBranch "Nil")
      , ("Cons", [], consBranch)
      ])
  where
    tagOnlyBranch dcon =
      L3.mkLets
        [ ("nil_out_dcon_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
        , ("nil_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag dcon "nil_out_dcon_cur")
        , ("nil_bump_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "in_dcon_loc" (L3.mkLitE64 1))
        , ("nil_bump_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "out_dcon_loc" (L3.mkLitE64 1))
        ]
        (L3.MkProdE [])

    consBranch =
      L3.mkLets
        [ ("in_int_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], L3.ProdTy [L3.IntTy W64, L3.CursorTy], L3.Ext $ L3.ReadScalar L3.intS64 "in_int_cur")
        , ("i", [], L3.IntTy W64, L3.ProjE 0 (L3.VarE "read_int_pair"))
        , ("plus1", [], L3.IntTy W64, L3.PrimAppE addP64 [L3.VarE "i", L3.mkLitE64 1])
        , ("out_int_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_int_loc")
        , ("write_int", [], L3.CursorTy, L3.Ext $ L3.WriteScalar L3.intS64 "out_int_cur" (L3.VarE "plus1"))
        , ("out_dcon_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
        , ("write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "out_dcon_cur")
        , ("bump_int_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "in_int_loc" (L3.mkLitE64 8))
        , ("bump_int_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "out_int_loc" (L3.mkLitE64 8))
        , ("bump_dcon_in", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "in_dcon_loc" (L3.mkLitE64 1))
        , ("bump_dcon_out", [], L3.ProdTy [], L3.Ext $ L3.BumpCursorMutable "out_dcon_loc" (L3.mkLitE64 1))
        , ("recur", [], L3.ProdTy [], L3.AppE "producer" TailModuloCons [] (map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]))
        ]
        (L3.MkProdE [])

mainBody :: L3.Exp3
mainBody =
  L3.LetE
    ("call", [], L3.ProdTy [], L3.AppE "producer" UnknownTailType [] args)
    (L3.VarE "call")
  where
    args = map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]

countCopies :: L3.Prog3 -> Int
countCopies L3.Prog{fundefs, mainExp} =
  sum (map (countCopiesExp . funBody) (M.elems fundefs)) +
  maybe 0 (countCopiesExp . fst) mainExp

countCopiesExp :: L3.Exp3 -> Int
countCopiesExp ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> countCopiesExp rhs + countCopiesExp bod
    L3.IfE a b c -> sum (map countCopiesExp [a,b,c])
    L3.CaseE scrt brs ->
      countCopiesExp scrt + sum [ countCopiesExp rhs | (_, _, rhs) <- brs ]
    L3.MkProdE ls -> sum (map countCopiesExp ls)
    L3.ProjE _ e -> countCopiesExp e
    L3.PrimAppE _ args -> sum (map countCopiesExp args)
    L3.TimeIt e _ _ -> countCopiesExp e
    L3.WithArenaE _ e -> countCopiesExp e
    L3.SpawnE _ _ args -> sum (map countCopiesExp args)
    L3.MapE (_, _, rhs) bod -> countCopiesExp rhs + countCopiesExp bod
    L3.FoldE (_, _, rhs1) (_, _, rhs2) bod ->
      sum (map countCopiesExp [rhs1, rhs2, bod])
    L3.DataConE _ _ args -> sum (map countCopiesExp args)
    L3.Ext ext -> countCopiesExt ext
    _ -> 0

countCopiesExt :: L3.E3Ext () L3.Ty3 -> Int
countCopiesExt ext =
  case ext of
    L3.ScalarCountCopyAll{} -> 1
    L3.ForE _ bound bod -> countCopiesExp bound + countCopiesExp bod
    L3.WhileCursor _ bod -> countCopiesExp bod
    L3.WriteScalar _ _ rhs -> countCopiesExp rhs
    L3.WriteTagPacked _ rhs -> countCopiesExp rhs
    L3.WriteTaggedCursor _ rhs -> countCopiesExp rhs
    L3.WriteCursorMutable _ rhs -> countCopiesExp rhs
    L3.WriteList _ rhs _ -> countCopiesExp rhs
    L3.WriteVector _ rhs _ -> countCopiesExp rhs
    L3.AddCursor _ rhs -> countCopiesExp rhs
    L3.BumpCursorMutable _ rhs -> countCopiesExp rhs
    L3.AddrOfCursor rhs -> countCopiesExp rhs
    L3.LetAvail _ bod -> countCopiesExp bod
    L3.Assert rhs -> countCopiesExp rhs
    L3.WriteCursorSelectiveIndirection _ _ _ mask -> countCopiesExp mask
    _ -> 0


--------------------------------------------------------------------------------
-- VW-09: which producers the count-availability gate can SEE.
--
-- `countGuaranteedTyCons` decides whether a type's values always carry scalar
-- counts, and therefore whether a traversal over it may be loopified and use a
-- stored footer count as an unchecked trip count.  It builds that judgement
-- from `writtenDataCons`, so a producer `writtenDataCons` cannot see is a
-- producer the gate does not know exists.

countedProducer :: L3.FunDef3
countedProducer = producerFun { funMeta = FunMeta Rec NoInline False [StoreScalarCounts] Nothing }

gateProg :: [(Var, L3.FunDef3)] -> L3.Exp3 -> L3.Prog3
gateProg extra mainE =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList (("producer", countedProducer) : extra))
          (Just (mainE, L3.ProdTy []))

case_vw09_gate_requires_a_from_scratch_producer :: Assertion
case_vw09_gate_requires_a_from_scratch_producer =
  let prg = L3.Prog (M.fromList [("List", listDDef)])
                    (M.fromList [("producer", producerFun)])   -- no StoreScalarCounts
                    (Just (L3.MkProdE [], L3.ProdTy []))
   in assertBool "with no count-establishing producer the type must be rejected"
        (S.notMember "List" (countGuaranteedTyCons False prg))

case_vw09_counted_producer_alone_is_accepted :: Assertion
case_vw09_counted_producer_alone_is_accepted =
  assertBool "a lone OPT:StoreScalarCounts producer must make the type eligible"
    (S.member "List" (countGuaranteedTyCons False (gateProg [] (L3.MkProdE []))))

case_vw09_unannotated_extra_producer_disqualifies_the_type :: Assertion
case_vw09_unannotated_extra_producer_disqualifies_the_type =
  let other = producerFun { funName = "otherProducer"
                          , funMeta = FunMeta NotRec NoInline False [] Nothing }
   in assertBool "a user producer that establishes no counts must disqualify the type"
        (S.notMember "List"
           (countGuaranteedTyCons False (gateProg [("otherProducer", other)] (L3.MkProdE []))))

case_vw09_readPackedFile_producer_disqualifies_the_type :: Assertion
case_vw09_readPackedFile_producer_disqualifies_the_type =
  let readE = L3.PrimAppE (ReadPackedFile Nothing "List" Nothing (L3.PackedTy "List" ())) []
      prg = gateProg [] (L3.mkLets [("t", [], L3.PackedTy "List" (), readE)] (L3.MkProdE []))
   in do
     -- `writtenDataCons` recurses only into PrimAppE arguments, so a packed
     -- value read from a file reports no constructors at all.
     [] @=? writtenDataCons readE
     -- ...so `writtenDataCons` alone cannot see this producer.  VW-09 closes
     -- that hole in the GATE rather than in `writtenDataCons`: a packed value
     -- obtained without an attributable producer disqualifies its type, so the
     -- traversal stays recursive instead of looping on untouched footers.
     ["List"] @=? unattributedPackedTyCons readE
     assertBool "readPackedFile must disqualify the type (VW-09)"
       (S.notMember "List" (countGuaranteedTyCons False prg))

case_vw09_generated_copy_helper_is_excluded_from_the_gate :: Assertion
case_vw09_generated_copy_helper_is_excluded_from_the_gate =
  let copyFn = producerFun { funName = "_copy_List"
                           , funMeta = FunMeta Rec NoInline False [] Nothing }
   in assertBool "RECORDED BLIND SPOT (VW-09): a generated _copy_ helper is not a producer here"
        (S.member "List"
           (countGuaranteedTyCons False (gateProg [("_copy_List", copyFn)] (L3.MkProdE []))))

--------------------------------------------------------------------------------
-- Both gate helpers must see through an extension form they do not name.
--
-- Their `Ext` arms route through `L3.Traverse.extExps`, which is total, so a
-- producer reachable only underneath an unlisted form still surfaces.  The
-- alternative -- listing forms and falling through to `[]` -- makes a new
-- `E3Ext` constructor hide producers silently, which is the direction that
-- loses counts.

-- `WriteScalar` is named by neither helper and carries an expression child, so
-- reaching that child is exactly the routing under test.
extWrapping :: L3.Exp3 -> L3.Exp3
extWrapping inner = L3.Ext (L3.WriteScalar (L3.IntS W64) "cur" inner)

case_gate_helpers_see_through_unnamed_ext_forms :: Assertion
case_gate_helpers_see_through_unnamed_ext_forms = do
  let readE = L3.PrimAppE (ReadPackedFile Nothing "List" Nothing (L3.PackedTy "List" ())) []
      dconE = L3.DataConE () "Nil" []
  -- Directly, both helpers see these.
  ["List"] @=? unattributedPackedTyCons readE
  ["Nil"]  @=? writtenDataCons dconE
  -- Underneath an extension form neither helper names, they still do.
  ["List"] @=? unattributedPackedTyCons (extWrapping readE)
  ["Nil"]  @=? writtenDataCons (extWrapping dconE)

--------------------------------------------------------------------------------
-- `--loopification-report` elaborates a counts-gate rejection with the reason.
-- It is a second reading of the same three conditions, so it is pinned to the
-- gate itself: a type is guaranteed exactly when there is no reason.

gateAgrees :: String -> L3.Prog3 -> Assertion
gateAgrees label prg =
  assertBool (label ++ ": the report's reason must agree with the gate")
    (S.member "List" (countGuaranteedTyCons False prg)
       == (countsGateReason False prg "List" == Nothing))

case_report_reason_agrees_with_the_gate :: Assertion
case_report_reason_agrees_with_the_gate = do
  let other = producerFun { funName = "otherProducer"
                          , funMeta = FunMeta NotRec NoInline False [] Nothing }
      copyFn = producerFun { funName = "_copy_List"
                           , funMeta = FunMeta Rec NoInline False [] Nothing }
      noScratch = L3.Prog (M.fromList [("List", listDDef)])
                          (M.fromList [("producer", producerFun)])
                          (Just (L3.MkProdE [], L3.ProdTy []))
  gateAgrees "no from-scratch producer" noScratch
  gateAgrees "counted producer alone" (gateProg [] (L3.MkProdE []))
  gateAgrees "extra uncounted producer" (gateProg [("otherProducer", other)] (L3.MkProdE []))
  gateAgrees "generated copy helper" (gateProg [("_copy_List", copyFn)] (L3.MkProdE []))
  gateAgrees "gibbon_main produces the type" (gateProg [] mainProducesList)

case_report_names_the_specific_counts_gate_reason :: Assertion
case_report_names_the_specific_counts_gate_reason = do
  let other = producerFun { funName = "otherProducer"
                          , funMeta = FunMeta NotRec NoInline False [] Nothing }
      noScratch = L3.Prog (M.fromList [("List", listDDef)])
                          (M.fromList [("producer", producerFun)])
                          (Just (L3.MkProdE [], L3.ProdTy []))
  Just NoScratchProducer @=? countsGateReason False noScratch "List"
  Just (ProducerWithoutCounts "otherProducer")
    @=? countsGateReason False (gateProg [("otherProducer", other)] (L3.MkProdE [])) "List"
  -- One DataConE in gibbon_main disables the type program-wide.
  Just ProducedInGibbonMain
    @=? countsGateReason False (gateProg [] mainProducesList) "List"
  Nothing @=? countsGateReason False (gateProg [] (L3.MkProdE [])) "List"

mainProducesList :: L3.Exp3
mainProducesList =
  L3.mkLets [("l", [], L3.CursorTy, L3.DataConE () "Nil" [])] (L3.MkProdE [])

--------------------------------------------------------------------------------
-- VW-09: coverage/emission reconciliation.
--
-- `copyBindsForRhs` only emits a `ScalarCountCopyAll` when a producer call is
-- the immediate RHS of a `LetE` -- `rewriteExp`'s `go` has no case for a bare
-- `AppE`, so a producer call that is the direct value of an `IfE` branch (a
-- legal, un-flattened L3 shape; `ScalarCountPropagation` runs before
-- `L3.flatten`) is never visited and gets no copy.  `countPropagatedProducers`
-- must therefore say the same thing about that call site, or a type can be
-- declared "count guaranteed" while one of its producer's outputs never
-- actually receives its footer chain.

mainBodyIfBranchUncovered :: L3.Exp3
mainBodyIfBranchUncovered =
  L3.LetE
    ( "call"
    , []
    , L3.ProdTy []
    , L3.IfE
        (L3.PrimAppE ltP64 [L3.mkLitE64 1, L3.mkLitE64 2])
        (L3.AppE "producer" UnknownTailType [] args)
        (L3.AppE "producer" UnknownTailType [] args)
    )
    (L3.VarE "call")
  where
    args = map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]

propagationProgIfBranch :: L3.Prog3
propagationProgIfBranch =
  L3.Prog
    (M.fromList [("List", listDDef)])
    (M.fromList [("producer", producerFun)])
    (Just (mainBodyIfBranchUncovered, L3.ProdTy []))

case_vw09_step82_if_branch_producer_call_gets_no_copy :: Assertion
case_vw09_step82_if_branch_producer_call_gets_no_copy =
  countCopies (runnerEnabled propagationProgIfBranch) @?= 0

case_vw09_step82_coverage_gate_must_not_claim_if_branch_call_is_covered :: Assertion
case_vw09_step82_coverage_gate_must_not_claim_if_branch_call_is_covered =
  assertBool
    ( "SPLIT-BRAIN (VW-09 step 8.2): countPropagatedProducers claims every call "
      ++ "site of \"producer\" is covered, but copyBindsForRhs never emits a "
      ++ "copy for a call that is the direct value of an IfE branch -- a "
      ++ "loopified consumer downstream would read that value's untouched "
      ++ "(never-copied) footers as trip counts"
    )
    (S.notMember "producer" (countPropagatedProducers propagationProgIfBranch))

--------------------------------------------------------------------------------
-- VW-09: adversarial rejection controls.
--
-- Count propagation must be granted to NOTHING that cannot be proven shape
-- preserving.  Each fixture below breaks exactly one clause of
-- `isShapePreservingProducer`'s Cons branch and must therefore receive no
-- `ProducerShape` at all: `producerShapesFor` (checked indirectly, since it
-- is not exported) never has an entry for it, so no call to it is ever
-- copied and it can never appear in `countPropagatedProducers`.

mkAdversarialProducer :: Var -> [(Var, [()], L3.Ty3, L3.Exp3)] -> L3.FunDef3
mkAdversarialProducer name consBinds =
  L3.FunDef
    name
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    (replicate 4 (L3.CursorArrayTy 3), L3.ProdTy [])
    ( L3.mkLets
        [ ("in_dcon_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "inCurs" 0))
        , ("out_dcon_loc", [], L3.MutCursorTy, L3.Ext $ L3.AddrOfCursor (L3.Ext $ L3.IndexCursorArray "outCurs" 0))
        , ("dcur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "in_dcon_loc")
        ]
        (L3.CaseE
          (L3.VarE "dcur")
          [ ( "Nil", []
            , L3.mkLets
                [ ("nil_out_dcon_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
                , ("nil_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Nil" "nil_out_dcon_cur")
                ]
                (L3.MkProdE [])
            )
          , ( "Cons", []
            , L3.mkLets
                ( ("cons_out_dcon_cur", [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor "out_dcon_loc")
                  : consBinds
                )
                (L3.MkProdE [])
            )
          ]
        )
    )
    (FunMeta Rec NoInline False [] abiTraversal)

recurBind :: (Var, [()], L3.Ty3, L3.Exp3)
recurBind =
  ("recur", [], L3.ProdTy [], L3.AppE name TailModuloCons [] (map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]))
  where name = "self"

-- Filtering: writes the Cons tag but never recurses on the packed field, so
-- an element the input had is silently dropped from the output.
filteringProducer :: L3.FunDef3
filteringProducer =
  (mkAdversarialProducer "self" [("cons_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "cons_out_dcon_cur")])

-- Duplicating: writes the Cons tag twice for one input element.
duplicatingProducer :: L3.FunDef3
duplicatingProducer =
  mkAdversarialProducer "self"
    [ ("cons_write_tag1", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "cons_out_dcon_cur")
    , ("cons_write_tag2", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "cons_out_dcon_cur")
    , recurBind
    ]

-- Constructor changing: the Cons branch writes a "Nil" tag instead of "Cons".
constructorChangingProducer :: L3.FunDef3
constructorChangingProducer =
  mkAdversarialProducer "self"
    [ ("cons_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Nil" "cons_out_dcon_cur")
    , recurBind
    ]

adversarialProg :: L3.FunDef3 -> L3.Exp3 -> L3.Prog3
adversarialProg fn mainE =
  L3.Prog (M.fromList [("List", listDDef)])
          (M.fromList [("self", fn)])
          (Just (mainE, L3.ProdTy []))

callSelfLetBound :: L3.Exp3
callSelfLetBound =
  L3.LetE ("call", [], L3.ProdTy [], L3.AppE "self" UnknownTailType [] args) (L3.VarE "call")
  where args = map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]

case_vw09_step82_filtering_producer_gets_no_copy :: Assertion
case_vw09_step82_filtering_producer_gets_no_copy =
  countCopies (runnerEnabled (adversarialProg filteringProducer callSelfLetBound)) @?= 0

case_vw09_step82_duplicating_producer_gets_no_copy :: Assertion
case_vw09_step82_duplicating_producer_gets_no_copy =
  countCopies (runnerEnabled (adversarialProg duplicatingProducer callSelfLetBound)) @?= 0

case_vw09_step82_constructor_changing_producer_gets_no_copy :: Assertion
case_vw09_step82_constructor_changing_producer_gets_no_copy =
  countCopies (runnerEnabled (adversarialProg constructorChangingProducer callSelfLetBound)) @?= 0

case_vw09_step82_filtering_producer_never_covered :: Assertion
case_vw09_step82_filtering_producer_never_covered =
  assertBool "a filtering producer must never be reported count-propagated"
    (S.notMember "self" (countPropagatedProducers (adversarialProg filteringProducer callSelfLetBound)))

case_vw09_step82_duplicating_producer_never_covered :: Assertion
case_vw09_step82_duplicating_producer_never_covered =
  assertBool "a duplicating producer must never be reported count-propagated"
    (S.notMember "self" (countPropagatedProducers (adversarialProg duplicatingProducer callSelfLetBound)))

case_vw09_step82_constructor_changing_producer_never_covered :: Assertion
case_vw09_step82_constructor_changing_producer_never_covered =
  assertBool "a constructor-changing producer must never be reported count-propagated"
    (S.notMember "self" (countPropagatedProducers (adversarialProg constructorChangingProducer callSelfLetBound)))

-- Recursive enclosing context: `rewriteExp` never rewrites a Rec function's
-- own body, so a producer call inside one is never covered, no matter how it
-- looks.
callSelfFromRecursiveEnclosingFun :: L3.FunDef3
callSelfFromRecursiveEnclosingFun =
  L3.FunDef
    "wrapper"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    (replicate 4 (L3.CursorArrayTy 3), L3.ProdTy [])
    callSelfLetBound
    (FunMeta Rec NoInline False [] abiTraversal)

case_vw09_step82_call_in_recursive_enclosing_fun_never_covered :: Assertion
case_vw09_step82_call_in_recursive_enclosing_fun_never_covered =
  let prg = L3.Prog (M.fromList [("List", listDDef)])
                     (M.fromList [ ("producer", countedProducer)
                                 , ("wrapper", callSelfFromRecursiveEnclosingFun { funBody = wrapperBody })
                                 ])
                     (Just (L3.MkProdE [], L3.ProdTy []))
      wrapperBody =
        L3.LetE ("call", [], L3.ProdTy [], L3.AppE "producer" UnknownTailType [] args) (L3.VarE "call")
      args = map L3.VarE ["inEnds", "outEnds", "outCurs", "inCurs"]
   in assertBool "a call inside another Rec function's body must never be covered"
        (S.notMember "producer" (countPropagatedProducers prg))

-- Mismatched cursor-array length: a "producer" whose output cursor array has
-- a different length than its input must never be treated as shape
-- preserving -- the copy's `count` argument would be wrong on its face.
mismatchedLengthProducer :: L3.FunDef3
mismatchedLengthProducer =
  (mkAdversarialProducer "self" [("cons_write_tag", [], L3.CursorTy, L3.Ext $ L3.WriteTag "Cons" "cons_out_dcon_cur"), recurBind])
    { L3.funArgs = ["inEnds", "outEnds", "outCurs", "inCurs"]
    , L3.funTy = ([L3.CursorArrayTy 3, L3.CursorArrayTy 5, L3.CursorArrayTy 5, L3.CursorArrayTy 3], L3.ProdTy [])
    }

case_vw09_step82_mismatched_cursor_array_length_never_covered :: Assertion
case_vw09_step82_mismatched_cursor_array_length_never_covered =
  assertBool "mismatched input/output cursor-array lengths must never be covered"
    (S.notMember "self" (countPropagatedProducers (adversarialProg mismatchedLengthProducer callSelfLetBound)))

scalarCountPropagationTests :: TestTree
scalarCountPropagationTests = testGroup "ScalarCountPropagation" [tests]

tests :: TestTree
tests = $(testGroupGenerator)
