{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module LoopifyTraversals
  ( loopifyTraversalsTests
  ) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Exception (ErrorCall, evaluate, try)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L3.Syntax
import Gibbon.L2.Syntax (Modality(..))
import Gibbon.L3.Typecheck (tcProg)
import qualified Gibbon.L4.Syntax as T
import Gibbon.Passes.Lower (lower)
import Gibbon.Passes.LoopifyTraversals
import Gibbon.Passes.LoopifiedTraversalFusion
import Gibbon.Passes.VectorizeTraversals (vectorizeTraversals)


-- The cursorized calling convention these hand-built functions stand for.
-- Cursorize records it; a function without it has no convention to read, so
-- the passes under test decline rather than fall back to argument order.
abiTraversal :: Maybe [AbiRole]
abiTraversal = Just [AbiInEnd, AbiOutEnd, AbiOutCur, AbiInCur]

-- One more cursor array past the convention's four: not a role the convention
-- names, so it must not be mistaken for one.
abiTraversalExtra :: Maybe [AbiRole]
abiTraversalExtra = Just [AbiInEnd, AbiOutEnd, AbiOutCur, AbiInCur, AbiOther]

runner :: Prog3 -> Prog3
runner prg = fst $ defaultPackedRunPassM $ loopifyTraversals prg

runnerWithCounts :: Prog3 -> Prog3
runnerWithCounts prg =
  fst $
    runPassM
      (defaultConfig {dynflags = loopifyDFlags})
      0
      (loopifyTraversals prg)

runnerWithCountsAuto :: Prog3 -> Prog3
runnerWithCountsAuto prg =
  fst $
    runPassM
      (defaultConfig {dynflags = gopt_set Opt_AutoLoopification loopifyDFlags})
      0
      (loopifyTraversals prg)

loopifyDFlags :: DynFlags
loopifyDFlags =
  gopt_set Opt_EnableLoopification $
    gopt_set Opt_StoreScalarFieldCounts (dynflags defaultConfig)

withoutFunOpts :: Var -> Prog3 -> Prog3
withoutFunOpts fn prg@Prog{fundefs} =
  prg { fundefs = M.adjust clearOpts fn fundefs }
  where
    clearOpts fd@FunDef{funMeta} = fd { funMeta = funMeta { funOpt = [] } }

withCountedProducer :: TyCon -> Prog3 -> Prog3
withCountedProducer tycon prg@Prog{fundefs} =
  prg { fundefs = M.insert "countedBuilder" (countedBuilderFun tycon) fundefs }

runnerWithCountsNoFusion :: Prog3 -> Prog3
runnerWithCountsNoFusion prg =
  fst $
    runPassM
      ( defaultConfig
          { dynflags =
              loopifyDFlags
          }
      )
      0
      (loopifyTraversals prg)

runnerWithCountsThenFusion :: Prog3 -> Prog3
runnerWithCountsThenFusion prg =
  fst $
    runPassM
      (defaultConfig {dynflags = gopt_set Opt_EnableLoopFusion loopifyDFlags})
      0
      (loopifyTraversals prg >>= fuseLoopifiedTraversals)

runLowering :: Prog3 -> T.Prog
runLowering prg = fst $ defaultPackedRunPassM $ do
  prg' <- tcProg True prg
  lower prg'

listProg :: MemoryLayout -> [FunOpt] -> Prog3
listProg layout opts =
  Prog
    (M.fromList [("List", listDDef layout)])
    (M.fromList [("add1List", listFun opts)])
    Nothing

mixedProg :: Prog3
mixedProg =
  Prog
    (M.fromList [("List", listDDef FullyFactored), ("Tree", treeDDef FullyFactored)])
    (M.fromList [("mix", mixedFun [MayVectorize])])
    Nothing

loopIrProg :: Prog3
loopIrProg =
  Prog
    M.empty
    (M.fromList [("loopProbe", loopProbeFun)])
    Nothing

cursorizedLoopifyProg :: Prog3
cursorizedLoopifyProg =
  Prog
    (M.fromList [("List", cursorizedListDDef)])
    (M.fromList [("fastAdd1List", cursorizedLoopifyFun)])
    Nothing

-- | The cursorized loop body above, with the Int field's write RHS replaced by
-- an arbitrary expression over the field value @i@.  Used to feed the real
-- 'loopifyTraversals' a GUARDED PARTIAL operation and then check, structurally,
-- where the resulting binding ended up.
cursorizedGuardedBodyFor :: Var -> Exp3 -> Exp3
cursorizedGuardedBodyFor selfName scalarRhs =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("in_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 2))
    , ("out_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 2))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], mutableNilBranch "Nil")
      , ("Cons", [], recBranch)
      ])
  where
    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("guarded", [], IntTy W64, scalarRhs)
        , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "guarded"))
        , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
        , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
        , ("in_float_cur", [], CursorTy, Ext $ DerefMutCursor "in_float_loc")
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ("out_float_cur", [], CursorTy, Ext $ DerefMutCursor "out_float_loc")
        , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur" (VarE "f"))
        , ("bump_float_in", [], ProdTy [], Ext $ BumpCursorMutable "in_float_loc" (mkLitE64 4))
        , ("bump_float_out", [], ProdTy [], Ext $ BumpCursorMutable "out_float_loc" (mkLitE64 4))
        , ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
        , ("write_tag", [], CursorTy, Ext $ WriteTag "Cons" "out_dcon_cur")
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        , ("recur", [], ProdTy [], AppE selfName TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
        ]
        (MkProdE [])

-- | The same cursorized SoA program, but with an extra binding in the branch
-- that is never used.  This is the shape of the source-level defect: the
-- binding is a SIBLING of the scalar write, not nested inside its right-hand
-- side, so the scalar-expression grammar never sees it and the synthesized loop
-- simply omits it.
deadSiblingProg :: Exp3 -> Prog3
deadSiblingProg deadRhs =
  withCountedProducer "List" $
    Prog
      (M.fromList [("List", cursorizedListDDef)])
      (M.fromList [("fastAdd1ListMut", fd)])
      Nothing
  where
    fd =
      FunDef
        "fastAdd1ListMut"
        ["inEnds", "outEnds", "outCurs", "inCurs"]
        ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
        (insertDead (cursorizedGuardedBodyFor "fastAdd1ListMut"
                       (PrimAppE addP64 [VarE "i", mkLitE64 1])))
        (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)
    -- Splice the dead binding in immediately after `i` is read, so it is in
    -- scope exactly where a source-level one would be.
    insertDead ex =
      case ex of
        LetE b@(v, _, _, _) bod
          | v == "i" -> LetE b (LetE ("dead_sib", [], IntTy W64, deadRhs) (insertDead bod))
          | otherwise -> LetE b (insertDead bod)
        CaseE scrt brs -> CaseE scrt [ (dc, vs, insertDead r) | (dc, vs, r) <- brs ]
        _ -> ex

loopifiedDeadSiblingBody :: Exp3 -> Exp3
loopifiedDeadSiblingBody deadRhs =
  let Prog{fundefs = fds} = runnerWithCounts (deadSiblingProg deadRhs)
  in funBody (fds M.! "fastAdd1ListMut")

guardedProg :: Exp3 -> Prog3
guardedProg scalarRhs =
  withCountedProducer "List" $
    Prog
      (M.fromList [("List", cursorizedListDDef)])
      (M.fromList [("fastAdd1ListMut", fd)])
      Nothing
  where
    fd =
      FunDef
        "fastAdd1ListMut"
        ["inEnds", "outEnds", "outCurs", "inCurs"]
        ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
        (cursorizedGuardedBodyFor "fastAdd1ListMut" scalarRhs)
        (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

-- @if i == 0 then 7 else 100 / i@
guardedDivRhs :: Exp3
guardedDivRhs =
  IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
      (mkLitE64 7)
      (PrimAppE divP64 [mkLitE64 100, VarE "i"])

-- @if i == 0 then 7 else if i == 1 then 100 / i else 60 / i@
nestedGuardedDivRhs :: Exp3
nestedGuardedDivRhs =
  IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
      (mkLitE64 7)
      (IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 1])
           (PrimAppE divP64 [mkLitE64 100, VarE "i"])
           (PrimAppE divP64 [mkLitE64 60, VarE "i"]))

-- @if i == 0 then 7 else 100 / (i * 2)@ -- a CHAIN of dependent temporaries in
-- one arm, all of which must stay inside it.
chainedGuardedDivRhs :: Exp3
chainedGuardedDivRhs =
  IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
      (mkLitE64 7)
      (PrimAppE divP64 [mkLitE64 100, PrimAppE mulP64 [VarE "i", mkLitE64 2]])

-- @if i == 0 then i + 1 else i - 1@ -- TOTAL, nothing partial anywhere.
totalCondRhs :: Exp3
totalCondRhs =
  IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
      (PrimAppE addP64 [VarE "i", mkLitE64 1])
      (PrimAppE subP64 [VarE "i", mkLitE64 1])

-- | Let-bound variables whose RHS mentions a partial primitive, split by
-- whether the binding sits inside a conditional arm.
--
-- This is the dominance property stated directly: after loopification, a
-- division that the source only reached under a guard must be bound INSIDE the
-- arm.  A binding outside every arm would run the partial primitive
-- unconditionally, which is the bug this test guards against.
partialBindingSites :: Exp3 -> ([Var], [Var])   -- ^ (inside an arm, outside every arm)
partialBindingSites = go False
  where
    go inArm ex =
      case ex of
        LetE (v, _, _, rhs) bod ->
          let here = if mentionsPartial rhs
                     then (if inArm then ([v], []) else ([], [v]))
                     else ([], [])
          in here <> go inArm rhs <> go inArm bod
        IfE a b c -> go inArm a <> go True b <> go True c
        AppE _ _ _ args -> mconcat (map (go inArm) args)
        PrimAppE _ args -> mconcat (map (go inArm) args)
        ProjE _ e -> go inArm e
        MkProdE es -> mconcat (map (go inArm) es)
        CaseE scrt brs -> go inArm scrt <> mconcat [ go inArm r | (_, _, r) <- brs ]
        DataConE _ _ es -> mconcat (map (go inArm) es)
        TimeIt e _ _ -> go inArm e
        WithArenaE _ e -> go inArm e
        SpawnE _ _ args -> mconcat (map (go inArm) args)
        SyncE -> ([], [])
        MapE (_, _, e1) e2 -> go inArm e1 <> go inArm e2
        FoldE (_, _, e1) (_, _, e2) e3 -> mconcat (map (go inArm) [e1, e2, e3])
        -- The loopified body sits inside a WhileCursor/ForE nest, so every
        -- Ext form that can carry an expression has to be walked; stopping at
        -- the outermost one silently finds nothing and passes vacuously.
        Ext (ForE _ bound bod) -> go inArm bound <> go inArm bod
        Ext (WhileCursor _ bod) -> go inArm bod
        Ext (WriteScalar _ _ rhs) -> go inArm rhs
        Ext (WriteTaggedCursor _ rhs) -> go inArm rhs
        Ext (WriteCursorMutable _ rhs) -> go inArm rhs
        Ext (WriteList _ rhs _) -> go inArm rhs
        Ext (WriteVector _ rhs _) -> go inArm rhs
        Ext (AddCursor _ rhs) -> go inArm rhs
        Ext (BumpCursorMutable _ rhs) -> go inArm rhs
        Ext (AddrOfCursor rhs) -> go inArm rhs
        Ext (LetAvail _ bod) -> go inArm bod
        Ext (Assert rhs) -> go inArm rhs
        Ext _ -> ([], [])
        _ -> ([], [])

    -- Does THIS binding's own right-hand side evaluate a partial operation
    -- unconditionally?  Deliberately does NOT descend through `IfE` or `LetE`:
    -- a binding like `conditional_write = if c then .. else 100 / i` does not
    -- itself divide -- the division is guarded inside it, which is the whole
    -- point.  Counting such enclosing bindings would report a violation for
    -- correct output.
    mentionsPartial ex =
      case ex of
        PrimAppE p args -> isPartial p || any mentionsPartial args
        ProjE _ e -> mentionsPartial e
        _ -> False
    isPartial p = case p of
                    DivP{} -> True
                    ModP{} -> True
                    FDivP  -> True
                    _      -> False

-- | Every let-bound variable in an expression, in order (duplicates kept).
allLetBinders :: Exp3 -> [Var]
allLetBinders ex =
  case ex of
    LetE (v, _, _, rhs) bod -> v : allLetBinders rhs ++ allLetBinders bod
    IfE a b c -> concatMap allLetBinders [a, b, c]
    AppE _ _ _ args -> concatMap allLetBinders args
    PrimAppE _ args -> concatMap allLetBinders args
    ProjE _ e -> allLetBinders e
    MkProdE es -> concatMap allLetBinders es
    CaseE scrt brs -> allLetBinders scrt ++ concat [ allLetBinders r | (_, _, r) <- brs ]
    DataConE _ _ es -> concatMap allLetBinders es
    TimeIt e _ _ -> allLetBinders e
    WithArenaE _ e -> allLetBinders e
    SpawnE _ _ args -> concatMap allLetBinders args
    SyncE -> []
    MapE (_, _, e1) e2 -> allLetBinders e1 ++ allLetBinders e2
    FoldE (_, _, e1) (_, _, e2) e3 -> concatMap allLetBinders [e1, e2, e3]
    Ext (ForE _ bound bod) -> allLetBinders bound ++ allLetBinders bod
    Ext (WhileCursor _ bod) -> allLetBinders bod
    Ext (WriteScalar _ _ rhs) -> allLetBinders rhs
    Ext (WriteTaggedCursor _ rhs) -> allLetBinders rhs
    Ext (WriteCursorMutable _ rhs) -> allLetBinders rhs
    Ext (WriteList _ rhs _) -> allLetBinders rhs
    Ext (WriteVector _ rhs _) -> allLetBinders rhs
    Ext (AddCursor _ rhs) -> allLetBinders rhs
    Ext (BumpCursorMutable _ rhs) -> allLetBinders rhs
    Ext (AddrOfCursor rhs) -> allLetBinders rhs
    Ext (LetAvail _ bod) -> allLetBinders bod
    Ext (Assert rhs) -> allLetBinders rhs
    Ext _ -> []
    _ -> []

loopifiedGuardedBody :: Exp3 -> Exp3
loopifiedGuardedBody rhs =
  let Prog{fundefs = fds} = runnerWithCounts (guardedProg rhs)
  in funBody (fds M.! "fastAdd1ListMut")

cursorizedMutableLoopifyProg :: Prog3
cursorizedMutableLoopifyProg =
  Prog
    (M.fromList [("List", cursorizedListDDef)])
    (M.fromList [("fastAdd1ListMut", cursorizedMutableLoopifyFun)])
    Nothing

cursorizedMutableLoopifyExtraCursorProg :: Prog3
cursorizedMutableLoopifyExtraCursorProg =
  Prog
    (M.fromList [("List", cursorizedListDDef)])
    (M.fromList [("fastAdd1ListMutExtra", cursorizedMutableLoopifyExtraCursorFun)])
    Nothing

cursorizedMutableParentChildDependentProg :: Prog3
cursorizedMutableParentChildDependentProg =
  Prog
    (M.fromList [("List", cursorizedListDDef)])
    (M.fromList [("badParentChildMut", cursorizedMutableParentChildDependentFun)])
    Nothing

cursorizedMutableTreeLoopifyProg :: Prog3
cursorizedMutableTreeLoopifyProg =
  Prog
    (M.fromList [("Tree", treeDDef FullyFactored)])
    (M.fromList [("fastAdd1TreeMut", cursorizedMutableTreeLoopifyFun)])
    Nothing

cursorizedRealisticMutableLoopifyProg :: Prog3
cursorizedRealisticMutableLoopifyProg =
  Prog
    (M.fromList [("List", cursorizedRuntimeListDDef)])
    (M.fromList [("fastAdd1ListRealisticMut", cursorizedRealisticMutableLoopifyFun)])
    Nothing

listDDef :: MemoryLayout -> DDef3
listDDef layout =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons =
        [ ("Nil", [])
        , ("Cons", [(False, IntTy W64), (True, PackedTy "List" ())])
        ]
    , memLayout = layout
    }

treeDDef :: MemoryLayout -> DDef3
treeDDef layout =
  DDef
    { tyName = "Tree"
    , tyArgs = []
    , dataCons =
        [ ("Leaf", [(False, IntTy W64)])
        , ("Node", [(True, PackedTy "Tree" ()), (True, PackedTy "Tree" ())])
        ]
    , memLayout = layout
    }

cursorizedListDDef :: DDef3
cursorizedListDDef =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons =
        [ ("Nil", [])
        , ("Cons", [(False, IntTy W64), (False, FloatTy), (True, PackedTy "List" ())])
        ]
    , memLayout = FullyFactored
    }

cursorizedRuntimeListDDef :: DDef3
cursorizedRuntimeListDDef =
  DDef
    { tyName = "List"
    , tyArgs = []
    , dataCons =
        [ ("Nil", [])
        , ("Cons", [(False, IntTy W64), (False, FloatTy), (True, PackedTy "List" ())])
        , ("INDIRECTION_0", [(False, CursorArrayTy 3)])
        , ("REDIRECTION_1", [(False, CursorTy)])
        ]
    , memLayout = FullyFactored
    }

listFun :: [FunOpt] -> FunDef3
listFun opts =
  FunDef
    "add1List"
    ["xs"]
    ([CursorArrayTy 2], CursorArrayTy 2)
    listBody
    (FunMeta Rec NoInline False opts Nothing)

mixedFun :: [FunOpt] -> FunDef3
mixedFun opts =
  FunDef
    "mix"
    ["xs"]
    ([CursorArrayTy 2], CursorArrayTy 2)
    mixedBody
    (FunMeta Rec NoInline False opts Nothing)

loopProbeFun :: FunDef3
loopProbeFun =
  FunDef
    "loopProbe"
    ["footer"]
    ([CursorTy], ProdTy [])
    loopProbeBody
    (FunMeta Rec NoInline False [] Nothing)

countedBuilderFun :: TyCon -> FunDef3
countedBuilderFun tycon =
  FunDef
    "countedBuilder"
    ["footer"]
    ([CursorTy], ProdTy [])
    (Ext $ ScalarCountBump dcon [("footer", 0)])
    (FunMeta Rec NoInline False [StoreScalarCounts] Nothing)
  where
    dcon = case tycon of
             "List" -> "Cons"
             "Tree" -> "Leaf"
             _ -> error $ "countedBuilderFun: unknown tycon " ++ sdoc tycon

cursorizedLoopifyFun :: FunDef3
cursorizedLoopifyFun =
  FunDef
    "fastAdd1List"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, ProdTy [CursorArrayTy 3, CursorArrayTy 3]])
    cursorizedLoopifyBody
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

cursorizedMutableLoopifyFun :: FunDef3
cursorizedMutableLoopifyFun =
  FunDef
    "fastAdd1ListMut"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
    cursorizedMutableLoopifyBody
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

cursorizedMutableLoopifyExtraCursorFun :: FunDef3
cursorizedMutableLoopifyExtraCursorFun =
  FunDef
    "fastAdd1ListMutExtra"
    ["inEnds", "outEnds", "outCurs", "inCurs", "spareCursors"]
    ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 1], ProdTy [])
    (cursorizedMutableLoopifyBodyFor "fastAdd1ListMutExtra")
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversalExtra)

cursorizedMutableParentChildDependentFun :: FunDef3
cursorizedMutableParentChildDependentFun =
  FunDef
    "badParentChildMut"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
    cursorizedMutableParentChildDependentBody
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

cursorizedMutableTreeLoopifyFun :: FunDef3
cursorizedMutableTreeLoopifyFun =
  FunDef
    "fastAdd1TreeMut"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ([CursorArrayTy 2, CursorArrayTy 2, CursorArrayTy 2, CursorArrayTy 2], ProdTy [])
    cursorizedMutableTreeLoopifyBody
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

cursorizedRealisticMutableLoopifyFun :: FunDef3
cursorizedRealisticMutableLoopifyFun =
  FunDef
    "fastAdd1ListRealisticMut"
    ["inEnds", "outEnds", "outCurs", "inCurs"]
    ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
    cursorizedRealisticMutableLoopifyBody
    (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

listBody :: Exp3
listBody =
  CaseE
    (VarE "xs")
    [ ("Nil", [], DataConE () "Nil" [])
    , ("Cons", [("i", ()), ("rst", ())], DataConE () "Cons" [VarE "i", VarE "rst"])
    ]

mixedBody :: Exp3
mixedBody =
  LetE
    ("t", [], CursorTy, Ext $ WriteTag "Leaf" "some_cur")
    (CaseE
      (VarE "xs")
      [ ("Nil", [], DataConE () "Nil" [])
      , ("Cons", [("i", ()), ("rst", ())], DataConE () "Cons" [VarE "i", VarE "rst"])
      ])

loopProbeBody :: Exp3
loopProbeBody =
  LetE
    ("first", [], CursorTy, Ext $ ReadScalarCountFirstFooter "footer")
    (LetE
      ("count", [], IntTy W64, Ext $ ReadScalarCount "first")
      (LetE
        ("next", [], CursorTy, Ext $ ReadScalarCountNextFooter "first")
        (LetE
          ("nextCount", [], IntTy W64, Ext $ ReadScalarCount "next")
          (LetE
            ("_loop", [], ProdTy [], Ext $ ForE "i" (VarE "count") (MkProdE []))
            (MkProdE [])))))

cursorizedLoopifyBody :: Exp3
cursorizedLoopifyBody =
  mkLets
    [ ("dout_end", [], CursorTy, Ext $ IndexCursorArray "outEnds" 0)
    , ("int_out_end", [], CursorTy, Ext $ IndexCursorArray "outEnds" 1)
    , ("float_out_end", [], CursorTy, Ext $ IndexCursorArray "outEnds" 2)
    , ("int_out_loc", [], CursorTy, Ext $ IndexCursorArray "outCurs" 1)
    , ("dout_loc", [], CursorTy, Ext $ IndexCursorArray "outCurs" 0)
    , ("float_out_loc", [], CursorTy, Ext $ IndexCursorArray "outCurs" 2)
    , ( "_bounds"
      , []
      , IntTy W64
      , Ext $ BoundsCheckVector [(13, "float_out_end", "float_out_loc", ("float_out_end", "float_out_loc"))
                                ,(17, "int_out_end", "int_out_loc", ("int_out_end", "int_out_loc"))
                                ,(34, "dout_end", "dout_loc", ("dout_end", "dout_loc"))]
      )
    , ("overwrite_reg", [], CursorArrayTy 3, Ext $ MakeCursorArray 3 ["dout_end", "int_out_end", "float_out_end"])
    , ("dcur", [], CursorTy, Ext $ IndexCursorArray "inCurs" 0)
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], nilBranch)
      , ("Cons", [], recBranch)
      ])
  where
    nilBranch =
      mkLets
        [ ("writetag_nil", [], CursorTy, Ext $ WriteTag "Nil" "dout_loc")
        , ("after_tag_nil", [], CursorTy, Ext $ AddCursor "dout_loc" (mkLitE64 1))
        , ("aft_nil", [], CursorArrayTy 3, Ext $ MakeCursorArray 3 ["after_tag_nil", "int_out_loc", "float_out_loc"])
        , ("packed_nil", [], ProdTy [CursorArrayTy 3, CursorArrayTy 3], MkProdE [VarE "outCurs", VarE "aft_nil"])
        ]
        (MkProdE [VarE "inEnds", VarE "overwrite_reg", VarE "inCurs", VarE "packed_nil"])

    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ IndexCursorArray "inCurs" 1)
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("plus1", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
        , ("out_int_cur", [], CursorTy, Ext $ IndexCursorArray "outCurs" 1)
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "plus1"))
        , ("in_float_cur", [], CursorTy, Ext $ IndexCursorArray "inCurs" 2)
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ("out_float_cur", [], CursorTy, Ext $ IndexCursorArray "outCurs" 2)
        , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur" (VarE "f"))
        , ("dcon_next", [], CursorTy, Ext $ AddCursor "dcur" (mkLitE64 1))
        , ("next_in", [], CursorArrayTy 3, Ext $ MakeCursorArray 3 ["dcon_next", "in_int_cur", "in_float_cur"])
        , ("next_out_dcon", [], CursorTy, Ext $ AddCursor "dout_loc" (mkLitE64 1))
        , ("next_out_int", [], CursorTy, Ext $ AddCursor "int_out_loc" (mkLitE64 8))
        , ("next_out_float", [], CursorTy, Ext $ AddCursor "float_out_loc" (mkLitE64 4))
        , ("next_out", [], CursorArrayTy 3, Ext $ MakeCursorArray 3 ["next_out_dcon", "next_out_int", "next_out_float"])
        , ("writetag_cons", [], CursorTy, Ext $ WriteTag "Cons" "dout_loc")
        , ("recur", [], ProdTy [CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, ProdTy [CursorArrayTy 3, CursorArrayTy 3]], AppE "fastAdd1List" TailModuloCons [] [VarE "inEnds", VarE "overwrite_reg", VarE "next_out", VarE "next_in"])
        ]
        (VarE "recur")

-- | A cursorized nullary-constructor branch.  Real cursorize output always
-- writes the branch's own constructor tag into the output tag stream and
-- advances both dcon cursors, so the fixtures model that.
mutableNilBranch :: DataCon -> Exp3
mutableNilBranch dcon =
  mkLets
    [ ("nil_out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
    , ("nil_write_tag", [], CursorTy, Ext $ WriteTag dcon "nil_out_dcon_cur")
    , ("nil_bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
    , ("nil_bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
    ]
    (MkProdE [])

cursorizedMutableLoopifyBody :: Exp3
cursorizedMutableLoopifyBody = cursorizedMutableLoopifyBodyFor "fastAdd1ListMut"

-- | Same body, parameterized by the name of the enclosing function so that the
-- recursive call really is a self call (as it is in real cursorize output).
cursorizedMutableLoopifyBodyFor :: Var -> Exp3
cursorizedMutableLoopifyBodyFor selfName =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("in_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 2))
    , ("out_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 2))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], mutableNilBranch "Nil")
      , ("Cons", [], recBranch)
      ])
  where
    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("plus1", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
        , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "plus1"))
        , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
        , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
        , ("in_float_cur", [], CursorTy, Ext $ DerefMutCursor "in_float_loc")
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ("out_float_cur", [], CursorTy, Ext $ DerefMutCursor "out_float_loc")
        , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur" (VarE "f"))
        , ("bump_float_in", [], ProdTy [], Ext $ BumpCursorMutable "in_float_loc" (mkLitE64 4))
        , ("bump_float_out", [], ProdTy [], Ext $ BumpCursorMutable "out_float_loc" (mkLitE64 4))
        , ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
        , ("write_tag", [], CursorTy, Ext $ WriteTag "Cons" "out_dcon_cur")
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        , ("recur", [], ProdTy [], AppE selfName TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
        ]
        (MkProdE [])

-- | A partial binding on the branch body's SPINE, consumed by TWO different
-- scalar writes.
--
-- This is the shape `touchHotObjects` has, and the one `multiUsePartialRhs`
-- does NOT: there the whole `let` is a single write's right-hand side, which
-- the 'ScalarExpr' grammar admits directly (it includes `LetE`), so it already
-- loopifies.  A binding that has to cross PLAN boundaries is the case
-- 'collectPureBindings' decides, and the case this pass now handles.
--
-- The float write is conditional on the shared value on purpose: the residual
-- must be attached ABOVE that `IfE`, dominating both arms, because the source
-- evaluated it unconditionally.
sharedPartialBodyFor :: Var -> Exp3
sharedPartialBodyFor selfName =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("in_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 2))
    , ("out_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 2))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], mutableNilBranch "Nil")
      , ("Cons", [], recBranch)
      ])
  where
    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        -- the shared partial, unconditional, used by both writes below
        , ("q_sh", [], IntTy W64, PrimAppE divP64 [mkLitE64 100, VarE "i"])
        , ("plus_q", [], IntTy W64, PrimAppE addP64 [VarE "i", VarE "q_sh"])
        , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "plus_q"))
        , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
        , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
        , ("in_float_cur", [], CursorTy, Ext $ DerefMutCursor "in_float_loc")
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ("out_float_cur", [], CursorTy, Ext $ DerefMutCursor "out_float_loc")
        , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur"
              (IfE (PrimAppE eqIntP64 [VarE "q_sh", mkLitE64 0]) (VarE "f") (VarE "f")))
        , ("bump_float_in", [], ProdTy [], Ext $ BumpCursorMutable "in_float_loc" (mkLitE64 4))
        , ("bump_float_out", [], ProdTy [], Ext $ BumpCursorMutable "out_float_loc" (mkLitE64 4))
        , ("out_dcon_cur", [], CursorTy, Ext $ WriteTag "Cons" "out_dcon_cur")
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        , ("recur", [], ProdTy [], AppE selfName TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
        ]
        (MkProdE [])

sharedPartialProg :: Prog3
sharedPartialProg =
  withCountedProducer "List" $
    Prog
      (M.fromList [("List", cursorizedListDDef)])
      (M.fromList [("fastAdd1ListMut", fd)])
      Nothing
  where
    fd =
      FunDef
        "fastAdd1ListMut"
        ["inEnds", "outEnds", "outCurs", "inCurs"]
        ([CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3, CursorArrayTy 3], ProdTy [])
        (sharedPartialBodyFor "fastAdd1ListMut")
        (FunMeta TailRec NoInline False [MayVectorize] abiTraversal)

cursorizedMutableParentChildDependentBody :: Exp3
cursorizedMutableParentChildDependentBody =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("in_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 2))
    , ("out_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 2))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], mutableNilBranch "Nil")
      , ("Cons", [], recBranch)
      ])
  where
    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "i"))
        , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
        , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
        , ("in_float_cur", [], CursorTy, Ext $ DerefMutCursor "in_float_loc")
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ("out_float_cur", [], CursorTy, Ext $ DerefMutCursor "out_float_loc")
        , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur" (VarE "f"))
        , ("bump_float_in", [], ProdTy [], Ext $ BumpCursorMutable "in_float_loc" (mkLitE64 4))
        , ("bump_float_out", [], ProdTy [], Ext $ BumpCursorMutable "out_float_loc" (mkLitE64 4))
        , ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
        , ("write_tag", [], CursorTy, Ext $ WriteTag "Cons" "out_dcon_cur")
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        , ("child_cond", [], BoolTy, AppE "badParentChildMut" TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
        ]
        (IfE (VarE "child_cond") (MkProdE []) (MkProdE []))

cursorizedMutableTreeLoopifyBody :: Exp3
cursorizedMutableTreeLoopifyBody =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Leaf", [], leafBranch)
      , ("Node", [], nodeBranch)
      ])
  where
    leafBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("plus1", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
        , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
        , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "plus1"))
        , ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
        , ("write_tag_leaf", [], CursorTy, Ext $ WriteTag "Leaf" "out_dcon_cur")
        , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
        , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        ]
        (MkProdE [])

    nodeBranch =
      mkLets
        [ ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
        , ("write_tag_node", [], CursorTy, Ext $ WriteTag "Node" "out_dcon_cur")
        , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
        , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
        ]
        (MkProdE [])

cursorizedRealisticMutableLoopifyBody :: Exp3
cursorizedRealisticMutableLoopifyBody =
  mkLets
    [ ("in_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 0))
    , ("out_dcon_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 0))
    , ("in_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 1))
    , ("out_int_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 1))
    , ("in_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "inCurs" 2))
    , ("out_float_loc", [], MutCursorTy, Ext $ AddrOfCursor (Ext $ IndexCursorArray "outCurs" 2))
    , ("dcur", [], CursorTy, Ext $ DerefMutCursor "in_dcon_loc")
    ]
    (CaseE
      (VarE "dcur")
      [ ("Nil", [], mutableNilBranch "Nil")
      , ("Cons", [], recBranch)
      ])
  where
    recBranch =
      mkLets
        [ ("in_int_cur", [], CursorTy, Ext $ DerefMutCursor "in_int_loc")
        , ("read_int_pair", [], ProdTy [IntTy W64, CursorTy], Ext $ ReadScalar intS64 "in_int_cur")
        , ("i", [], IntTy W64, ProjE 0 (VarE "read_int_pair"))
        , ("plus1", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
        , ("in_float_cur", [], CursorTy, Ext $ DerefMutCursor "in_float_loc")
        , ("read_float_pair", [], ProdTy [FloatTy, CursorTy], Ext $ ReadScalar FloatS "in_float_cur")
        , ("f", [], FloatTy, ProjE 0 (VarE "read_float_pair"))
        , ( "tup_packed"
          , []
          , ProdTy []
          , mkLets
              [ ("out_dcon_cur", [], CursorTy, Ext $ DerefMutCursor "out_dcon_loc")
              , ("write_tag", [], CursorTy, Ext $ WriteTag "Cons" "out_dcon_cur")
              , ("out_int_cur", [], CursorTy, Ext $ DerefMutCursor "out_int_loc")
              , ("write_int", [], CursorTy, Ext $ WriteScalar intS64 "out_int_cur" (VarE "plus1"))
              , ("out_float_cur", [], CursorTy, Ext $ DerefMutCursor "out_float_loc")
              , ("write_float", [], CursorTy, Ext $ WriteScalar FloatS "out_float_cur" (VarE "f"))
              , ("bump_dcon_in", [], ProdTy [], Ext $ BumpCursorMutable "in_dcon_loc" (mkLitE64 1))
              , ("bump_dcon_out", [], ProdTy [], Ext $ BumpCursorMutable "out_dcon_loc" (mkLitE64 1))
              , ("bump_int_in", [], ProdTy [], Ext $ BumpCursorMutable "in_int_loc" (mkLitE64 8))
              , ("bump_int_out", [], ProdTy [], Ext $ BumpCursorMutable "out_int_loc" (mkLitE64 8))
              , ("bump_float_in", [], ProdTy [], Ext $ BumpCursorMutable "in_float_loc" (mkLitE64 4))
              , ("bump_float_out", [], ProdTy [], Ext $ BumpCursorMutable "out_float_loc" (mkLitE64 4))
              ]
              (MkProdE [])
          )
        , ("recur", [], ProdTy [], AppE "fastAdd1ListRealisticMut" TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
        ]
        (MkProdE [])

collectTailPrims :: T.Tail -> [T.Prim]
collectTailPrims tl =
  case tl of
    T.EndOfMain -> []
    T.RetValsT _ -> []
    T.AssnValsT _ mb -> maybe [] collectTailPrims mb
    T.LetCallT {T.bod} -> collectTailPrims bod
    T.LetPrimCallT {T.prim, T.bod} -> prim : collectTailPrims bod
    T.LetTrivT {T.bod} -> collectTailPrims bod
    T.LetIfT {T.ife = (_, t1, t2), T.bod} ->
      collectTailPrims t1 ++ collectTailPrims t2 ++ collectTailPrims bod
    T.LetUnpackT {T.bod} -> collectTailPrims bod
    T.LetAllocT {T.bod} -> collectTailPrims bod
    T.LetAvailT {T.bod} -> collectTailPrims bod
    T.ForLoopT {T.loopBody, T.bod} ->
      collectTailPrims loopBody ++ collectTailPrims bod
    T.WhileCursorT {T.loopBody, T.bod} ->
      collectTailPrims loopBody ++ collectTailPrims bod
    T.IfT {T.con, T.els} ->
      collectTailPrims con ++ collectTailPrims els
    T.ErrT _ -> []
    T.LetTimedT {T.timed, T.bod} ->
      collectTailPrims timed ++ collectTailPrims bod
    T.Switch _ _ alts mb ->
      collectAltsPrims alts ++ maybe [] collectTailPrims mb
    T.TailCall _ _ -> []
    T.Goto _ -> []
    T.LetArenaT {T.bod} -> collectTailPrims bod

collectAltsPrims :: T.Alts -> [T.Prim]
collectAltsPrims alts =
  case alts of
    T.TagAlts ls -> concatMap (collectTailPrims . snd) ls
    T.IntAlts ls -> concatMap (collectTailPrims . snd) ls

containsForLoop :: T.Tail -> Bool
containsForLoop tl =
  case tl of
    T.ForLoopT {} -> True
    T.EndOfMain -> False
    T.RetValsT _ -> False
    T.AssnValsT _ mb -> maybe False containsForLoop mb
    T.LetCallT {T.bod} -> containsForLoop bod
    T.LetPrimCallT {T.bod} -> containsForLoop bod
    T.LetTrivT {T.bod} -> containsForLoop bod
    T.LetIfT {T.ife = (_, t1, t2), T.bod} ->
      containsForLoop t1 || containsForLoop t2 || containsForLoop bod
    T.LetUnpackT {T.bod} -> containsForLoop bod
    T.LetAllocT {T.bod} -> containsForLoop bod
    T.LetAvailT {T.bod} -> containsForLoop bod
    T.IfT {T.con, T.els} ->
      containsForLoop con || containsForLoop els
    T.ErrT _ -> False
    T.LetTimedT {T.timed, T.bod} ->
      containsForLoop timed || containsForLoop bod
    T.Switch _ _ alts mb ->
      containsLoopAlts alts || maybe False containsForLoop mb
    T.TailCall _ _ -> False
    T.Goto _ -> False
    T.LetArenaT {T.bod} -> containsForLoop bod

containsLoopAlts :: T.Alts -> Bool
containsLoopAlts alts =
  case alts of
    T.TagAlts ls -> any (containsForLoop . snd) ls
    T.IntAlts ls -> any (containsForLoop . snd) ls

-- | Count the 'E3Ext' nodes satisfying a predicate, anywhere in an expression.
-- Used by the VW-07 structural tests below.
countExt :: (E3Ext () Ty3 -> Bool) -> Exp3 -> Int
countExt p = go
  where
    go ex = case ex of
      VarE{} -> 0
      LitE{} -> 0
      CharE{} -> 0
      FloatE{} -> 0
      LitSymE{} -> 0
      AppE _ _ _ args -> sum (map go args)
      PrimAppE _ args -> sum (map go args)
      LetE (_, _, _, rhs) bod -> go rhs + go bod
      ProjE _ e -> go e
      IfE a b c -> go a + go b + go c
      MkProdE ls -> sum (map go ls)
      CaseE scrt brs -> go scrt + sum [go rhs | (_, _, rhs) <- brs]
      DataConE _ _ args -> sum (map go args)
      TimeIt e _ _ -> go e
      WithArenaE _ e -> go e
      SpawnE _ _ args -> sum (map go args)
      SyncE -> 0
      MapE (_, _, e1) e2 -> go e1 + go e2
      FoldE (_, _, e1) (_, _, e2) e3 -> go e1 + go e2 + go e3
      Ext ext -> (if p ext then 1 else 0) + goExt ext

    goExt ext = case ext of
      WriteScalar _ _ rhs -> go rhs
      AddCursor _ rhs -> go rhs
      BumpCursorMutable _ rhs -> go rhs
      AddrOfCursor rhs -> go rhs
      RetE ls -> sum (map go ls)
      LetAvail _ bod -> go bod
      ForE _ n bod -> go n + go bod
      WhileCursor _ bod -> go bod
      _ -> 0

isForE', isWhileCursor', isScalarCountSet', isGrowRegion', isBoundsCheckLike
  :: E3Ext () Ty3 -> Bool
isForE' e          = case e of ForE{}          -> True; _ -> False
isWhileCursor' e   = case e of WhileCursor{}   -> True; _ -> False
isScalarCountSet' e = case e of ScalarCountSet{} -> True; _ -> False
isGrowRegion' e    = case e of GrowRegion{}    -> True; _ -> False
isBoundsCheckLike e = case e of
                        BoundsCheck{}       -> True
                        BoundsCheckVector{} -> True
                        _                   -> False

containsL3For :: Exp3 -> Bool
containsL3For ex =
  case ex of
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args -> any containsL3For args
    PrimAppE _ args -> any containsL3For args
    LetE (_, _, _, rhs) bod -> containsL3For rhs || containsL3For bod
    ProjE _ e -> containsL3For e
    IfE a b c -> any containsL3For [a, b, c]
    MkProdE ls -> any containsL3For ls
    CaseE scrt brs -> containsL3For scrt || any (containsL3For . (\(_, _, rhs) -> rhs)) brs
    DataConE _ _ args -> any containsL3For args
    TimeIt e _ _ -> containsL3For e
    WithArenaE _ e -> containsL3For e
    SpawnE _ _ args -> any containsL3For args
    SyncE -> False
    MapE (_, _, e1) e2 -> containsL3For e1 || containsL3For e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any containsL3For [e1, e2, e3]
    Ext (ForE _ _ _) -> True
    Ext (WhileCursor _ bod) -> containsL3For bod
    Ext (WriteScalar _ _ rhs) -> containsL3For rhs
    Ext (WriteTaggedCursor _ rhs) -> containsL3For rhs
    Ext (WriteCursorMutable _ rhs) -> containsL3For rhs
    Ext (WriteList _ rhs _) -> containsL3For rhs
    Ext (WriteVector _ rhs _) -> containsL3For rhs
    Ext (AddCursor _ rhs) -> containsL3For rhs
    Ext (BumpCursorMutable _ rhs) -> containsL3For rhs
    Ext (AddrOfCursor rhs) -> containsL3For rhs
    Ext (LetAvail _ bod) -> containsL3For bod
    Ext (Assert rhs) -> containsL3For rhs
    Ext _ -> False

countL3For :: Exp3 -> Int
countL3For ex =
  case ex of
    VarE{} -> 0
    LitE{} -> 0
    CharE{} -> 0
    FloatE{} -> 0
    LitSymE{} -> 0
    AppE _ _ _ args -> sum (map countL3For args)
    PrimAppE _ args -> sum (map countL3For args)
    LetE (_, _, _, rhs) bod -> countL3For rhs + countL3For bod
    ProjE _ e -> countL3For e
    IfE a b c -> sum (map countL3For [a, b, c])
    MkProdE ls -> sum (map countL3For ls)
    CaseE scrt brs -> countL3For scrt + sum (map (countL3For . (\(_, _, rhs) -> rhs)) brs)
    DataConE _ _ args -> sum (map countL3For args)
    TimeIt e _ _ -> countL3For e
    WithArenaE _ e -> countL3For e
    SpawnE _ _ args -> sum (map countL3For args)
    SyncE -> 0
    MapE (_, _, e1) e2 -> countL3For e1 + countL3For e2
    FoldE (_, _, e1) (_, _, e2) e3 -> sum (map countL3For [e1, e2, e3])
    Ext (ForE _ bound bod) -> 1 + countL3For bound + countL3For bod
    Ext (WhileCursor _ bod) -> countL3For bod
    Ext (WriteScalar _ _ rhs) -> countL3For rhs
    Ext (WriteTaggedCursor _ rhs) -> countL3For rhs
    Ext (WriteCursorMutable _ rhs) -> countL3For rhs
    Ext (WriteList _ rhs _) -> countL3For rhs
    Ext (WriteVector _ rhs _) -> countL3For rhs
    Ext (AddCursor _ rhs) -> countL3For rhs
    Ext (BumpCursorMutable _ rhs) -> countL3For rhs
    Ext (AddrOfCursor rhs) -> countL3For rhs
    Ext (LetAvail _ bod) -> countL3For bod
    Ext (Assert rhs) -> countL3For rhs
    Ext _ -> 0

containsScalarCountRead :: Exp3 -> Bool
containsScalarCountRead ex =
  case ex of
    LetE (_, _, _, rhs) bod -> containsScalarCountRead rhs || containsScalarCountRead bod
    IfE a b c -> any containsScalarCountRead [a, b, c]
    CaseE scrt brs -> containsScalarCountRead scrt || any (containsScalarCountRead . (\(_, _, rhs) -> rhs)) brs
    Ext ReadScalarCount{} -> True
    Ext ReadScalarCountFirstFooter{} -> True
    Ext ReadScalarCountNextFooter{} -> True
    Ext (ForE _ bound body) -> containsScalarCountRead bound || containsScalarCountRead body
    Ext (WhileCursor _ bod) -> containsScalarCountRead bod
    Ext (WriteScalar _ _ rhs) -> containsScalarCountRead rhs
    Ext (WriteTaggedCursor _ rhs) -> containsScalarCountRead rhs
    Ext (WriteCursorMutable _ rhs) -> containsScalarCountRead rhs
    Ext (WriteList _ rhs _) -> containsScalarCountRead rhs
    Ext (WriteVector _ rhs _) -> containsScalarCountRead rhs
    Ext (AddCursor _ rhs) -> containsScalarCountRead rhs
    Ext (BumpCursorMutable _ rhs) -> containsScalarCountRead rhs
    Ext (AddrOfCursor rhs) -> containsScalarCountRead rhs
    Ext (LetAvail _ bod) -> containsScalarCountRead bod
    Ext (Assert rhs) -> containsScalarCountRead rhs
    Ext _ -> False
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args -> any containsScalarCountRead args
    PrimAppE _ args -> any containsScalarCountRead args
    ProjE _ e -> containsScalarCountRead e
    MkProdE ls -> any containsScalarCountRead ls
    DataConE _ _ args -> any containsScalarCountRead args
    TimeIt e _ _ -> containsScalarCountRead e
    WithArenaE _ e -> containsScalarCountRead e
    SpawnE _ _ args -> any containsScalarCountRead args
    SyncE -> False
    MapE (_, _, e1) e2 -> containsScalarCountRead e1 || containsScalarCountRead e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any containsScalarCountRead [e1, e2, e3]

containsScalarCountWrite :: Exp3 -> Bool
containsScalarCountWrite ex =
  case ex of
    LetE (_, _, _, rhs) bod -> containsScalarCountWrite rhs || containsScalarCountWrite bod
    IfE a b c -> any containsScalarCountWrite [a, b, c]
    CaseE scrt brs -> containsScalarCountWrite scrt || any (containsScalarCountWrite . (\(_, _, rhs) -> rhs)) brs
    Ext ScalarCountBump{} -> True
    Ext ScalarCountSet{} -> True
    Ext (ForE _ bound body) -> containsScalarCountWrite bound || containsScalarCountWrite body
    Ext (WhileCursor _ bod) -> containsScalarCountWrite bod
    Ext (WriteScalar _ _ rhs) -> containsScalarCountWrite rhs
    Ext (WriteTaggedCursor _ rhs) -> containsScalarCountWrite rhs
    Ext (WriteCursorMutable _ rhs) -> containsScalarCountWrite rhs
    Ext (WriteList _ rhs _) -> containsScalarCountWrite rhs
    Ext (WriteVector _ rhs _) -> containsScalarCountWrite rhs
    Ext (AddCursor _ rhs) -> containsScalarCountWrite rhs
    Ext (BumpCursorMutable _ rhs) -> containsScalarCountWrite rhs
    Ext (AddrOfCursor rhs) -> containsScalarCountWrite rhs
    Ext (LetAvail _ bod) -> containsScalarCountWrite bod
    Ext (Assert rhs) -> containsScalarCountWrite rhs
    Ext _ -> False
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args -> any containsScalarCountWrite args
    PrimAppE _ args -> any containsScalarCountWrite args
    ProjE _ e -> containsScalarCountWrite e
    MkProdE ls -> any containsScalarCountWrite ls
    DataConE _ _ args -> any containsScalarCountWrite args
    TimeIt e _ _ -> containsScalarCountWrite e
    WithArenaE _ e -> containsScalarCountWrite e
    SpawnE _ _ args -> any containsScalarCountWrite args
    SyncE -> False
    MapE (_, _, e1) e2 -> containsScalarCountWrite e1 || containsScalarCountWrite e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any containsScalarCountWrite [e1, e2, e3]

containsL3WhileCursor :: Exp3 -> Bool
containsL3WhileCursor ex =
  case ex of
    LetE (_, _, _, rhs) bod -> containsL3WhileCursor rhs || containsL3WhileCursor bod
    IfE a b c -> any containsL3WhileCursor [a, b, c]
    CaseE scrt brs -> containsL3WhileCursor scrt || any (containsL3WhileCursor . (\(_, _, rhs) -> rhs)) brs
    Ext (WhileCursor _ _) -> True
    Ext (ForE _ bound body) -> containsL3WhileCursor bound || containsL3WhileCursor body
    Ext (WriteScalar _ _ rhs) -> containsL3WhileCursor rhs
    Ext (WriteTaggedCursor _ rhs) -> containsL3WhileCursor rhs
    Ext (WriteCursorMutable _ rhs) -> containsL3WhileCursor rhs
    Ext (WriteList _ rhs _) -> containsL3WhileCursor rhs
    Ext (WriteVector _ rhs _) -> containsL3WhileCursor rhs
    Ext (AddCursor _ rhs) -> containsL3WhileCursor rhs
    Ext (BumpCursorMutable _ rhs) -> containsL3WhileCursor rhs
    Ext (AddrOfCursor rhs) -> containsL3WhileCursor rhs
    Ext (LetAvail _ bod) -> containsL3WhileCursor bod
    Ext (Assert rhs) -> containsL3WhileCursor rhs
    Ext _ -> False
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args -> any containsL3WhileCursor args
    PrimAppE _ args -> any containsL3WhileCursor args
    ProjE _ e -> containsL3WhileCursor e
    MkProdE ls -> any containsL3WhileCursor ls
    DataConE _ _ args -> any containsL3WhileCursor args
    TimeIt e _ _ -> containsL3WhileCursor e
    WithArenaE _ e -> containsL3WhileCursor e
    SpawnE _ _ args -> any containsL3WhileCursor args
    SyncE -> False
    MapE (_, _, e1) e2 -> containsL3WhileCursor e1 || containsL3WhileCursor e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any containsL3WhileCursor [e1, e2, e3]

containsWriteTagPacked :: Exp3 -> Bool
containsWriteTagPacked ex =
  case ex of
    LetE (_, _, _, rhs) bod -> containsWriteTagPacked rhs || containsWriteTagPacked bod
    IfE a b c -> any containsWriteTagPacked [a, b, c]
    CaseE scrt brs -> containsWriteTagPacked scrt || any (containsWriteTagPacked . (\(_, _, rhs) -> rhs)) brs
    Ext (WriteTagPacked _ rhs) -> containsWriteTagPacked rhs || True
    Ext (ForE _ bound body) -> containsWriteTagPacked bound || containsWriteTagPacked body
    Ext (WhileCursor _ bod) -> containsWriteTagPacked bod
    Ext (WriteScalar _ _ rhs) -> containsWriteTagPacked rhs
    Ext (WriteTaggedCursor _ rhs) -> containsWriteTagPacked rhs
    Ext (WriteCursorMutable _ rhs) -> containsWriteTagPacked rhs
    Ext (WriteList _ rhs _) -> containsWriteTagPacked rhs
    Ext (WriteVector _ rhs _) -> containsWriteTagPacked rhs
    Ext (AddCursor _ rhs) -> containsWriteTagPacked rhs
    Ext (BumpCursorMutable _ rhs) -> containsWriteTagPacked rhs
    Ext (AddrOfCursor rhs) -> containsWriteTagPacked rhs
    Ext (LetAvail _ bod) -> containsWriteTagPacked bod
    Ext (Assert rhs) -> containsWriteTagPacked rhs
    Ext _ -> False
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args -> any containsWriteTagPacked args
    PrimAppE _ args -> any containsWriteTagPacked args
    ProjE _ e -> containsWriteTagPacked e
    MkProdE ls -> any containsWriteTagPacked ls
    DataConE _ _ args -> any containsWriteTagPacked args
    TimeIt e _ _ -> containsWriteTagPacked e
    WithArenaE _ e -> containsWriteTagPacked e
    SpawnE _ _ args -> any containsWriteTagPacked args
    SyncE -> False
    MapE (_, _, e1) e2 -> containsWriteTagPacked e1 || containsWriteTagPacked e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any containsWriteTagPacked [e1, e2, e3]

case_detects_fully_factored_may_vectorize_candidate :: Assertion
case_detects_fully_factored_may_vectorize_candidate =
  let prg = listProg FullyFactored [MayVectorize]
      fd = (fundefs prg) M.! "add1List"
   in Just (LoopifyCandidate "add1List" "List" ["Nil", "Cons"]) @=?
        loopifyCandidateInfo (ddefs prg) fd

case_requires_annotation :: Assertion
case_requires_annotation =
  let prg = listProg FullyFactored []
      fd = (fundefs prg) M.! "add1List"
   in Nothing @=? loopifyCandidateInfo (ddefs prg) fd

case_auto_detection_allows_unannotated_candidate :: Assertion
case_auto_detection_allows_unannotated_candidate =
  let prg = listProg FullyFactored []
      fd = (fundefs prg) M.! "add1List"
   in Just (LoopifyCandidate "add1List" "List" ["Nil", "Cons"]) @=?
        loopifyCandidateInfoWith True (ddefs prg) fd

case_auto_detection_skips_generated_packed_helpers :: Assertion
case_auto_detection_skips_generated_packed_helpers =
  let fd0 = cursorizedMutableLoopifyFun
      fd = fd0 { funName = "_copy_List", funMeta = (funMeta fd0) { funOpt = [] } }
      prg = Prog (M.fromList [("List", cursorizedListDDef)]) (M.fromList [("_copy_List", fd)]) Nothing
   in Nothing @=? loopifyCandidateInfoWith True (ddefs prg) fd

case_auto_loopification_rewrites_unannotated_cursorized_fast_path :: Assertion
case_auto_loopification_rewrites_unannotated_cursorized_fast_path =
  let prg = withCountedProducer "List" (withoutFunOpts "fastAdd1ListMut" cursorizedMutableLoopifyProg)
      Prog {fundefs = fds} = runnerWithCountsAuto prg
      fd = fds M.! "fastAdd1ListMut"
   in do
        assertBool "expected auto loopification to emit ForE" (containsL3For (funBody fd))
        assertBool "expected auto loopification to stamp Loopified metadata" (Loopified `elem` funOpt (funMeta fd))

case_auto_loopification_requires_counted_producer :: Assertion
case_auto_loopification_requires_counted_producer =
  let Prog {fundefs = fds} = runnerWithCountsAuto (withoutFunOpts "fastAdd1ListMut" cursorizedMutableLoopifyProg)
      fd = fds M.! "fastAdd1ListMut"
   in assertBool
        "expected auto loopification to stay recursive without scalar-count producer metadata"
        (not (containsL3For (funBody fd)))

case_requires_fully_factored_layout :: Assertion
case_requires_fully_factored_layout =
  let prg = listProg Linear [MayVectorize]
      fd = (fundefs prg) M.! "add1List"
   in Nothing @=? loopifyCandidateInfo (ddefs prg) fd

case_rejects_mixed_tycons :: Assertion
case_rejects_mixed_tycons =
  let fd = (fundefs mixedProg) M.! "mix"
   in Nothing @=? loopifyCandidateInfo (ddefs mixedProg) fd

case_first_milestone_is_identity :: Assertion
case_first_milestone_is_identity =
  let prg = listProg FullyFactored [MayVectorize]
   in prg @=? runner prg

case_rewrites_supported_cursorized_fast_path :: Assertion
case_rewrites_supported_cursorized_fast_path =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "List" cursorizedLoopifyProg)
      fd = fds M.! "fastAdd1List"
   in do
        assertBool "expected loopified fast path to contain ForE" (containsL3For (funBody fd))
        assertBool "expected loopified fast path to read scalar-count metadata" (containsScalarCountRead (funBody fd))
        assertBool "expected loopified fast path to copy dcon tags from input" (containsWriteTagPacked (funBody fd))

case_rewrites_supported_mutable_cursorized_fast_path :: Assertion
case_rewrites_supported_mutable_cursorized_fast_path =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "List" cursorizedMutableLoopifyProg)
      fd = fds M.! "fastAdd1ListMut"
  in do
        assertBool "expected mutable loopified fast path to contain ForE" (containsL3For (funBody fd))
        3 @=? countL3For (funBody fd)
        assertBool "expected mutable loopified fast path to contain WhileCursor" (containsL3WhileCursor (funBody fd))
        assertBool "expected mutable loopified fast path to read scalar-count metadata" (containsScalarCountRead (funBody fd))
        assertBool "expected mutable loopified fast path to write scalar-count metadata" (containsScalarCountWrite (funBody fd))
        assertBool "expected mutable loopified fast path to copy dcon tags from input" (containsWriteTagPacked (funBody fd))

case_can_disable_scalar_loop_fusion :: Assertion
case_can_disable_scalar_loop_fusion =
  let Prog {fundefs = fds} = runnerWithCountsNoFusion (withCountedProducer "List" cursorizedMutableLoopifyProg)
      fd = fds M.! "fastAdd1ListMut"
   in do
        assertBool "expected mutable loopified fast path to still contain ForE" (containsL3For (funBody fd))
        3 @=? countL3For (funBody fd)
        assertBool "expected mutable loopified fast path to still read scalar-count metadata" (containsScalarCountRead (funBody fd))

case_post_selective_loop_fusion_fuses_scalar_loops :: Assertion
case_post_selective_loop_fusion_fuses_scalar_loops =
  let Prog {fundefs = fds} = runnerWithCountsThenFusion (withCountedProducer "List" cursorizedMutableLoopifyProg)
      fd = fds M.! "fastAdd1ListMut"
   in do
        assertBool "expected post-selective loop fusion to preserve ForE loops" (containsL3For (funBody fd))
        2 @=? countL3For (funBody fd)

case_rewrites_mutable_fast_path_with_extra_cursor_array_argument :: Assertion
case_rewrites_mutable_fast_path_with_extra_cursor_array_argument =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "List" cursorizedMutableLoopifyExtraCursorProg)
      fd = fds M.! "fastAdd1ListMutExtra"
   in do
        assertBool "expected extra cursor-array argument not to block loopification" (containsL3For (funBody fd))
        assertBool "expected loopified fast path to read scalar-count metadata" (containsScalarCountRead (funBody fd))

case_detects_parent_child_dependency_in_primitive_rhs :: Assertion
case_detects_parent_child_dependency_in_primitive_rhs =
  let body =
        LetE
          ("child_sum", [], IntTy W64, AppE "sumList" TailModuloCons [] [VarE "inEnds", VarE "outEnds", VarE "outCurs", VarE "inCurs"])
          (LetE
             ("total", [], IntTy W64, PrimAppE addP64 [VarE "child_sum", mkLitE64 1])
             (VarE "total"))
   in assertBool "expected primitive use of child result to be rejected" $
        hasParentChildDependency "sumList" body

case_rejects_parent_child_dependent_traversal :: Assertion
case_rejects_parent_child_dependent_traversal =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "List" cursorizedMutableParentChildDependentProg)
      fd = fds M.! "badParentChildMut"
   in assertBool
        "expected parent-child dependent traversal to remain recursive"
        (not (containsL3For (funBody fd)))

case_rewrites_supported_mutable_tree_fast_path :: Assertion
case_rewrites_supported_mutable_tree_fast_path =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "Tree" cursorizedMutableTreeLoopifyProg)
      fd = fds M.! "fastAdd1TreeMut"
  in do
        assertBool "expected mutable tree loopified fast path to contain ForE" (containsL3For (funBody fd))
        assertBool "expected mutable tree loopified fast path to contain WhileCursor" (containsL3WhileCursor (funBody fd))
        assertBool "expected mutable tree loopified fast path to read scalar-count metadata" (containsScalarCountRead (funBody fd))
        assertBool "expected mutable tree loopified fast path to write scalar-count metadata" (containsScalarCountWrite (funBody fd))
        assertBool "expected mutable tree loopified fast path to copy dcon tags from input" (containsWriteTagPacked (funBody fd))

case_rewrites_realistic_mutable_cursorized_fast_path :: Assertion
case_rewrites_realistic_mutable_cursorized_fast_path =
  let Prog {fundefs = fds} = runnerWithCounts (withCountedProducer "List" cursorizedRealisticMutableLoopifyProg)
      fd = fds M.! "fastAdd1ListRealisticMut"
   in do
        assertBool "expected realistic mutable loopified fast path to contain ForE" (containsL3For (funBody fd))
        assertBool "expected realistic mutable loopified fast path to contain WhileCursor" (containsL3WhileCursor (funBody fd))
        assertBool "expected realistic mutable loopified fast path to read scalar-count metadata" (containsScalarCountRead (funBody fd))
        assertBool "expected realistic mutable loopified fast path to copy dcon tags from input" (containsWriteTagPacked (funBody fd))

case_lower_supports_footer_counts_and_for_loops :: Assertion
case_lower_supports_footer_counts_and_for_loops =
  let T.Prog {T.fundefs = [fd]} = runLowering loopIrProg
      prims = collectTailPrims (T.funBody fd)
   in do
        assertBool "expected scalar-count get primitive" (T.ScalarCountGet `elem` prims)
        assertBool "expected first-footer primitive" (T.ScalarCountFirstFooter `elem` prims)
        assertBool "expected next-footer primitive" (T.ScalarCountNextFooter `elem` prims)
        assertBool "expected lowered for-loop tail" (containsForLoop (T.funBody fd))

-- | Invariant: a binding created for an `IfE` arm stays inside
-- that arm.  Before the fix, `anfScalarExpr` returned the condition's, the
-- then-arm's and the else-arm's bindings CONCATENATED to a caller that spliced
-- them above the `IfE`, so `if i == 0 then 7 else 100 / i` evaluated the
-- division for every element -- a division by zero on exactly the elements the
-- guard existed to exclude.
case_guarded_division_stays_inside_its_arm :: Assertion
case_guarded_division_stays_inside_its_arm =
  let body = loopifiedGuardedBody guardedDivRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "expected the traversal to be loopified" (containsL3For body)
        assertEqual "no partial binding may sit outside the conditional" [] outside
        assertEqual "the division must be bound inside the arm" 1 (length inside)

-- Nested conditionals must keep their nesting AND their bindings: each of the
-- two divisions belongs to its own inner arm.
case_nested_guards_keep_their_own_bindings :: Assertion
case_nested_guards_keep_their_own_bindings =
  let body = loopifiedGuardedBody nestedGuardedDivRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "expected the traversal to be loopified" (containsL3For body)
        assertEqual "no partial binding may sit outside the conditionals" [] outside
        assertEqual "both divisions must be bound inside their arms" 2 (length inside)

-- A chain of dependent temporaries in one arm: `100 / (i * 2)` ANFs to two
-- bindings, and BOTH must stay in the arm -- lifting only the outermost would
-- still evaluate the multiply unconditionally.
case_chained_arm_bindings_stay_inside :: Assertion
case_chained_arm_bindings_stay_inside =
  let body = loopifiedGuardedBody chainedGuardedDivRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "expected the traversal to be loopified" (containsL3For body)
        assertEqual "no partial binding may sit outside the conditional" [] outside
        assertEqual "the division must be bound inside the arm" 1 (length inside)

-- Branch-local bindings must not collide: the fresh counter still threads
-- through the condition and both arms even though they are now separate scopes.
-- Branch-local bindings must not collide.  The bindings ANF creates now live in
-- separate scopes (condition, then-arm, else-arm), so a counter that restarted
-- per branch would produce two `anf0`s; the counter still threads through all
-- three, and this pins that.
--
-- Scoped to the ANF-generated names on purpose: an ordinary Gibbon program
-- legitimately reuses a binder name in disjoint scopes (the Nil and Cons
-- branches, the fast and general paths), so asserting global uniqueness over
-- every binder would fail for reasons that have nothing to do with this fix.
case_branch_local_binders_are_unique :: Assertion
case_branch_local_binders_are_unique =
  sequence_
    [ let anfs = [ v | v <- allLetBinders (loopifiedGuardedBody rhs)
                     , "anf" `L.isInfixOf` fromVar v ]
      in do assertBool (lbl ++ ": expected ANF bindings to exist") (not (null anfs))
            assertEqual (lbl ++ ": every ANF binder must be distinct")
                        (length anfs) (length (L.nub anfs))
    | (lbl, rhs) <- [ ("guarded", guardedDivRhs)
                    , ("nested", nestedGuardedDivRhs)
                    , ("chained", chainedGuardedDivRhs)
                    , ("total", totalCondRhs) ]
    ]

-- The fix must not be "refuse to loopify conditionals": a TOTAL conditional
-- still loopifies, and has no partial binding anywhere to place.
case_total_conditional_still_loopifies :: Assertion
case_total_conditional_still_loopifies =
  let body = loopifiedGuardedBody totalCondRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "a total conditional must still loopify" (containsL3For body)
        assertEqual "a total conditional has no partial bindings" ([], []) (inside, outside)

-- | Loopify, then vectorize, exactly as the production pipeline does.
vectorizedGuardedBody :: Exp3 -> Exp3
vectorizedGuardedBody rhs =
  -- Loop fusion runs between loopification and vectorization in the real
  -- pipeline, and the vectorizer matches the FUSED unit-valued loop body, so
  -- leaving it out here would make every one of these tests report "did not
  -- vectorize" for the wrong reason.
  let cfg = defaultConfig
              {dynflags = gopt_set Opt_EnableVectorization
                            (gopt_set Opt_EnableLoopFusion loopifyDFlags)}
      (prg', _) =
        runPassM cfg 0
          (loopifyTraversals (guardedProg rhs)
             >>= fuseLoopifiedTraversals
             >>= vectorizeTraversals)
      Prog{fundefs = fds} = prg'
  in funBody (fds M.! "fastAdd1ListMut")

-- | Names of the L3 vector extension nodes present, as rendered constructor
-- tags.  Structural enough for "did this loop vectorize, and with what".
vecNodeCount :: String -> Exp3 -> Int
vecNodeCount tag ex = length (filter (L.isPrefixOf tag) (L.tails (show ex)))

-- A guarded partial operation must NOT be speculated into a vector select.
--
-- This is the half of the fix that could regress silently: `matchScalarDag` now
-- looks THROUGH the branch-local administrative lets the loopifier emits, and
-- if that transparency were applied without the partial-operation check still
-- seeing the division underneath, the loop would vectorize both arms and
-- divide by zero for every element -- the original bug, moved one pass later.
case_guarded_partial_does_not_vectorize :: Assertion
case_guarded_partial_does_not_vectorize =
  let body = vectorizedGuardedBody guardedDivRhs
   in do
        assertEqual "a guarded division must not become a packed divide"
                    0 (vecNodeCount "VecDiv" body)
        assertEqual "a guarded division must not become a packed select"
                    0 (vecNodeCount "VecSelect" body)
        assertBool "the loop itself must still be loopified" (containsL3For body)

case_guarded_nested_partial_does_not_vectorize :: Assertion
case_guarded_nested_partial_does_not_vectorize =
  let body = vectorizedGuardedBody nestedGuardedDivRhs
   in do
        assertEqual "nested guarded divisions must not become packed divides"
                    0 (vecNodeCount "VecDiv" body)
        assertEqual "nested guarded divisions must not become packed selects"
                    0 (vecNodeCount "VecSelect" body)

-- ...while a TOTAL conditional still becomes a comparison mask plus a select.
-- The fix for guarded partial operations must not regress to "stop
-- vectorizing conditionals" -- total conditionals must keep vectorizing.
case_total_conditional_still_vectorizes :: Assertion
case_total_conditional_still_vectorizes =
  let body = vectorizedGuardedBody totalCondRhs
   in do
        assertBool "a total conditional must still produce a packed select"
                   (vecNodeCount "VecSelect" body > 0)
        assertBool "a total conditional must still produce a packed comparison"
                   (vecNodeCount "VecCmp" body > 0)

-- 'ErrorP' is a terminating effect, so it must never be speculated into a
-- vector select.  The guarantee comes from the LOOPIFIER, not the vectorizer:
-- 'primEffectClass' classifies `ErrorP` as 'EffUnsupported', so the traversal
-- is never loopified and there is no loop for the vectorizer to be shown.
--
-- Asserting only "no packed operation appears" would hold for any function the
-- loopifier declined, for any reason at all, so the absence of a loop is
-- asserted too -- that is where the guarantee actually is.
case_error_prim_keeps_the_loop_scalar :: Assertion
case_error_prim_keeps_the_loop_scalar =
  let rhs = IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
                (PrimAppE (ErrorP "boom" (IntTy W64)) [])
                (VarE "i")
      body = vectorizedGuardedBody rhs
   in do
        EffUnsupported @=? primEffectClass (ErrorP "boom" (IntTy W64) :: Prim Ty3)
        assertBool "an ErrorP body must not be loopified at all"
                   (not (containsL3For body))
        assertEqual "ErrorP must never be speculated into a select"
                    0 (vecNodeCount "VecSelect" body)
        assertEqual "ErrorP must not become any packed operation"
                    0 (vecNodeCount "VecAdd" body + vecNodeCount "VecDiv" body)

--------------------------------------------------------------------------------
-- Scoped LetE in loopifiable scalar expressions
--------------------------------------------------------------------------------

-- @if i == 0 then 7 else (let y = 100 / i in y + 1)@ -- a guarded partial
-- operation behind a let INSIDE the arm.  Both the binding and the division
-- must stay in that arm.
letPartialInArmRhs :: Exp3
letPartialInArmRhs =
  IfE (PrimAppE eqIntP64 [VarE "i", mkLitE64 0])
      (mkLitE64 7)
      (LetE ("y_arm", [], IntTy W64, PrimAppE divP64 [mkLitE64 100, VarE "i"])
            (PrimAppE addP64 [VarE "y_arm", mkLitE64 1]))

-- A chain of dependent lets, ending in a division whose divisor is 2*i.
letChainRhs :: Exp3
letChainRhs =
  LetE ("a_c", [], IntTy W64, PrimAppE mulP64 [VarE "i", mkLitE64 2])
    (LetE ("b_c", [], IntTy W64, PrimAppE addP64 [VarE "a_c", VarE "i"])
      (LetE ("c_c", [], IntTy W64, PrimAppE subP64 [VarE "b_c", VarE "i"])
        (PrimAppE addP64 [VarE "c_c", mkLitE64 1])))

-- A let-bound value referenced TWICE, whose RHS is partial.  Inlining it would
-- perform two divisions where the source performs one.
multiUsePartialRhs :: Exp3
multiUsePartialRhs =
  LetE ("q_m", [], IntTy W64, PrimAppE divP64 [mkLitE64 100, VarE "i"])
       (PrimAppE addP64 [VarE "q_m", VarE "q_m"])

-- A strict binding whose RHS traps and whose value is never used.
unusedTrappingRhs :: Exp3
unusedTrappingRhs =
  LetE ("dead_t", [], IntTy W64, PrimAppE divP64 [mkLitE64 100, VarE "i"])
       (mkLitE64 7)

-- Same shape, but the dead binding is total: dropping it is unobservable.
unusedTotalRhs :: Exp3
unusedTotalRhs =
  LetE ("dead_ok", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
       (mkLitE64 7)

-- A total multi-let conditional: no partial operation anywhere.
totalMultiLetCondRhs :: Exp3
totalMultiLetCondRhs =
  LetE ("t0", [], IntTy W64, PrimAppE addP64 [VarE "i", mkLitE64 1])
    (IfE (PrimAppE eqIntP64 [VarE "t0", mkLitE64 0])
         -- add, not multiply: this fixture exists to exercise the
         -- CONDITIONAL (packed select) path, and W64 multiply is deliberately
         -- not SIMD-capable, so a multiply here would make the loop stay
         -- scalar and the test would be asserting nothing.
         (LetE ("t1", [], IntTy W64, PrimAppE addP64 [VarE "t0", mkLitE64 3])
               (PrimAppE addP64 [VarE "t1", mkLitE64 2]))
         (PrimAppE subP64 [VarE "t0", mkLitE64 1]))

-- An unsupported effectful primitive inside an otherwise fine scalar shape.
errorInLetRhs :: Exp3
errorInLetRhs =
  LetE ("e_v", [], IntTy W64, PrimAppE (ErrorP "boom" (IntTy W64)) [])
       (PrimAppE addP64 [VarE "e_v", mkLitE64 1])

-- | Look up the type recorded for a binder in the loopified body.
binderTypeIn :: Var -> Exp3 -> Maybe Ty3
binderTypeIn want = go
  where
    go ex =
      case ex of
        LetE (v, _, ty, rhs) bod
          | v == want -> Just ty
          | otherwise -> go rhs `orElse` go bod
        IfE a b c -> foldr (orElse . go) Nothing [a, b, c]
        PrimAppE _ args -> foldr (orElse . go) Nothing args
        AppE _ _ _ args -> foldr (orElse . go) Nothing args
        ProjE _ e -> go e
        MkProdE es -> foldr (orElse . go) Nothing es
        CaseE scrt brs -> foldr (orElse . go) Nothing (scrt : [ r | (_, _, r) <- brs ])
        Ext (ForE _ bound bod) -> go bound `orElse` go bod
        Ext (WhileCursor _ bod) -> go bod
        Ext (WriteScalar _ _ rhs) -> go rhs
        Ext (LetAvail _ bod) -> go bod
        _ -> Nothing
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | Occurrences of a rendered constructor tag, e.g. "DivP".
tagCount :: String -> Exp3 -> Int
tagCount tag ex = length (filter (L.isPrefixOf tag) (L.tails (show ex)))

-- A `let` written inside a conditional arm must stay inside it, exactly as a
-- bare operation does.  Before scoped-let support, the arm's `LetE` was
-- rejected by the scalar-expression grammar and the traversal was never
-- loopified at all.
case_arm_local_let_stays_in_its_arm :: Assertion
case_arm_local_let_stays_in_its_arm =
  let body = loopifiedGuardedBody letPartialInArmRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "a let-bearing arm must now loopify" (containsL3For body)
        assertEqual "no partial binding may sit outside the conditional" [] outside
        assertEqual "the division must be bound inside the arm" 1 (length inside)
        assertEqual "the division must appear exactly once" 1 (tagCount "DivP" body)

-- A dependent chain keeps its order and each binder keeps its declared type.
case_let_chain_keeps_order_and_types :: Assertion
case_let_chain_keeps_order_and_types =
  let body = loopifiedGuardedBody letChainRhs
      binders = allLetBinders body
      positionOf v = L.elemIndex v binders
   in do
        assertBool "a dependent let chain must loopify" (containsL3For body)
        assertEqual "binder a_c keeps its type" (Just (IntTy W64)) (binderTypeIn "a_c" body)
        assertEqual "binder b_c keeps its type" (Just (IntTy W64)) (binderTypeIn "b_c" body)
        assertEqual "binder c_c keeps its type" (Just (IntTy W64)) (binderTypeIn "c_c" body)
        assertBool "a_c must be bound before b_c" (positionOf "a_c" < positionOf "b_c")
        assertBool "b_c must be bound before c_c" (positionOf "b_c" < positionOf "c_c")
        -- Each source operation appears exactly once: nothing was duplicated by
        -- substituting a binding at its uses.
        assertEqual "one multiply" 1 (tagCount "MulP" body)

-- A non-trivial RHS referenced twice must not be evaluated twice.  Either the
-- binding survives as a binding (one division), or the traversal stays scalar.
case_multi_use_partial_is_not_duplicated :: Assertion
case_multi_use_partial_is_not_duplicated =
  let body = loopifiedGuardedBody multiUsePartialRhs
   in if containsL3For body
      then assertEqual "a shared division must not be duplicated"
                       1 (tagCount "DivP" body)
      else assertEqual "if it did not loopify, no division may have leaked in"
                       0 (tagCount "DivP" body)

-- A multiply-used partial that already loopified must be undisturbed.
--
-- Measured: this fixture loopifies with the flag off too, because the whole
-- `let` is a single write's right-hand side and the 'ScalarExpr' grammar
-- admits `LetE` directly -- it never reaches the environment/residual decision
-- the flag changes.  (An earlier reading of this test had it staying scalar by
-- default; it does not.  'sharedPartialProg' is the fixture that actually
-- exercises the shared-across-writes path.)  What matters here is that the
-- division is still bound once and not duplicated.
case_multi_use_partial_loopifies :: Assertion
case_multi_use_partial_loopifies =
  let body = loopifiedGuardedBody multiUsePartialRhs
   in do
        assertBool "a multiply-used partial must loopify under the flag"
                   (containsL3For body)
        assertEqual "and the division must not be duplicated within the plan"
                    1 (tagCount "DivP" body)

-- ...and without the flag it must still refuse, so the flag is what changed
-- the outcome rather than something else drifting.
-- THE case this handles: a partial bound on the branch body's spine and
-- consumed by TWO scalar writes, so it has to cross plan boundaries.
--
-- Note this is NOT what 'multiUsePartialRhs' tests.  There the whole `let` is a
-- single write's right-hand side, which the 'ScalarExpr' grammar admits
-- directly, so it loopifies with or without the flag.  Only a binding shared
-- BETWEEN writes goes through the environment/residual decision.
case_shared_partial_loopifies :: Assertion
case_shared_partial_loopifies =
  let Prog{fundefs = fds} = runnerWithCounts sharedPartialProg
      body = funBody (fds M.! "fastAdd1ListMut")
   in do
        assertEqual "it must loopify: one loop per buffer (dcon, int, float)"
                    3 (countL3For body)
        -- Two consuming plans, and production emits one loop per scalar buffer
        -- with no shared per-element scope, so the division is evaluated once
        -- per consuming loop.  Pure, so the value is unchanged; and re-trapping
        -- is indistinguishable from trapping once.  Pinned here so the cost is
        -- a decision on record rather than a surprise.
        assertEqual "recomputed once per consuming plan, not more"
                    2 (tagCount "DivP" body)

-- The residual must dominate the conditional write, not sit inside an arm:
-- the source evaluated it unconditionally, so skipping it on one branch would
-- skip a trap the source would have taken.
case_shared_partial_dominates_the_conditional_write :: Assertion
case_shared_partial_dominates_the_conditional_write =
  let Prog{fundefs = fds} = runnerWithCounts sharedPartialProg
      body = funBody (fds M.! "fastAdd1ListMut")
      (inside, _outside) = partialBindingSites body
   in assertEqual "no part of the shared division may be bound inside an arm"
                  [] inside

-- A partial the source GUARDED must never be promoted.
--
-- This is the whole safety argument: only bindings on the branch body's
-- unconditional spine are promoted.  Hoisting a guarded division above its
-- guard would make it trap on elements the source never divided -- the logged
-- `if d == 0 then 7 else 100 / d` regression.
case_guarded_partial_is_never_hoisted :: Assertion
case_guarded_partial_is_never_hoisted =
  let body = loopifiedGuardedBody letPartialInArmRhs
      (inside, outside) = partialBindingSites body
   in do
        assertEqual "no partial binding may sit outside the conditional" [] outside
        assertEqual "the division must stay bound inside the arm" 1 (length inside)
        assertEqual "and appear exactly once" 1 (tagCount "DivP" body)

-- A dead trapping binding must STILL block loopification under the flag: the
-- synthesized loop reproduces only the plans, so the trap would vanish.
case_dead_trap_is_never_resurrected :: Assertion
case_dead_trap_is_never_resurrected =
  let body = loopifiedGuardedBody unusedTrappingRhs
   in assertBool "a dropped trapping computation must still block loopification"
                 (not (containsL3For body))

-- Gibbon's `let` is strict.  A dead binding whose RHS traps must not be dropped:
-- the synthesized loop reproduces only the extracted plans, so such a branch
-- must not be loopified at all.
case_unused_trapping_binding_is_not_dropped :: Assertion
case_unused_trapping_binding_is_not_dropped =
  let body = loopifiedGuardedBody unusedTrappingRhs
   in assertBool "a branch that would drop a trapping computation must stay scalar"
                 (not (containsL3For body))

-- ...while a dead TOTAL binding is unobservable, so it must not block the
-- optimization.  Without this control, the guard above could be satisfied by
-- refusing to loopify anything with an unused binding.
case_unused_total_binding_still_loopifies :: Assertion
case_unused_total_binding_still_loopifies =
  let body = loopifiedGuardedBody unusedTotalRhs
   in assertBool "a dead total binding must not prevent loopification"
                 (containsL3For body)

-- An unclassified/effectful primitive must keep the traversal scalar rather
-- than being treated as arithmetic.  `ErrorP` used to pass the whitelist,
-- because it accepted any `PrimAppE`.
case_error_prim_blocks_loopification :: Assertion
case_error_prim_blocks_loopification =
  let body = loopifiedGuardedBody errorInLetRhs
   in assertBool "an effectful primitive must keep the traversal scalar"
                 (not (containsL3For body))

-- Total multi-let conditionals must both loopify and vectorize: admitting
-- `LetE` is pointless if the result stops being SIMD-eligible.
case_total_multi_let_conditional_loopifies :: Assertion
case_total_multi_let_conditional_loopifies =
  let body = loopifiedGuardedBody totalMultiLetCondRhs
      (inside, outside) = partialBindingSites body
   in do
        assertBool "a total multi-let conditional must loopify" (containsL3For body)
        assertEqual "it has no partial bindings" ([], []) (inside, outside)

case_total_multi_let_conditional_vectorizes :: Assertion
case_total_multi_let_conditional_vectorizes =
  let body = vectorizedGuardedBody totalMultiLetCondRhs
   in do
        assertBool "a total multi-let conditional must still produce a packed select"
                   (vecNodeCount "VecSelect" body > 0)
        assertEqual "and must not produce a packed divide"
                    0 (vecNodeCount "VecDiv" body)

-- Partial-operation detection must see through the newly admitted nested lets.
case_partial_behind_lets_does_not_vectorize :: Assertion
case_partial_behind_lets_does_not_vectorize =
  let body = vectorizedGuardedBody letPartialInArmRhs
   in do
        assertEqual "a guarded division behind a let must not become a packed divide"
                    0 (vecNodeCount "VecDiv" body)
        assertEqual "nor a packed select"
                    0 (vecNodeCount "VecSelect" body)

-- Binder names must remain distinct once source lets and ANF temporaries share
-- one block.
-- Admitting source `let`s puts source binders and ANF temporaries in the same
-- block, so check that no NEW collision appears.
--
-- Measured relative to a baseline shape rather than as absolute distinctness:
-- the surrounding generated program legitimately reuses a few binder names in
-- disjoint scopes (the Nil and Cons branches, the fast and general paths), so
-- an absolute assertion would fail for reasons unrelated to scoped-let
-- support.  What matters is that a let-bearing scalar expression adds none
-- of its own, and that no name under test is among the duplicates.
case_source_and_anf_binders_do_not_collide :: Assertion
case_source_and_anf_binders_do_not_collide =
  let dupsOf rhs = let bs = allLetBinders (loopifiedGuardedBody rhs)
                   in bs L.\\ L.nub bs
      baseline = dupsOf (PrimAppE addP64 [VarE "i", mkLitE64 1])
      underTest = ["y_arm", "a_c", "b_c", "c_c", "t0", "t1"]
   in sequence_
        [ do let ds = dupsOf rhs
             assertEqual (lbl ++ ": no binder duplicated beyond the baseline shape")
                         (length baseline) (length ds)
             assertBool (lbl ++ ": no source-let binder may be duplicated: " ++ show ds)
                        (not (any (`elem` underTest) ds))
             assertBool (lbl ++ ": no ANF temporary may be duplicated: " ++ show ds)
                        (not (any (L.isInfixOf "anf" . fromVar) ds))
        | (lbl, rhs) <- [ ("armLet", letPartialInArmRhs)
                        , ("chain", letChainRhs)
                        , ("totalMultiLet", totalMultiLetCondRhs) ]
        ]

-- The real shape of the dropped-effect defect: a branch computes something
-- trapping and never uses it.
--
-- Gibbon's `let` is strict, so the source program must divide by zero.  The
-- synthesized loop is built only from the extracted plans, so without this
-- check the binding would simply vanish -- the division would not appear in
-- the generated C at all, and the optimized program would print a number
-- where the unoptimized one exits 1.  A branch like this must stay scalar.
case_dead_sibling_trap_blocks_loopification :: Assertion
case_dead_sibling_trap_blocks_loopification =
  let body = loopifiedDeadSiblingBody (PrimAppE divP64 [mkLitE64 100, VarE "i"])
   in assertBool "a branch that would drop a trapping computation must stay scalar"
                 (not (containsL3For body))

case_dead_sibling_error_blocks_loopification :: Assertion
case_dead_sibling_error_blocks_loopification =
  let body = loopifiedDeadSiblingBody (PrimAppE (ErrorP "boom" (IntTy W64)) [])
   in assertBool "a branch that would drop an effectful computation must stay scalar"
                 (not (containsL3For body))

-- ...and the control: a dead TOTAL sibling binding is unobservable, so it must
-- not cost the optimization.
case_dead_sibling_total_still_loopifies :: Assertion
case_dead_sibling_total_still_loopifies =
  let body = loopifiedDeadSiblingBody (PrimAppE mulP64 [VarE "i", mkLitE64 3])
   in assertBool "a dead total binding must not prevent loopification"
                 (containsL3For body)


--------------------------------------------------------------------------------
-- VW-07: output-buffer capacity in synthesized chunk loops.
--
-- Loopification REMOVES the recursive function's per-node BoundsCheck and
-- replaces it with a per-output-buffer chunk discipline.  See
-- Note [Output capacity in synthesized chunk loops] in
-- "Gibbon.Passes.LoopifyTraversals".  These tests pin the replacement so it
-- cannot be dropped silently: the runtime byte accounting lives in
-- tests/vw07_output_capacity.sh, but a structural regression here fails fast.

-- | Every synthesized chunk loop must carry the COMPLETE mechanism: one
-- WhileCursor over the input chunk chain, one ScalarCountSet stamping the
-- output chunk footer, one GrowRegion for the chunk transition, and at least
-- one inner ForE doing the writes.  Dropping any one of them would leave writes
-- whose capacity nothing establishes.
case_vw07_chunk_loop_carries_full_capacity_mechanism :: Assertion
case_vw07_chunk_loop_carries_full_capacity_mechanism =
  let prg = withCountedProducer "List" cursorizedMutableLoopifyProg
      Prog {fundefs = fds} = runnerWithCounts prg
      body = funBody (fds M.! "fastAdd1ListMut")
      nWhile = countExt isWhileCursor' body
      nSet   = countExt isScalarCountSet' body
      nGrow  = countExt isGrowRegion' body
      nFor   = countExt isForE' body
   in do
        assertBool "expected loopification to fire at all" (nFor > 0 && nWhile > 0)
        assertEqual "one ScalarCountSet per chunk loop" nWhile nSet
        assertEqual "one GrowRegion per chunk loop" nWhile nGrow
        assertBool "each chunk loop needs at least one inner ForE"
                   (nFor >= nWhile)

-- | The other half of the invariant: a transformation may drop a BoundsCheck
-- only if it emits the replacement.  When loopification does NOT fire, any
-- check in the body must survive verbatim -- it must not be discarded merely
-- because 'classifyScalarShape' scores it as @bsUnit@ (zero writes).
case_vw07_bounds_check_survives_when_loopification_does_not_fire :: Assertion
case_vw07_bounds_check_survives_when_loopification_does_not_fire =
  let prg  = withoutFunOpts "fastAdd1ListMut" cursorizedMutableLoopifyProg
      fdIn = (fundefs prg) M.! "fastAdd1ListMut"
      guarded = fdIn { funBody = withBoundsCheck (funBody fdIn) }
      prg' = prg { fundefs = M.insert "fastAdd1ListMut" guarded (fundefs prg) }
      Prog {fundefs = fds} = runner prg'
      body = funBody (fds M.! "fastAdd1ListMut")
   in do
        assertBool "control: this configuration must not loopify"
                   (countExt isWhileCursor' body == 0)
        assertEqual "a BoundsCheck must not be dropped when nothing replaces it"
                    1 (countExt isBoundsCheckLike body)

-- | Wrap a body in a BoundsCheck, the way Cursorize emits one ahead of the
-- writes it protects.
withBoundsCheck :: Exp3 -> Exp3
withBoundsCheck bod =
  LetE ( "vw07_check", [], ProdTy []
       , Ext (BoundsCheck 26 "outEnds" "outCurs" Nothing Output))
       bod

--------------------------------------------------------------------------------
-- VW-09 / historical B22: which chunk loops may be fused.
--
-- 'Gibbon.Passes.LoopifiedTraversalFusion' gives ONE representative loop's
-- per-chunk trip count to every loop it fuses with.  See
-- Note [What makes fusing two chunk loops sound] there.  The relation it uses
-- is "same constructor key, parsed out of the generated loop variable's name,
-- and adjacent", so the encoding of that key carries a correctness obligation.
--
-- These tests drive the REAL fusion pass over chunk loops whose names come from
-- the REAL encoder, so a change to either is caught here.  The end-to-end
-- runtime evidence lives in tests/vw09_builder_counts.sh and
-- examples/vw09_fusion_skew.hs.

-- | A synthetic chunk loop in exactly the shape 'parseChunkLoop' accepts:
-- @WhileCursor cond (prefix.. ; ForE i bound body ; IfE c t e ; ())@.
--
-- @stride@ stands in for the buffer's element width, so two loops in one group
-- can differ in width the way an Int8 and an Int32 buffer of the same
-- constructor do.
fusionChunkLoop :: Var -> Int -> Maybe DataCon -> Int -> (Var, [()], Ty3, Exp3)
fusionChunkLoop seed ix mdcon stride =
    (loopVar, [], ProdTy [], Ext $ WhileCursor footerLoc chunkBody)
  where
    nm suffix = toVar (fromVar seed ++ "_buf" ++ show ix ++ "_" ++ suffix)
    loopVar = case mdcon of
                -- The dcon (tag) stream loop is named WITHOUT a _dcon_<k>_loop
                -- segment, which is how it stays out of every fusion group.
                Nothing   -> nm "loop"
                Just dcon -> nm ("dcon_" ++ sanitizeLoopName dcon ++ "_loop")
    footerLoc = nm "count_footer_loc"
    chunkBody =
      mkLets
        [ (nm "current_count_footer", [], CursorTy, Ext $ DerefMutCursor footerLoc)
        , (nm "chunk_count", [], IntTy W64, Ext $ ReadScalarCount (nm "current_count_footer"))
        , (nm "inner", [], ProdTy [], Ext $ ForE (nm "i") (VarE (nm "chunk_count"))
            (mkLets [ (nm "bump", [], ProdTy []
                      , Ext $ BumpCursorMutable (nm "out_loc") (mkLitE64 (fromIntegral stride))) ]
                    (MkProdE [])))
        , (nm "branch", [], ProdTy [], IfE (VarE (nm "is_last"))
                                            (MkProdE []) (MkProdE []))
        ]
        (MkProdE [])

-- | Run only the fusion pass over a function whose body is these loops.
fuseLoops :: [(Var, [()], Ty3, Exp3)] -> Exp3
fuseLoops binds =
    funBody (fds M.! "fuseProbe")
  where
    fn = FunDef "fuseProbe" [] ([], ProdTy []) (mkLets binds (MkProdE []))
                (FunMeta TailRec NoInline False [Loopified] Nothing)
    prg = Prog M.empty (M.fromList [("fuseProbe", fn)]) Nothing
    Prog{fundefs = fds} =
      fst $ runPassM (defaultConfig {dynflags = gopt_set Opt_EnableLoopFusion loopifyDFlags})
                     0 (fuseLoopifiedTraversals prg)

-- | The constructor key must be injective, because equal keys authorize giving
-- one loop's trip count to another.  Collapsing every non-alphanumeric
-- character to @_@ was not: @A'@ and @A_@ both became @A_@, and the fused loop
-- ran the @A_@ buffer for the number of @A'@ elements.
case_vw09_b22_constructor_key_is_injective :: Assertion
case_vw09_b22_constructor_key_is_injective =
  let dcons = [ "A", "A_", "A'", "A__", "A'_", "A_'", "Foo", "Foo_loop"
              , "X_dcon_Y", "Cons", "Cons'", "N1", "N_1" ]
      keys  = map sanitizeLoopName dcons
   in do
        assertEqual "distinct constructors must get distinct keys"
                    (length dcons) (length (L.nub keys))
        assertBool "keys must stay legal C identifier tails"
                   (all (all (\c -> isAlphaNumC c || c == '_')) keys)
        assertEqual "a purely alphanumeric name must encode to itself"
                    ["A", "Foo", "Cons", "N1"]
                    (map sanitizeLoopName ["A", "Foo", "Cons", "N1"])
  where
    isAlphaNumC c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')

-- | Two buffers of the SAME constructor have the same per-chunk element count,
-- so they may share a trip count -- including when their widths differ.
case_vw09_b22_same_constructor_buffers_fuse :: Assertion
case_vw09_b22_same_constructor_buffers_fuse =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 1 (Just "A") 1
                       , fusionChunkLoop "loop_1" 2 (Just "A") 4
                       ]
   in do
        assertEqual "two same-constructor loops must fuse into one"
                    1 (countExt isWhileCursor' body)
        assertEqual "and keep both inner loop bodies"
                    1 (countExt isForE' body)

case_vw09_b22_mixed_widths_do_not_block_fusion :: Assertion
case_vw09_b22_mixed_widths_do_not_block_fusion =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 1 (Just "N") 1
                       , fusionChunkLoop "loop_1" 2 (Just "N") 2
                       , fusionChunkLoop "loop_1" 3 (Just "N") 4
                       , fusionChunkLoop "loop_1" 4 (Just "N") 8
                       ]
   in assertEqual "W8/W16/W32/W64 buffers of one constructor must still fuse"
                  1 (countExt isWhileCursor' body)

-- | Different constructors have unrelated per-chunk counts.  This is the B22
-- miscompilation in structural form: before the key was made injective these
-- two names collided and the pass fused them.
case_vw09_b22_name_colliding_constructors_do_not_fuse :: Assertion
case_vw09_b22_name_colliding_constructors_do_not_fuse =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 1 (Just "A'") 8
                       , fusionChunkLoop "loop_1" 2 (Just "A_") 8
                       ]
   in assertEqual "A' and A_ are different constructors and must not fuse"
                  2 (countExt isWhileCursor' body)

case_vw09_b22_distinct_constructors_do_not_fuse :: Assertion
case_vw09_b22_distinct_constructors_do_not_fuse =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 1 (Just "N") 8
                       , fusionChunkLoop "loop_1" 2 (Just "S") 8
                       ]
   in assertEqual "loops for different constructors must stay separate"
                  2 (countExt isWhileCursor' body)

-- | The tag stream's footer count is the number of tags in the chunk, not any
-- one constructor's count, so it must never be substituted for a scalar
-- field's -- nor take one of theirs.
case_vw09_b22_tag_loop_never_joins_a_group :: Assertion
case_vw09_b22_tag_loop_never_joins_a_group =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 0 Nothing 1
                       , fusionChunkLoop "loop_1" 1 (Just "A") 1
                       , fusionChunkLoop "loop_1" 2 (Just "A") 4
                       ]
   in do
        assertEqual "the tag loop stays separate while A's two buffers fuse"
                    2 (countExt isWhileCursor' body)
        assertBool "the tag loop's own name must carry no constructor key"
                   (L.isSuffixOf "_buf0_loop"
                      (fromVar (fst4 (fusionChunkLoop "loop_1" 0 Nothing 1))))
  where fst4 (a, _, _, _) = a

-- | Adjacency is part of the relation: a group is a maximal run.  A different
-- constructor between two same-constructor loops must break the run rather
-- than be swallowed by it.
case_vw09_b22_interposed_constructor_breaks_the_group :: Assertion
case_vw09_b22_interposed_constructor_breaks_the_group =
  let body = fuseLoops [ fusionChunkLoop "loop_1" 1 (Just "A") 1
                       , fusionChunkLoop "loop_1" 2 (Just "B") 2
                       , fusionChunkLoop "loop_1" 3 (Just "A") 4
                       ]
   in assertEqual "three loops of two constructors must remain three loops"
                  3 (countExt isWhileCursor' body)

-- 'trulyInvariantArgs': both loopify passes read non-cursor arguments once,
-- at function entry, so a formal the recursion rebinds must not be reported
-- as loop invariant.  These pin the predicate directly; the pass-level
-- consequence is that such a formal's uses stay free and the candidate is
-- refused.

selfCall :: [Exp3] -> Exp3
selfCall args = AppE "self" NotTailRec [] args

-- | The shape every corpus map has: the traversal cursor descends to a child,
-- the scalar goes straight back in.  Only the scalar is invariant.
case_truly_invariant_accepts_pass_through :: Assertion
case_truly_invariant_accepts_pass_through =
  assertEqual "the scalar passed back as itself at every self-call is invariant"
              (S.fromList ["k"])
              (trulyInvariantArgs "self" ["cur", "k"]
                 (LetE ("r", [], ProdTy [], selfCall [VarE "child", VarE "k"])
                       (MkProdE [])))

-- | `depthMark t k = ... depthMark l (k+1) ...` after ANF: the self-call
-- passes a fresh binding, not the formal.
case_truly_invariant_rejects_rebound_arg :: Assertion
case_truly_invariant_rejects_rebound_arg =
  assertEqual "a formal the recursion rebinds is not invariant"
              S.empty
              (trulyInvariantArgs "self" ["cur", "k"]
                 (LetE ("k2", [], IntTy W64, PrimAppE addP64 [VarE "k", mkLitE64 1])
                       (LetE ("r", [], ProdTy [], selfCall [VarE "child", VarE "k2"])
                             (MkProdE []))))

-- | One faithful call does not excuse another that is not: `prefix acc xs`
-- threads a running accumulator.
case_truly_invariant_requires_every_self_call :: Assertion
case_truly_invariant_requires_every_self_call =
  assertEqual "one varying self-call is enough to disqualify"
              S.empty
              (trulyInvariantArgs "self" ["cur", "acc"]
                 (IfE (PrimAppE eqIntP64 [VarE "n", mkLitE64 0])
                      (selfCall [VarE "child", VarE "acc"])
                      (LetE ("acc2", [], IntTy W64, PrimAppE addP64 [VarE "acc", VarE "x"])
                            (selfCall [VarE "child", VarE "acc2"]))))

-- | A non-variable argument -- a literal, an expression -- is not a
-- pass-through either.
case_truly_invariant_rejects_non_variable_arg :: Assertion
case_truly_invariant_rejects_non_variable_arg =
  assertEqual "a literal at the scalar position is not the formal"
              S.empty
              (trulyInvariantArgs "self" ["cur", "k"]
                 (selfCall [VarE "child", mkLitE64 3]))

-- | Positional, not by name: passing the right variable at the wrong index
-- still changes what the callee sees.
case_truly_invariant_is_positional :: Assertion
case_truly_invariant_is_positional =
  assertEqual "swapped arguments are not pass-through"
              S.empty
              (trulyInvariantArgs "self" ["a", "b"]
                 (selfCall [VarE "b", VarE "a"]))

-- | Self-calls are found wherever they are, including buried in another
-- call's arguments and under an extension node -- the traversal gaps that
-- previously hid them.
case_truly_invariant_sees_nested_self_calls :: Assertion
case_truly_invariant_sees_nested_self_calls =
  assertEqual "a self-call nested in a call argument still disqualifies"
              S.empty
              (trulyInvariantArgs "self" ["k"]
                 (Ext (Assert (AppE "other" NotTailRec [] [selfCall [mkLitE64 9]]))))

-- | Nothing recurses, so nothing varies.
case_truly_invariant_vacuous_without_self_calls :: Assertion
case_truly_invariant_vacuous_without_self_calls =
  assertEqual "no self-call means no argument can change"
              (S.fromList ["cur", "k"])
              (trulyInvariantArgs "self" ["cur", "k"] (MkProdE []))

-- | A spawned self-call is still a self-call.
case_truly_invariant_sees_spawned_self_calls :: Assertion
case_truly_invariant_sees_spawned_self_calls =
  assertEqual "a spawned self-call that rebinds an argument disqualifies it"
              (S.fromList ["cur"])
              (trulyInvariantArgs "self" ["cur", "k"]
                 (SpawnE "self" [] [VarE "cur", mkLitE64 1]))

-- 'programWritesIndirections': neither loop emitter inspects tags, so an
-- indirection node landing mid-chunk desynchronises the walk.  The INDIRECTION
-- case arm is present in every cursorized traversal and therefore proves
-- nothing; only a writer does.  No program can reach the writer from source
-- today, so these pin the predicate at the IR level.

indirProg :: Exp3 -> Prog3
indirProg body =
  Prog { ddefs = M.empty
       , fundefs = M.fromList [("f", walkFun body)]
       , mainExp = Nothing
       }
  where
    walkFun b =
      FunDef { funName = "f"
             , funArgs = ["cur"]
             , funTy = ([CursorTy], ProdTy [])
             , funBody = b
             , funMeta = FunMeta NotRec NoInline False [] Nothing
             }

case_indirection_case_arm_alone_is_not_a_writer :: Assertion
case_indirection_case_arm_alone_is_not_a_writer =
  assertBool "an INDIRECTION case arm is not evidence a node can exist"
             (not (programWritesIndirections
                     (indirProg (CaseE (VarE "cur")
                                   [ ("Leaf", [], MkProdE [])
                                   , ("INDIRECTION_Tree", [], MkProdE [])
                                   ]))))

case_indirection_barrier_is_a_writer :: Assertion
case_indirection_barrier_is_a_writer =
  assertBool "an IndirectionBarrier creates an indirection node"
             (programWritesIndirections
                (indirProg (Ext (IndirectionBarrier "Tree" ("a", "b", "c", "d")))))

case_write_cursor_indirection_is_a_writer :: Assertion
case_write_cursor_indirection_is_a_writer =
  assertBool "a WriteCursorIndirection creates an indirection node"
             (programWritesIndirections
                (indirProg (Ext (WriteCursorIndirection "cur" "to" "toEnd"))))

case_indirection_writer_under_ext_is_found :: Assertion
case_indirection_writer_under_ext_is_found =
  assertBool "a writer nested under another extension node is still found"
             (programWritesIndirections
                (indirProg (Ext (WhileCursor "cur"
                                   (Ext (IndirectionBarrier "Tree"
                                           ("a", "b", "c", "d")))))))

--------------------------------------------------------------------------------
-- SoA buffer list: the same buffers, in the same order, with and without
-- random access.
--
-- AddRAN appends a `^` variant carrying extra cursor fields and the program's
-- case branches are rewritten over the variant, so the buffer keys must name
-- the variant too -- that is what `filterRanDatacons` picks, and it is the
-- filter `InferLocations.freshSoALoc2` uses to decide the layout.  A cursor
-- field gets no buffer, so the ARITY is the same either way, which is what
-- `getCursorTypeFromTy` independently reports and what the ABI scan matches.

ranTreeDDef :: DDef3
ranTreeDDef =
  DDef
    { tyName = "T"
    , tyArgs = []
    , dataCons =
        [ ("Node", [(False, IntTy W64), (True, PackedTy "T" ()), (True, PackedTy "T" ())])
        , ("Leaf", [(False, IntTy W64)])
        , ("Node^", [(False, CursorTy), (False, IntTy W64), (True, PackedTy "T" ()), (True, PackedTy "T" ())])
        , ("REDIRECTION_0", [(False, CursorTy)])
        ]
    , memLayout = FullyFactored
    }

noRanTreeDDef :: DDef3
noRanTreeDDef =
  ranTreeDDef { dataCons = filter ((`notElem` ["Node^"]) . fst) (dataCons ranTreeDDef) }

bufKeys :: DDef3 -> Maybe [(Int, DataCon, Int)]
bufKeys ddef =
  map (\ScalarBufferSpec{sbsBufIx, sbsDCon, sbsFieldIdx} -> (sbsBufIx, sbsDCon, sbsFieldIdx))
    <$> scalarBufferSpecs (M.fromList [("T", ddef)]) "T"

case_ran_and_non_ran_agree_on_buffer_count :: Assertion
case_ran_and_non_ran_agree_on_buffer_count = do
  -- Without random access the buffers are keyed on the plain constructors.
  Just [(1, "Node", 0), (2, "Leaf", 0)] @=? bufKeys noRanTreeDDef
  -- With it, on the `^` variant -- the one the program's branches are over --
  -- and the cursor field adds no buffer, so the count is unchanged.
  Just [(1, "Leaf", 0), (2, "Node^", 1)] @=? bufKeys ranTreeDDef

case_buffer_count_matches_the_cursor_array_length :: Assertion
case_buffer_count_matches_the_cursor_array_length = do
  let arrLen ddef = getCursorTypeFromTy "T" (M.fromList [("T", ddef)]) :: Ty3
  CursorArrayTy 3 @=? arrLen noRanTreeDDef
  CursorArrayTy 3 @=? arrLen ranTreeDDef

-- A random-access node writes its skipped subtree's cursor array INLINE in the
-- tag buffer, so that one element is 1 + 8*arrLen bytes where every other
-- constructor is 1.  The emitted loops read no tags and advance by a fixed
-- stride, so the traversal must be refused -- and named, not skipped silently.
-- The cursor array's LENGTH and its LAYOUT are the same enumeration, and the
-- random-access variant is where they could come apart: AddRAN keeps the
-- variant in the layout while the length drops it, and the two agree only
-- because the fields AddRAN adds are cursors.  That is checked, not assumed.

-- A `^` variant carrying a SCALAR -- which AddRAN never emits, so no source
-- program reaches this.
ranTreeDDefScalarVariant :: DDef3
ranTreeDDefScalarVariant =
  ranTreeDDef
    { dataCons =
        [ if dcon == "Node^" then (dcon, (False, IntTy W64) : flds) else (dcon, flds)
        | (dcon, flds) <- dataCons ranTreeDDef
        ]
    }

case_soa_buffer_enumeration_is_one_list :: Assertion
case_soa_buffer_enumeration_is_one_list = do
  let ddefs d = M.fromList [("T", d)]
      widthOf d = getCursorTypeFromTy "T" (ddefs d) :: Ty3
      slotsOf d = [ (dcon, ix) | (dcon, ix, _, _) <- soaBufferedFields (ddefs d) "T" ]
  -- Without random access, the layout is keyed on the plain constructors.
  [("Node", 0), ("Leaf", 0)] @=? slotsOf noRanTreeDDef
  -- With it, on the `^` variant -- and the width is the same either way.
  [("Leaf", 0), ("Node^", 1)] @=? slotsOf ranTreeDDef
  CursorArrayTy 3 @=? widthOf noRanTreeDDef
  CursorArrayTy 3 @=? widthOf ranTreeDDef

case_ran_variant_adding_a_buffer_is_refused :: Assertion
case_ran_variant_adding_a_buffer_is_refused = do
  r <- try (evaluate (length (show (soaBufferedFields
                                      (M.fromList [("T", ranTreeDDefScalarVariant)])
                                      "T"))))
  case r of
    Left (e :: ErrorCall) ->
      assertBool ("the refusal must name the disagreement, got: " ++ show e)
                 ("layout and its cursor array length disagree" `L.isInfixOf` show e)
    Right _ ->
      assertFailure "a `^` variant with a buffered field must be refused, not counted"

case_random_access_nodes_are_refused :: Assertion
case_random_access_nodes_are_refused = do
  assertBool "a `^` constructor means random-access nodes"
             (tyConHasRanNodes (M.fromList [("T", ranTreeDDef)]) "T")
  assertBool "without one there are none"
             (not (tyConHasRanNodes (M.fromList [("T", noRanTreeDDef)]) "T"))

-- A packed field of a DIFFERENT type gets buffers of its own, which the
-- emitted loop cannot walk.  Refused outright rather than indexed past the end
-- of the array.
case_foreign_packed_field_is_refused :: Assertion
case_foreign_packed_field_is_refused =
  let ddefs = M.fromList
                [ ("Pair", DDef "Pair" []
                             [("P", [(False, IntTy W64), (True, PackedTy "Leafy" ())])]
                             FullyFactored)
                , ("Leafy", DDef "Leafy" [] [("L", [(False, IntTy W64)])] FullyFactored)
                ]
   in Nothing @=? scalarBufferSpecs ddefs "Pair"

-- Every decline the report can print must have its own text: a copied line
-- would send a reader looking at the wrong condition.

case_soa_decline_reasons_are_distinct :: Assertion
case_soa_decline_reasons_are_distinct = do
  let ds = [ SoaNotCandidate, SoaCountsUnavailable "Tree", SoaNoPlan, SoaAbiMismatch ]
      rs = map soaDeclineReason ds
  assertBool "no decline reason may be empty" (all (not . null) rs)
  length ds @=? S.size (S.fromList rs)

--------------------------------------------------------------------------------
-- The counts gate's `gibbon_main` clause.
--
-- A value main materializes has no scalar-count footers -- Cursorize emits no
-- count bumps for the main expression -- so the clause asks whether such a
-- value can reach a traversal that would be loopified over its type.

-- | @let sentinel = Cons ... in ...@, as it looks after cursorization: a tag
-- written through a cursor indexed out of the value's own cursor array.
mainSentinelBinds :: [(Var, [()], Ty3, Exp3)]
mainSentinelBinds =
  [ ("sentinel_regs", [], CursorArrayTy 3, Ext $ MakeCursorArray 3 ["r0", "r1", "r2"])
  , ("sentinel_dcon", [], CursorTy, Ext $ IndexCursorArray "sentinel_regs" 0)
  , ("sentinel_tag", [], CursorTy, Ext $ WriteTag "Cons" "sentinel_dcon")
  ]

-- | The program under test with a given main expression, and a traversal over
-- @List@ that loopification accepts.
gateMainProg :: Exp3 -> Prog3
gateMainProg mainE =
  (guardedProg totalCondRhs) { mainExp = Just (mainE, ProdTy []) }

loopifiedInMain :: Exp3 -> Bool
loopifiedInMain mainE =
  let Prog{fundefs = fds} = runnerWithCounts (gateMainProg mainE)
   in Loopified `elem` funOpt (funMeta (fds M.! "fastAdd1ListMut"))

case_main_materialization_that_goes_nowhere_does_not_block_loopification :: Assertion
case_main_materialization_that_goes_nowhere_does_not_block_loopification =
  assertBool "a value main builds and never passes on cannot reach the traversal"
    (loopifiedInMain (mkLets mainSentinelBinds (MkProdE [])))

case_main_materialization_passed_to_the_traversal_blocks_loopification :: Assertion
case_main_materialization_passed_to_the_traversal_blocks_loopification =
  assertBool "a value main hands to the traversal must disqualify the type"
    (not (loopifiedInMain
            (mkLets
               (mainSentinelBinds ++
                [ ("consume", [], ProdTy []
                  , AppE "fastAdd1ListMut" UnknownTailType []
                      [ VarE "sentinel_regs", VarE "outEnds"
                      , VarE "outCurs", VarE "sentinel_regs" ]) ])
               (MkProdE []))))

case_main_materialization_passed_elsewhere_does_not_block_loopification :: Assertion
case_main_materialization_passed_elsewhere_does_not_block_loopification =
  assertBool "a value main hands to a function that cannot reach the traversal is fine"
    (loopifiedInMain
       (mkLets
          (mainSentinelBinds ++
           [ ("consume", [], ProdTy []
             , AppE "countedBuilder" UnknownTailType [] [VarE "sentinel_regs"]) ])
          (MkProdE [])))

-- | The tainted set follows the value, not just the cursor the tag went
-- through: the call is handed the region array the write cursor was indexed
-- out of, one alias further on.
case_main_materialization_reaches_through_an_alias :: Assertion
case_main_materialization_reaches_through_an_alias =
  assertBool "an alias of the materialized value must disqualify the type too"
    (not (loopifiedInMain
            (mkLets
               (mainSentinelBinds ++
                [ ("sentinel_alias", [], CursorArrayTy 3, VarE "sentinel_regs")
                , ("consume", [], ProdTy []
                  , AppE "fastAdd1ListMut" UnknownTailType []
                      [ VarE "sentinel_alias", VarE "outEnds"
                      , VarE "outCurs", VarE "sentinel_alias" ]) ])
               (MkProdE []))))

loopifyTraversalsTests :: TestTree
loopifyTraversalsTests = $(testGroupGenerator)
