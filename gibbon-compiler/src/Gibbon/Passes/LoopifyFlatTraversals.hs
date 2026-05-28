-- | Conservative loopification for `OPT:CanVectorize` traversals over flat
-- AoS packed layouts.
--
-- This is deliberately separate from `LoopifyTraversals`, which targets fully
-- factored SoA layouts.  In a flat AoS layout all constructor tags and fields
-- live in one heterogeneous byte stream, so there are no homogeneous field
-- buffers, no scalar-count footer bounds, and no useful per-buffer vector loop.
-- The best first-step loopification is therefore structural: replace recursive
-- calls with a single cursor walk over the packed input value.
--
-- Invariants for this pass:
--
-- * The function must be annotated with `OPT:CanVectorize`, or the compiler
--   must be run with `--auto-loopification`.  The annotation/auto-discovery path
--   is the user/compiler promise that recursive calls are independent.
--   Automatic mode ignores generated packed helpers (`_copy_*`, `_print_*`,
--   `_traverse_*`, `_unpack_*`, etc.) because they are compiler infrastructure,
--   not source-level map candidates. The pass
--   still reuses the SoA parent-child dependency check and refuses functions
--   where self-call results flow into parent scalar writes, tags, conditions, or
--   subsequent traversal decisions.
--
-- * The datatype mentioned by the top-level case expression must not be
--   `FullyFactored`.  Fully factored values are handled by the SoA pass using
--   footer counts and per-buffer loops.
--
-- * The cursorized mutable AoS function carries both the input value end and
--   the current input cursor as mutable cursor references.  After the Cursorize
--   end-cursor fix, the input end argument is the packed value end, so the flat
--   loop can stop at `while (*input_cursor != *input_end)`.
--
-- * Each loop iteration executes the original single-node switch body with
--   recursive self-calls replaced by unit.  Normal constructor branches consume
--   exactly one node header and its scalar fields, leaving recursive child
--   cursors for later loop iterations.  Redirection/indirection branches update
--   the input cursor to the target and then let the loop continue.
--
-- Current limitations:
--
-- * This first AoS pass only handles the mutable-cursor cursorized shape.  That
--   is the backend used for the flat baseline we care about right now.
--
-- * It does not attempt SIMD, selective sharing, or field fusion.  Those are
--   SoA-only optimizations.
module Gibbon.Passes.LoopifyFlatTraversals
  ( loopifyFlatTraversals
  ) where

import           Control.Monad (guard)
import           Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S

import           Gibbon.Common
import           Gibbon.DynFlags
import           Gibbon.L3.Syntax
import           Gibbon.Passes.LoopifyTraversals
  ( collectMentionedDataCons
  , hasParentChildDependency
  )

loopifyFlatTraversals :: Prog3 -> PassM Prog3
loopifyFlatTraversals prog@Prog{ddefs, fundefs} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_EnableLoopification dflags
      auto = gopt Opt_AutoLoopification dflags
  fds' <- if enabled
          then mapM (rewriteFun auto ddefs) (M.elems fundefs)
          else pure (M.elems fundefs)
  pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

rewriteFun :: Bool -> DDefs3 -> FunDef3 -> PassM FunDef3
rewriteFun auto ddefs f@FunDef{funName, funMeta, funBody}
  | not explicitlyAnnotated && not canInfer = pure f
  | hasParentChildDependency funName funBody = pure f
  | otherwise =
      case flatCandidateInfo ddefs f of
        Nothing -> pure f
        Just FlatCandidate{fcInputEnd, fcInputCursor} -> do
          let loopBody = exposeRhsLets (eraseSelfCalls funName funBody)
              body' = LetE (freshFlatLoopName funName, [], ProdTy [],
                            Ext $ WhileCursorEnd fcInputCursor fcInputEnd loopBody)
                           (MkProdE [])
          pure $ stampCanVectorize (f { funBody = body' })
  where
    explicitlyAnnotated = CanVectorize `elem` funOpt funMeta
    canInfer = auto && not (isGeneratedPackedHelper funName)

isGeneratedPackedHelper :: Var -> Bool
isGeneratedPackedHelper v =
  or [ isCopyFunName v
     , isCopySansPtrsFunName v
     , isPrinterName v
     , isTravFunName v
     , isUnpackerName v
     , isRelOffsetsFunName v
     ]

stampCanVectorize :: FunDef3 -> FunDef3
stampCanVectorize fn@FunDef{funMeta} =
  fn { funMeta = funMeta { funOpt = CanVectorize : filter (/= CanVectorize) (funOpt funMeta) } }

-- | The minimal role information needed for flat AoS loopification.
data FlatCandidate = FlatCandidate
  { fcInputEnd    :: Var
  , fcInputCursor :: Var
  } deriving (Show)

flatCandidateInfo :: DDefs3 -> FunDef3 -> Maybe FlatCandidate
flatCandidateInfo ddefs FunDef{funName, funArgs, funTy, funBody} = do
  guard (all isMutCursorTy (take 4 (fst funTy)))
  _ <- singleMentionedNonSoATyCon ddefs funBody
  inputCursor <- topCaseInputCursor funBody
  inputEnd <- inferInputEndFromSelfCall funName inputCursor (S.fromList funArgs) funBody
  pure $ FlatCandidate inputEnd inputCursor

singleMentionedNonSoATyCon :: DDefs3 -> Exp3 -> Maybe TyCon
singleMentionedNonSoATyCon ddefs body = do
  let tycons = S.toList . S.fromList $ mapMaybe dconTyCon (collectMentionedDataCons body)
  tycon <- listToMaybe tycons
  guard (length tycons == 1)
  let ddef = lookupDDef ddefs tycon
  guard (memLayout ddef /= FullyFactored)
  pure tycon
  where
    dconTyCon dcon = do
      let matches = [ fromVar tyName | (_k, DDef{tyName, dataCons}) <- M.toList ddefs
                            , (dc, _) <- dataCons
                            , dc == dcon ]
      listToMaybe matches

isMutCursorTy :: Ty3 -> Bool
isMutCursorTy MutCursorTy = True
isMutCursorTy _ = False

-- | Find the mutable input cursor feeding the top-level packed case.  Cursorize
-- emits `let scrut = DerefMutCursor input_cursor in case scrut of ...` for flat
-- AoS traversals.
topCaseInputCursor :: Exp3 -> Maybe Var
topCaseInputCursor = go M.empty
  where
    go env ex =
      case ex of
        LetE ((v, _, _, Ext (DerefMutCursor cur))) bod ->
          go (M.insert v cur env) bod
        LetE _ bod -> go env bod
        CaseE (VarE scrut) _ -> M.lookup scrut env
        _ -> Nothing

-- | The stable input end is the first argument supplied to an ordinary
-- recursive self-call.  Redirection branches pass the current cursor as the
-- first argument, so ignore calls whose first argument is the input cursor.
inferInputEndFromSelfCall :: Var -> Var -> S.Set Var -> Exp3 -> Maybe Var
inferInputEndFromSelfCall funName inputCursor formals body =
  listToMaybe
    [ v
    | AppE fn _ _ args <- collectApps body
    , fn == funName
    , VarE v : _ <- [args]
    , v /= inputCursor
    , v `S.member` formals
    ]

collectApps :: Exp3 -> [Exp3]
collectApps ex =
  case ex of
    AppE{} -> [ex]
    LetE (_, _, _, rhs) bod -> collectApps rhs ++ collectApps bod
    IfE a b c -> collectApps a ++ collectApps b ++ collectApps c
    MkProdE es -> concatMap collectApps es
    ProjE _ e -> collectApps e
    CaseE scrt brs -> collectApps scrt ++ concatMap (collectApps . thd3) brs
    DataConE _ _ es -> concatMap collectApps es
    TimeIt e _ _ -> collectApps e
    WithArenaE _ e -> collectApps e
    SpawnE _ _ es -> concatMap collectApps es
    MapE (_, _, e1) e2 -> collectApps e1 ++ collectApps e2
    FoldE (_, _, e1) (_, _, e2) e3 -> concatMap collectApps [e1, e2, e3]
    Ext ext -> collectAppsExt ext
    _ -> []

collectAppsExt :: E3Ext () Ty3 -> [Exp3]
collectAppsExt ext =
  case ext of
    WriteScalar _ _ rhs -> collectApps rhs
    WriteTagPacked _ rhs -> collectApps rhs
    WriteCursorSelectiveIndirection _ _ _ rhs -> collectApps rhs
    WriteTaggedCursor _ rhs -> collectApps rhs
    WriteCursorMutable _ rhs -> collectApps rhs
    WriteList _ rhs _ -> collectApps rhs
    WriteVector _ rhs _ -> collectApps rhs
    AddCursor _ rhs -> collectApps rhs
    BumpCursorMutable _ rhs -> collectApps rhs
    AddrOfCursor rhs -> collectApps rhs
    LetAvail _ rhs -> collectApps rhs
    ForE _ bound rhs -> collectApps bound ++ collectApps rhs
    WhileCursor _ rhs -> collectApps rhs
    WhileCursorEnd _ _ rhs -> collectApps rhs
    RetE es -> concatMap collectApps es
    Assert rhs -> collectApps rhs
    _ -> []

-- | Turn recursive calls into unit effects; the enclosing cursor-end loop will
-- visit the child nodes in packed order.  Parent-child dependencies are checked
-- before this rewrite, so call results should not be semantically consumed.
eraseSelfCalls :: Var -> Exp3 -> Exp3
eraseSelfCalls funName ex =
  case ex of
    AppE fn _ _ _ | fn == funName -> MkProdE []
    LetE (v, locs, ty, rhs) bod -> LetE (v, locs, ty, eraseSelfCalls funName rhs) (eraseSelfCalls funName bod)
    IfE a b c -> IfE (eraseSelfCalls funName a) (eraseSelfCalls funName b) (eraseSelfCalls funName c)
    MkProdE es -> MkProdE (map (eraseSelfCalls funName) es)
    ProjE i e -> ProjE i (eraseSelfCalls funName e)
    CaseE scrt brs -> CaseE (eraseSelfCalls funName scrt)
                         [ (dc, vs, eraseSelfCalls funName rhs) | (dc, vs, rhs) <- brs ]
    DataConE loc dc es -> DataConE loc dc (map (eraseSelfCalls funName) es)
    TimeIt e ty b -> TimeIt (eraseSelfCalls funName e) ty b
    WithArenaE v e -> WithArenaE v (eraseSelfCalls funName e)
    SpawnE v loc es -> SpawnE v loc (map (eraseSelfCalls funName) es)
    MapE (v, ty, rhs) bod -> MapE (v, ty, eraseSelfCalls funName rhs) (eraseSelfCalls funName bod)
    FoldE (v1, t1, r1) (v2, t2, r2) bod ->
      FoldE (v1, t1, eraseSelfCalls funName r1)
            (v2, t2, eraseSelfCalls funName r2)
            (eraseSelfCalls funName bod)
    Ext ext -> Ext (eraseSelfCallsExt funName ext)
    _ -> ex

eraseSelfCallsExt :: Var -> E3Ext () Ty3 -> E3Ext () Ty3
eraseSelfCallsExt funName ext =
  case ext of
    WriteScalar s cur rhs -> WriteScalar s cur (go rhs)
    WriteTagPacked cur rhs -> WriteTagPacked cur (go rhs)
    WriteCursorSelectiveIndirection a b c rhs -> WriteCursorSelectiveIndirection a b c (go rhs)
    WriteTaggedCursor cur rhs -> WriteTaggedCursor cur (go rhs)
    WriteCursorMutable cur rhs -> WriteCursorMutable cur (go rhs)
    WriteList cur rhs ty -> WriteList cur (go rhs) ty
    WriteVector cur rhs ty -> WriteVector cur (go rhs) ty
    AddCursor cur rhs -> AddCursor cur (go rhs)
    BumpCursorMutable cur rhs -> BumpCursorMutable cur (go rhs)
    AddrOfCursor rhs -> AddrOfCursor (go rhs)
    LetAvail vs rhs -> LetAvail vs (go rhs)
    ForE idx bound rhs -> ForE idx (go bound) (go rhs)
    WhileCursor cur rhs -> WhileCursor cur (go rhs)
    WhileCursorEnd cur end rhs -> WhileCursorEnd cur end (go rhs)
    RetE es -> RetE (map go es)
    Assert rhs -> Assert (go rhs)
    _ -> ext
  where
    go = eraseSelfCalls funName

freshFlatLoopName :: Var -> Var
freshFlatLoopName f = varAppend f "_flat_aos_loop"

-- | Cursorize and ReorderScalarWrites sometimes leave statement-like cursor
-- temporaries inside a let RHS whose names are used by following statements.
-- Lowering flattens those RHS lets into C declarations, but an L3 loop body is
-- typechecked before lowering and therefore needs the same sequencing made
-- explicit.  This pass-local normalizer floats only prefix lets from RHSs.
exposeRhsLets :: Exp3 -> Exp3
exposeRhsLets ex =
  case ex of
    LetE (v, locs, ty, rhs) bod ->
      let (prefix, rhs') = peelLets (exposeRhsLets rhs)
       in mkLets3 prefix (LetE (v, locs, ty, rhs') (exposeRhsLets bod))
    IfE a b c -> IfE (exposeRhsLets a) (exposeRhsLets b) (exposeRhsLets c)
    MkProdE es -> MkProdE (map exposeRhsLets es)
    ProjE i e -> ProjE i (exposeRhsLets e)
    CaseE scrt brs -> CaseE (exposeRhsLets scrt)
                         [ (dc, vs, exposeRhsLets rhs) | (dc, vs, rhs) <- brs ]
    DataConE loc dc es -> DataConE loc dc (map exposeRhsLets es)
    TimeIt e ty b -> TimeIt (exposeRhsLets e) ty b
    WithArenaE v e -> WithArenaE v (exposeRhsLets e)
    SpawnE v loc es -> SpawnE v loc (map exposeRhsLets es)
    MapE (v, ty, rhs) bod -> MapE (v, ty, exposeRhsLets rhs) (exposeRhsLets bod)
    FoldE (v1, t1, r1) (v2, t2, r2) bod ->
      FoldE (v1, t1, exposeRhsLets r1)
            (v2, t2, exposeRhsLets r2)
            (exposeRhsLets bod)
    Ext ext -> Ext (exposeRhsLetsExt ext)
    _ -> ex

exposeRhsLetsExt :: E3Ext () Ty3 -> E3Ext () Ty3
exposeRhsLetsExt ext =
  case ext of
    WriteScalar s cur rhs -> WriteScalar s cur (exposeRhsLets rhs)
    WriteTagPacked cur rhs -> WriteTagPacked cur (exposeRhsLets rhs)
    WriteCursorSelectiveIndirection a b c rhs -> WriteCursorSelectiveIndirection a b c (exposeRhsLets rhs)
    WriteTaggedCursor cur rhs -> WriteTaggedCursor cur (exposeRhsLets rhs)
    WriteCursorMutable cur rhs -> WriteCursorMutable cur (exposeRhsLets rhs)
    WriteList cur rhs ty -> WriteList cur (exposeRhsLets rhs) ty
    WriteVector cur rhs ty -> WriteVector cur (exposeRhsLets rhs) ty
    AddCursor cur rhs -> AddCursor cur (exposeRhsLets rhs)
    BumpCursorMutable cur rhs -> BumpCursorMutable cur (exposeRhsLets rhs)
    AddrOfCursor rhs -> AddrOfCursor (exposeRhsLets rhs)
    LetAvail vs rhs -> LetAvail vs (exposeRhsLets rhs)
    ForE idx bound rhs -> ForE idx (exposeRhsLets bound) (exposeRhsLets rhs)
    WhileCursor cur rhs -> WhileCursor cur (exposeRhsLets rhs)
    WhileCursorEnd cur end rhs -> WhileCursorEnd cur end (exposeRhsLets rhs)
    RetE es -> RetE (map exposeRhsLets es)
    Assert rhs -> Assert (exposeRhsLets rhs)
    _ -> ext

peelLets :: Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3)
peelLets ex =
  case ex of
    LetE bind bod ->
      let (binds, tailExp) = peelLets bod
       in (bind : binds, tailExp)
    _ -> ([], ex)

mkLets3 :: [(Var, [()], Ty3, Exp3)] -> Exp3 -> Exp3
mkLets3 binds bod = foldr LetE bod binds
