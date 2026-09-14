-- | Conservative loopification for `OPT:MayVectorize` traversals over flat AoS
-- packed layouts.
--
-- Separate from `LoopifyTraversals`, which targets SoA: a flat AoS layout keeps
-- all tags and fields in one heterogeneous byte stream, so there are no
-- homogeneous field buffers, no scalar-count footer bounds, and no per-buffer
-- vector loop.  Loopification here is structural -- recursive calls become a
-- single cursor walk over the packed input.
--
-- Invariants:
--
-- * The function must carry `OPT:MayVectorize`, or `--auto-loopification` must
--   be set; automatic mode ignores generated packed helpers (`_copy_*`,
--   `_print_*`, `_traverse_*`, `_unpack_*`).
-- * The SoA `hasParentChildDependency` check is applied, but it cannot reject
--   anything HERE and is not what keeps this pass safe: `flatCandidateInfo`
--   requires `isVoidTy (snd funTy)`, so every self-call returns unit and the
--   result it binds is dead, which is exactly the shape that check looks for.
--   What actually refuses a parent-child dependency in this pass is
--   'hasUnerasableCall' -- consuming a child's result post-cursorize means
--   reading it back, which takes a call.
-- * Every formal past the ABI cursor block must be passed through unchanged by
--   every self-call ('trulyInvariantArgs'), the body must contain no call
--   erasure cannot remove ('hasUnerasableCall') and no observable effect
--   ('hasObservableEffect'), and every caller must pass a provable value end
--   ('callerEndsAreValueEnds').
-- * The datatype in the top-level case must be `Linear`.  `FullyFactored`
--   goes to the SoA pass, and `Mixed` is documented as unimplemented.
-- * The cursorized mutable AoS function carries the input value end and the
--   current input cursor as mutable cursor references, so the loop stops at
--   `while (*input_cursor != *input_end)`.
-- * Each iteration runs the original single-node switch body with self-calls
--   replaced by unit.  Constructor branches consume one node header and its
--   scalar fields; a redirection branch continues at the next chunk.  The
--   pass refuses to run at all on a program that can WRITE an indirection
--   node: the emitted cursor walk skips past such a cell rather than
--   following it, and the recursive call into the target is erased, so the
--   indirected subtree would be neither traversed nor written.
--
-- Limitations: mutable-cursor cursorized shape only; no SIMD, selective
-- sharing, or field fusion (those are SoA-only).
module Gibbon.Passes.LoopifyFlatTraversals
  ( loopifyFlatTraversals
  -- Exported for tests: the refusals that decide whether a flat AoS
  -- traversal may be rewritten into a cursor loop.
  , hasUnerasableCall
  , hasObservableEffect
  , callerEndsAreValueEnds
  , flatAbiCursorCount
  -- The one answer to "would this be rewritten, and if not why not", shared
  -- with the loopification report so neither re-derives it.
  , FlatDecline(..)
  , flatDeclineReason
  ) where

import           Control.Monad (guard)
import           Data.List (elemIndex)
import           Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S

import           Gibbon.Common
import           Gibbon.DynFlags
import           Gibbon.L3.Syntax
import           Gibbon.L3.Traverse (extExps, mapExtExps, traverseExtExps)
import           Gibbon.Passes.LoopifyTraversals
  ( EffectClass(..)
  , collectMentionedDataCons
  , hasParentChildDependency
  , loopificationReport
  , primEffectClass
  , programWritesIndirections
  , trulyInvariantArgs
  )

-- | How many leading formals mutable-cursor AoS cursorization spends on the
-- traversal ABI: the two region ends, the output location, and the input
-- cursor.  Formals past this block are the function's own arguments.
flatAbiCursorCount :: Int
flatAbiCursorCount = 4

-- | Argument index of the input end -- the cursor the emitted loop stops at.
flatInputEndIx :: Int
flatInputEndIx = 0

-- | Argument index of the input cursor the traversal starts from.
flatInputStartIx :: Int
flatInputStartIx = 3

-- | What a mutable cursor is known to be.
--
-- 'CursorAddrOf' records @let m = AddrOfCursor (VarE r)@: @m@ addresses @r@.
-- 'CursorValueEnd' records that some call has since used @m@ as its OUTPUT
-- LOCATION, so a producer has advanced it from @r@ past everything it wrote.
data EndEnv = EndEnv
  { eeAddrOf   :: M.Map Var Var   -- ^ mutable cursor -> the cursor it addresses
  , eeAlias    :: M.Map Var Var   -- ^ copy -> source
  , eeValueEnd :: M.Map Var Var   -- ^ mutable cursor -> the start it now ends
  , eePoisoned :: S.Set Var       -- ^ used as an output location more than once
  }

emptyEndEnv :: EndEnv
emptyEndEnv = EndEnv M.empty M.empty M.empty S.empty

-- | Follow copies and 'AddrOfCursor' indirections to the underlying cursor.
rootOf :: EndEnv -> Var -> Var
rootOf env = go (64 :: Int)
  where
    go 0 v = v
    go n v =
      case M.lookup v (eeAddrOf env) of
        Just v' -> go (n - 1) v'
        Nothing ->
          case M.lookup v (eeAlias env) of
            Just v' -> go (n - 1) v'
            Nothing -> v

-- | Functions every one of whose non-self call sites passes an end argument
-- that is provably the end of the value the start argument points at.
--
-- The flat AoS loop stops at @while (*input_cursor != *input_end)@, and
-- nothing in the pass checks what callers put there.  A map applied to a
-- SUBTREE is called with the enclosing REGION end, so the walk would run past
-- the subtree, through its sibling and off the data.
--
-- The provenance that does establish a value end, and the one the corpus
-- actually has, is this: an earlier call in the same body used that mutable
-- cursor as its OUTPUT LOCATION, the cursor was created as @AddrOfCursor r@
-- for some region start @r@, and this call's start argument resolves to the
-- same @r@.  The producer wrote one packed value starting at @r@ and advanced
-- the cursor past it, so @[r, *end)@ is exactly that value.
--
-- Used twice as an output location, the cursor is poisoned: the span would
-- then cover two values, and the walk would run through both.
callerEndsAreValueEnds :: Var -> Prog3 -> Bool
callerEndsAreValueEnds fn Prog{fundefs, mainExp} =
  all okBody bodies
  where
    bodies =
      [ (funName fd, funBody fd) | fd <- M.elems fundefs ]
        ++ maybe [] (\(e, _) -> [(mainName, e)]) mainExp
    -- The pass erases the candidate's own self-calls, so they impose nothing.
    okBody (owner, body) =
      owner == fn || snd (scanEnds advanced fn emptyEndEnv body)
    advanced = advancedArgIxs fundefs

-- | For each function, the argument positions whose mutable cursor its body
-- ADVANCES with 'BumpCursorMutable'.
--
-- That is what makes a call evidence of a value end: a cursor handed to such a
-- position starts at a value's first byte and is stepped past every byte of
-- it, whether the callee is writing the value (an output location) or reading
-- it (an input cursor).  Either way it finishes at that value's end.
advancedArgIxs :: FunDefs3 -> M.Map Var (S.Set Int)
advancedArgIxs =
  M.map (\fd ->
           let bumped = bumpedCursors (funBody fd)
            in S.fromList [ ix
                          | (ix, v) <- zip [0 :: Int ..] (funArgs fd)
                          , v `S.member` bumped ])

bumpedCursors :: Exp3 -> S.Set Var
bumpedCursors ex =
  case ex of
    Ext (BumpCursorMutable cur rhs) -> S.insert cur (bumpedCursors rhs)
    Ext ext -> S.unions (map bumpedCursors (extExps ext))
    AppE _ _ _ args -> S.unions (map bumpedCursors args)
    SpawnE _ _ args -> S.unions (map bumpedCursors args)
    PrimAppE _ args -> S.unions (map bumpedCursors args)
    LetE (_, _, _, rhs) bod -> bumpedCursors rhs `S.union` bumpedCursors bod
    IfE a b c -> S.unions (map bumpedCursors [a, b, c])
    MkProdE es -> S.unions (map bumpedCursors es)
    ProjE _ e -> bumpedCursors e
    CaseE scrt brs ->
      bumpedCursors scrt `S.union` S.unions (map (bumpedCursors . thd3) brs)
    DataConE _ _ es -> S.unions (map bumpedCursors es)
    TimeIt e _ _ -> bumpedCursors e
    WithArenaE _ e -> bumpedCursors e
    MapE (_, _, e1) e2 -> bumpedCursors e1 `S.union` bumpedCursors e2
    FoldE (_, _, e1) (_, _, e2) e3 -> S.unions (map bumpedCursors [e1, e2, e3])
    _ -> S.empty

-- | A name no user function can have, standing for @mainExp@.
mainName :: Var
mainName = "#main"

-- | Walk a body in evaluation order, tracking cursor provenance and checking
-- every call to @fn@ against it.
scanEnds :: M.Map Var (S.Set Int) -> Var -> EndEnv -> Exp3 -> (EndEnv, Bool)
scanEnds advanced fn = go
  where
    go env ex =
      case ex of
        LetE (v, _, _, rhs) bod ->
          let (env1, ok1) = go env rhs
              env2 = record v rhs env1
              (env3, ok2) = go env2 bod
           in (env3, ok1 && ok2)
        -- Arguments are evaluated before the call, and cursorize builds some
        -- of them as their own let-chains, so they are walked first: their
        -- bindings are part of the provenance the call is then checked
        -- against.
        AppE g _ _ args ->
          let (envA, okA) = seqAll env args
              ok = okA && (g /= fn || callOk envA args)
           in (noteAdvanced g envA args, ok)
        SpawnE g _ args ->
          let (envA, okA) = seqAll env args
              ok = okA && (g /= fn || callOk envA args)
           in (noteAdvanced g envA args, ok)
        IfE a b c -> seqAll env [a, b, c]
        CaseE scrt brs -> seqAll env (scrt : map thd3 brs)
        MkProdE es -> seqAll env es
        ProjE _ e -> go env e
        PrimAppE _ args -> seqAll env args
        TimeIt e _ _ -> go env e
        WithArenaE _ e -> go env e
        DataConE _ _ args -> seqAll env args
        MapE (_, _, e1) e2 -> seqAll env [e1, e2]
        FoldE (_, _, e1) (_, _, e2) e3 -> seqAll env [e1, e2, e3]
        Ext ext -> seqAll env (extExps ext)
        _ -> (env, True)

    seqAll env =
      foldl (\(e, ok) x -> let (e', ok') = go e x in (e', ok && ok')) (env, True)

    record v rhs env =
      case rhs of
        Ext (AddrOfCursor (VarE r)) ->
          env { eeAddrOf = M.insert v r (eeAddrOf env) }
        VarE r -> env { eeAlias = M.insert v r (eeAlias env) }
        _ -> env

    -- A cursor handed to a position the callee ADVANCES is stepped past every
    -- byte of one complete value, so afterwards it holds that value's end.  A
    -- second such use would make the span cover two values, so it poisons the
    -- cursor instead of extending it.
    noteAdvanced g env args =
      foldl note env (S.toList (M.findWithDefault S.empty g advanced))
      where
        note e ix =
          case argVarAt ix args of
            Just o
              | Just r <- M.lookup o (eeAddrOf e) ->
                  if M.member o (eeValueEnd e)
                    then e { eePoisoned = S.insert o (eePoisoned e) }
                    else e { eeValueEnd = M.insert o r (eeValueEnd e) }
            _ -> e

    callOk env args =
      case (argVarAt flatInputEndIx args, argVarAt flatInputStartIx args) of
        (Just endV, Just startV)
          | not (endV `S.member` eePoisoned env)
          , Just root <- M.lookup endV (eeValueEnd env) ->
              rootOf env startV == root
        _ -> False

    -- Cursorize passes some arguments as a let-chain ending in the variable
    -- it actually means, so look through to the tail.
    argVarAt ix as =
      case drop ix as of
        a : _ -> tailVar a
        _ -> Nothing

    tailVar (VarE v) = Just v
    tailVar (LetE _ bod) = tailVar bod
    tailVar _ = Nothing

loopifyFlatTraversals :: Prog3 -> PassM Prog3
loopifyFlatTraversals prog@Prog{ddefs, fundefs} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_EnableLoopification dflags
      auto = gopt Opt_AutoLoopification dflags
      -- The emitted cursor walk skips PAST an indirection cell rather than
      -- following it, and the recursive call into the target is erased, so an
      -- indirected subtree would be neither traversed nor written.  Refuse the
      -- whole program rather than emit a walk that cannot survive one.  Every
      -- cursorized traversal carries an INDIRECTION case arm whether or not
      -- the program can put such a node in the data, so the arm itself proves
      -- nothing; only a writer does.
      report = gopt Opt_LoopificationReport dflags
      say lns x = loopificationReport report "AoS" lns x
  if not enabled
    then pure $ say ["--opt-loopification is off; the pass did nothing"] prog
    else if programWritesIndirections prog
    then pure $ say ["the program writes indirections; no function is loopified"] prog
    else do
      results <- mapM (rewriteFun auto ddefs prog) (M.elems fundefs)
      let fds' = map fst results
          lns = [ flatReportLine fn outcome | (fn, outcome) <- results ]
      pure $ say lns $
        prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

-- | Every decline path returns the function UNCHANGED.
--
-- `repairMutAddCursorSources` rewrites `AddCursor mutFormal e` into
-- `AddCursor (deref mutFormal) e`, which the emitted loop needs but a function
-- this pass declines does not.  Returning the repaired body on a decline made
-- an optimisation flag perturb the IR of functions the optimisation had
-- refused, so the flag was never neutral on the code it did not transform.
-- | The rewritten (or unchanged) function, paired with what was decided about
-- it, for @--loopification-report@.
rewriteFun :: Bool -> DDefs3 -> Prog3 -> FunDef3
           -> PassM (FunDef3, Either FlatDecline ())
rewriteFun auto ddefs prog f@FunDef{funName, funArgs, funTy, funMeta, funBody} = do
  let explicitlyAnnotated = MayVectorize `elem` funOpt funMeta
      canInfer = auto && not (isGeneratedPackedHelper funName)
  -- Checked BEFORE the repair, which is what makes it able to see anything:
  -- once `AddCursor mutFormal e` has become `AddCursor (deref mutFormal) e`,
  -- `addCursorSources` can no longer see the mutable formal.
  case () of
    _ | not explicitlyAnnotated && not canInfer -> pure (f, Left FlatNotCandidate)
      | hasNonAbiMutFormalAddCursorUse funArgs (fst funTy) funBody ->
          pure (f, Left FlatMutFormalAddCursor)
      | hasParentChildDependency funName funBody ->
          pure (f, Left FlatParentChildDependency)
      -- The loop stops at `while (*input_cursor != *input_end)`, so what
      -- CALLERS pass at the end position decides whether it terminates at
      -- the value's end or runs off the data.  Nothing else in this pass
      -- looks at a call site.
      | not (callerEndsAreValueEnds funName prog) ->
          pure (f, Left FlatCallerEndNotValueEnd)
      | otherwise -> do
          funBodyRepaired <-
            repairMutAddCursorSources (M.fromList (zip funArgs (fst funTy))) funBody
          let fRepaired = f { funBody = funBodyRepaired }
          case flatCandidateInfo ddefs fRepaired of
            Left d -> pure (f, Left d)
            Right FlatCandidate{fcInputEnd, fcInputCursor} -> do
              loopName <- gensym (varAppend funName "_flat_aos_loop")
              let loopBody = exposeRhsLets (eraseSelfCalls funName funBodyRepaired)
                  body' = LetE (loopName, [], ProdTy [],
                              Ext $ WhileCursorEnd fcInputCursor fcInputEnd loopBody)
                             (MkProdE [])
              pure (stampLoopified (fRepaired { funBody = body' }), Right ())

-- | Why the AoS loopifier did not rewrite a function.
--
-- One decision, asked once, so the pass and @--loopification-report@ cannot
-- give different answers.
data FlatDecline
  = FlatNotCandidate
    -- ^ No @OPT:MayVectorize@ and not inferred, or a generated packed helper.
  | FlatMutFormalAddCursor
    -- ^ A mutable-cursor formal outside the ABI block is used as an
    -- @AddCursor@ base, which the loop's repair cannot see through.
  | FlatParentChildDependency
    -- ^ A recursive call's result feeds another, so the elements are not
    -- independent.
  | FlatCallerEndNotValueEnd
    -- ^ Some caller passes something other than the value's own end, so the
    -- emitted @while (*cursor != *end)@ would not stop at the value.
  | FlatNotVoidReturn
    -- ^ The function returns something; the loop discards per-element results.
  | FlatAbiNotMutCursors
    -- ^ The leading ABI formals are not all mutable cursors, so this is not
    -- mutable-cursor AoS cursorization's output shape.
  | FlatNotSingleLinearTyCon
    -- ^ The body mentions no datatype, more than one, a constructor shared by
    -- two datatypes, or a type that is not @Linear@.
  | FlatNoInputCursor
    -- ^ No top-level packed case over a dereferenced mutable cursor.
  | FlatNoInputEnd
    -- ^ The traversal's end cursor could be found neither in the ABI block nor
    -- from a self-call.
  | FlatVariantArgs
    -- ^ A formal past the ABI block is not passed through the recursion
    -- unchanged, so hoisting its read to loop entry would change the meaning.
  | FlatUnerasableCall
    -- ^ A self-call the loop body cannot erase.
  | FlatObservableEffect
    -- ^ The body has an effect whose order the loop would change.
  | FlatNonTraversalInputUpdate
    -- ^ The input cursor is advanced by something other than the traversal.
  deriving (Eq, Show)

-- | Human-readable, one line, for @--loopification-report@.
flatDeclineReason :: FlatDecline -> String
flatDeclineReason d =
  case d of
    FlatNotCandidate -> "not a candidate (no OPT:MayVectorize, not inferred, or a generated packed helper)"
    FlatMutFormalAddCursor -> "a non-ABI mutable-cursor formal is used as an AddCursor base"
    FlatParentChildDependency -> "a recursive call's result feeds another (parent-child dependency)"
    FlatCallerEndNotValueEnd -> "a caller passes an end cursor that is not the value's own end"
    FlatNotVoidReturn -> "the function returns a value; the loop discards per-element results"
    FlatAbiNotMutCursors -> "the leading ABI formals are not all mutable cursors"
    FlatNotSingleLinearTyCon -> "not a traversal over exactly one Linear (flat AoS) datatype"
    FlatNoInputCursor -> "no top-level case over a dereferenced mutable input cursor"
    FlatNoInputEnd -> "the traversal's end cursor could not be identified"
    FlatVariantArgs -> "an argument past the ABI block is not invariant across the recursion"
    FlatUnerasableCall -> "a self-call the loop body cannot erase"
    FlatObservableEffect -> "the body has an observable effect the loop would reorder"
    FlatNonTraversalInputUpdate -> "the input cursor is advanced by something other than the traversal"

-- | One report line for one function.
flatReportLine :: FunDef3 -> Either FlatDecline () -> String
flatReportLine fn outcome =
  fromVar (funName fn) ++ ": " ++
  case outcome of
    Right () -> "loopified"
    Left d -> "declined: " ++ flatDeclineReason d

hasNonAbiMutFormalAddCursorUse :: [Var] -> [Ty3] -> Exp3 -> Bool
hasNonAbiMutFormalAddCursorUse args tys body =
  let flatAbiArgs = S.fromList (take flatAbiCursorCount args)
      mutFormals = S.fromList [ arg | (arg, ty) <- zip args tys, isMutCursorTy ty ]
      nonAbiMutFormals = mutFormals `S.difference` flatAbiArgs
   in not . S.null $ addCursorSources body `S.intersection` nonAbiMutFormals

isGeneratedPackedHelper :: Var -> Bool
isGeneratedPackedHelper v =
  or [ isCopyFunName v
     , isCopySansPtrsFunName v
     , isPrinterName v
     , isTravFunName v
     , isUnpackerName v
     , isRelOffsetsFunName v
     ]

repairMutAddCursorSources :: M.Map Var Ty3 -> Exp3 -> PassM Exp3
repairMutAddCursorSources env ex =
  case ex of
    LetE (v, locs, ty, rhs) bod -> do
      rhs' <- repairMutAddCursorSources env rhs
      bod' <- repairMutAddCursorSources (M.insert v ty env) bod
      pure $ LetE (v, locs, ty, rhs') bod'
    IfE a b c -> IfE <$> go a <*> go b <*> go c
    MkProdE es -> MkProdE <$> mapM go es
    ProjE i e -> ProjE i <$> go e
    CaseE scrt brs -> do
      scrt' <- go scrt
      brs' <- mapM (\(dc, vs, rhs) -> do
                       rhs' <- go rhs
                       pure (dc, vs, rhs')) brs
      pure $ CaseE scrt' brs'
    DataConE loc dc es -> DataConE loc dc <$> mapM go es
    TimeIt e ty b -> TimeIt <$> go e <*> pure ty <*> pure b
    WithArenaE v e -> WithArenaE v <$> go e
    SpawnE v loc es -> SpawnE v loc <$> mapM go es
    MapE (v, ty, rhs) bod -> do
      rhs' <- go rhs
      bod' <- go bod
      pure $ MapE (v, ty, rhs') bod'
    FoldE (v1, t1, r1) (v2, t2, r2) bod -> do
      r1' <- go r1
      r2' <- go r2
      bod' <- go bod
      pure $ FoldE (v1, t1, r1') (v2, t2, r2') bod'
    Ext ext -> repairMutAddCursorSourcesExt env ext
    _ -> pure ex
  where
    go = repairMutAddCursorSources env

repairMutAddCursorSourcesExt :: M.Map Var Ty3 -> E3Ext () Ty3 -> PassM Exp3
repairMutAddCursorSourcesExt env ext =
  case ext of
    AddCursor cur rhs -> do
      rhs' <- repairMutAddCursorSources env rhs
      case M.lookup cur env of
        Just MutCursorTy -> do
          deref <- gensym "deref_addcursor"
          pure $ LetE (deref, [], CursorTy, Ext $ DerefMutCursor cur)
                      (Ext $ AddCursor deref rhs')
        _ -> pure $ Ext $ AddCursor cur rhs'
    -- Fails CLOSED via 'traverseExtExps': every other form's expression
    -- children are still visited, so a form not named above never leaves a
    -- self-call or an un-repaired mutable-cursor use unvisited underneath it.
    _ -> Ext <$> traverseExtExps (repairMutAddCursorSources env) ext

-- | See the identically-named function in 'Gibbon.Passes.LoopifyTraversals'
-- (a separate copy, not shared code): stamps the INTERNAL 'Loopified'
-- marker, never the user's own 'MayVectorize' annotation.
stampLoopified :: FunDef3 -> FunDef3
stampLoopified fn@FunDef{funMeta} =
  fn { funMeta = funMeta { funOpt = Loopified : filter (/= Loopified) (funOpt funMeta) } }

-- | The minimal role information needed for flat AoS loopification.
data FlatCandidate = FlatCandidate
  { fcInputEnd    :: Var
  , fcInputCursor :: Var
  } deriving (Show)

flatCandidateInfo :: DDefs3 -> FunDef3 -> Either FlatDecline FlatCandidate
flatCandidateInfo ddefs FunDef{funName, funArgs, funTy, funBody} = do
  refuse FlatNotVoidReturn (isVoidTy (snd funTy))
  refuse FlatAbiNotMutCursors (all isMutCursorTy (take flatAbiCursorCount (fst funTy)))
  maybe (Left FlatNotSingleLinearTyCon) (const (Right ()))
        (singleMentionedNonSoATyCon ddefs funBody)
  inputCursor <- maybe (Left FlatNoInputCursor) Right (topCaseInputCursor funBody)
  inputEnd <-
    maybe (Left FlatNoInputEnd) Right $
      case inferInputEndFromABI funArgs inputCursor of
        Just end -> Just end
        Nothing -> inferInputEndFromSelfCall funName inputCursor (S.fromList funArgs) funBody
  -- Every formal past the ABI cursor block is read once, at function entry,
  -- and reused for every element of the loop.  That is only faithful to the
  -- recursion if the recursion passes it through unchanged.
  refuse FlatVariantArgs
         (all (`S.member` trulyInvariantArgs funName funArgs funBody)
              (drop flatAbiCursorCount funArgs))
  refuse FlatUnerasableCall (not (hasUnerasableCall funName funBody))
  refuse FlatObservableEffect (not (hasObservableEffect funBody))
  refuse FlatNonTraversalInputUpdate
         (not (hasNonTraversalInputUpdate funName funArgs inputCursor funBody))
  pure $ FlatCandidate inputEnd inputCursor
  where
    refuse d ok = if ok then Right () else Left d

-- | The one datatype this body traverses, when it is a flat AoS one.
--
-- 'Linear' is required explicitly rather than "anything but 'FullyFactored'":
-- that phrasing also admitted 'Mixed', which 'Gibbon.Language.Syntax'
-- documents as unimplemented.
singleMentionedNonSoATyCon :: DDefs3 -> Exp3 -> Maybe TyCon
singleMentionedNonSoATyCon ddefs body = do
  let tycons = S.toList . S.fromList $ mapMaybe dconTyCon (collectMentionedDataCons body)
  tycon <- listToMaybe tycons
  guard (length tycons == 1)
  let ddef = lookupDDef ddefs tycon
  guard (memLayout ddef == Linear)
  pure tycon
  where
    -- A constructor name shared by two datatypes cannot be resolved to one of
    -- them here, and picking arbitrarily would decide the layout question by
    -- map order.
    dconTyCon dcon =
      case [ fromVar tyName | (_k, DDef{tyName, dataCons}) <- M.toList ddefs
                            , (dc, _) <- dataCons
                            , dc == dcon ] of
        [tycon] -> Just tycon
        _ -> Nothing

isVoidTy :: Ty3 -> Bool
isVoidTy (ProdTy []) = True
isVoidTy _ = False

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

-- | Mutable flat AoS cursorization passes packed input end cursors first and the
-- corresponding packed input starts near the end of the argument list.  Pair the
-- top-level case cursor with its stable end by that ABI position before falling
-- back to recursive-call evidence.
inferInputEndFromABI :: [Var] -> Var -> Maybe Var
inferInputEndFromABI funArgs inputCursor = do
  inputIx <- elemIndex inputCursor (drop flatAbiCursorCount funArgs)
  listToMaybe (drop inputIx funArgs)

-- | An operation whose ORDER the loop would change.
--
-- The loop visits nodes in memory order; the recursion visited them in DFS
-- order.  Values agree either way, but anything observable does not: a map
-- that prints each leaf and prints a separator between its two recursive
-- calls emits `3 X 4 X 4 X 5` recursively and `X X 3 4 X 4 5` as a loop.
--
-- 'primEffectClass' is the SoA pass's classification, reused rather than
-- restated, and it has no default: a primitive it has not classified is
-- 'EffUnsupported'.  Trapping arithmetic ('EffPartial') is not refused --
-- reordering two aborts is not observable, and a body that both traps and
-- prints is already refused for the printing.
hasObservableEffect :: Exp3 -> Bool
hasObservableEffect body =
  any unsupported (collectPrimApps body)
  where
    unsupported p = primEffectClass p == EffUnsupported

collectPrimApps :: Exp3 -> [Prim Ty3]
collectPrimApps ex =
  case ex of
    PrimAppE p args -> p : concatMap collectPrimApps args
    AppE _ _ _ args -> concatMap collectPrimApps args
    SpawnE _ _ args -> concatMap collectPrimApps args
    LetE (_, _, _, rhs) bod -> collectPrimApps rhs ++ collectPrimApps bod
    IfE a b c -> concatMap collectPrimApps [a, b, c]
    MkProdE es -> concatMap collectPrimApps es
    ProjE _ e -> collectPrimApps e
    CaseE scrt brs -> collectPrimApps scrt ++ concatMap (collectPrimApps . thd3) brs
    DataConE _ _ es -> concatMap collectPrimApps es
    TimeIt e _ _ -> collectPrimApps e
    WithArenaE _ e -> collectPrimApps e
    MapE (_, _, e1) e2 -> collectPrimApps e1 ++ collectPrimApps e2
    FoldE (_, _, e1) (_, _, e2) e3 -> concatMap collectPrimApps [e1, e2, e3]
    Ext ext -> concatMap collectPrimApps (extExps ext)
    _ -> []

-- | A call in the body that erasure cannot remove.
--
-- 'eraseSelfCalls' rewrites `AppE f | f == funName` and nothing else, so any
-- other call survives verbatim into the loop body and re-runs once per node,
-- consuming whatever input it consumes each time.  A 'SpawnE' is refused even
-- when it is a self-call: erasure has no equation for one.
hasUnerasableCall :: Var -> Exp3 -> Bool
hasUnerasableCall funName body = any unerasable (collectApps body)
  where
    unerasable (AppE fn _ _ _) = fn /= funName
    unerasable SpawnE{} = True
    unerasable _ = False

hasNonTraversalInputUpdate :: Var -> [Var] -> Var -> Exp3 -> Bool
hasNonTraversalInputUpdate funName funArgs inputCursor body =
  case elemIndex inputCursor inputStartFormals of
    Nothing -> False
    Just traversalIx -> any (updatesOtherInput traversalIx) selfCallInputStarts
  where
    inputStartFormals = drop flatAbiCursorCount funArgs
    inputStartCount = length inputStartFormals
    formals = S.fromList funArgs
    selfCallInputStarts =
      [ drop (length args - inputStartCount) args
      | AppE fn _ _ args <- collectApps body
      , fn == funName
      , length args >= inputStartCount
      ]
    updatesOtherInput traversalIx starts =
      or [ not (isFormalVar arg)
         | (ix, arg) <- zip [0 :: Int ..] starts
         , ix /= traversalIx
         ]
    isFormalVar (VarE v) = v `S.member` formals
    isFormalVar _ = False

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

-- | Every call node reachable in the expression -- 'AppE' and 'SpawnE'
-- alike -- including one nested inside another call's own arguments or a
-- 'PrimAppE's arguments; either position previously fell through unseen,
-- hiding a self-call from both 'eraseSelfCalls' and
-- 'inferInputEndFromSelfCall'.
collectApps :: Exp3 -> [Exp3]
collectApps ex =
  case ex of
    AppE _ _ _ args -> ex : concatMap collectApps args
    SpawnE _ _ args -> ex : concatMap collectApps args
    PrimAppE _ args -> concatMap collectApps args
    LetE (_, _, _, rhs) bod -> collectApps rhs ++ collectApps bod
    IfE a b c -> collectApps a ++ collectApps b ++ collectApps c
    MkProdE es -> concatMap collectApps es
    ProjE _ e -> collectApps e
    CaseE scrt brs -> collectApps scrt ++ concatMap (collectApps . thd3) brs
    DataConE _ _ es -> concatMap collectApps es
    TimeIt e _ _ -> collectApps e
    WithArenaE _ e -> collectApps e
    MapE (_, _, e1) e2 -> collectApps e1 ++ collectApps e2
    FoldE (_, _, e1) (_, _, e2) e3 -> concatMap collectApps [e1, e2, e3]
    Ext ext -> collectAppsExt ext
    _ -> []

collectAppsExt :: E3Ext () Ty3 -> [Exp3]
collectAppsExt ext = concatMap collectApps (extExps ext)

addCursorSources :: Exp3 -> S.Set Var
addCursorSources ex =
  case ex of
    VarE{} -> S.empty
    LitE{} -> S.empty
    CharE{} -> S.empty
    FloatE{} -> S.empty
    LitSymE{} -> S.empty
    AppE _ _ _ args -> S.unions (map addCursorSources args)
    PrimAppE _ args -> S.unions (map addCursorSources args)
    LetE (_, _, _, rhs) bod -> addCursorSources rhs `S.union` addCursorSources bod
    IfE a b c -> S.unions (map addCursorSources [a, b, c])
    MkProdE es -> S.unions (map addCursorSources es)
    ProjE _ e -> addCursorSources e
    CaseE scrt brs -> addCursorSources scrt `S.union` S.unions (map (addCursorSources . thd3) brs)
    DataConE _ _ es -> S.unions (map addCursorSources es)
    TimeIt e _ _ -> addCursorSources e
    WithArenaE _ e -> addCursorSources e
    SpawnE _ _ es -> S.unions (map addCursorSources es)
    MapE (_, _, rhs) bod -> addCursorSources rhs `S.union` addCursorSources bod
    FoldE (_, _, e1) (_, _, e2) e3 -> S.unions (map addCursorSources [e1, e2, e3])
    Ext ext -> addCursorSourcesExt ext
    _ -> S.empty

addCursorSourcesExt :: E3Ext () Ty3 -> S.Set Var
addCursorSourcesExt ext =
  case ext of
    AddCursor cur rhs -> S.insert cur (addCursorSources rhs)
    _ -> S.unions (map addCursorSources (extExps ext))

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
eraseSelfCallsExt funName = mapExtExps (eraseSelfCalls funName)

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
exposeRhsLetsExt = mapExtExps exposeRhsLets

peelLets :: Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3)
peelLets ex =
  case ex of
    LetE bind bod ->
      let (binds, tailExp) = peelLets bod
       in (bind : binds, tailExp)
    _ -> ([], ex)

mkLets3 :: [(Var, [()], Ty3, Exp3)] -> Exp3 -> Exp3
mkLets3 binds bod = foldr LetE bod binds
