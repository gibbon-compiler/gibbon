{-# LANGUAGE TupleSections #-}
-- | Propagate scalar-count footer metadata across SoA producer calls.
--
-- Builders annotated with `OPT:StoreScalarCounts` establish valid counts from
-- scratch.  Loopified traversals then maintain those counts while walking
-- chunks.  This nano-pass covers the remaining shape-preserving producer case:
-- a cursorized SoA function that consumes one packed value and writes a fresh
-- packed value with the same cursor-array shape, but does not itself write
-- scalar-count metadata.
--
-- "Shape preserving" is a proof obligation, not an ABI shape.  A function that
-- drops or duplicates elements has exactly the same cursor ABI as a map, and
-- stamping the input's per-chunk counts onto its (shorter) output installs
-- counts a loopified consumer will happily use as an unchecked loop trip
-- count.  So `producerShape` additionally requires
-- `isShapePreservingProducer`: every user constructor branch writes exactly one
-- tag on every path, that tag is the branch's own constructor, and the branch
-- recurses exactly once per packed field.  Producers that cannot be proven
-- shape preserving get no copy at all, which is the safe direction.
--
-- The important complexity invariant is that this pass never scans elements.
-- It emits one runtime call per materialized producer call.  The runtime helper
-- walks the footer chains for each homogeneous SoA buffer, so the cost is
-- O(number-of-buffers * number-of-chunks).  Selective buffer sharing does not
-- need this copy, because shared buffers point at the already-counted input
-- buffer.
--
-- We deliberately avoid recursive function bodies.  Copying footer chains at
-- every recursive self-call would reintroduce avoidable overhead.  The intended
-- use is pipeline-level propagation: once a producer call materializes a fresh
-- packed value, copy the per-buffer chunk metadata to the output value before a
-- later loopified traversal consumes it.
module Gibbon.Passes.ScalarCountPropagation
  ( propagateScalarCounts
  , countPropagatedProducers
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L3.Abi ( CursorPairShape(..), soaInputCursorShapes, soaOutputCursorShape )
import qualified Gibbon.L3.Syntax as L3
import Gibbon.L3.Traverse (extExps, traverseExtExps)

data ProducerShape = ProducerShape
  { psInput :: CursorPairShape
  , psOutput :: CursorPairShape
  }
  deriving (Eq, Ord, Show)

propagateScalarCounts :: L3.Prog3 -> PassM L3.Prog3
propagateScalarCounts prog@Prog{ddefs, fundefs, mainExp} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_StoreScalarFieldCounts dflags
      producerShapes =
        if enabled
        then producerShapesFor ddefs fundefs
        else M.empty
  if not enabled || M.null producerShapes
    then pure prog
    else do
      fds' <- mapM (rewriteFun producerShapes) (M.elems fundefs)
      mainExp' <- mapM (\(e, ty) -> (,ty) <$> rewriteExp producerShapes e) mainExp
      pure $
        prog
          { fundefs = M.fromList [ (funName f, f) | f <- fds' ]
          , mainExp = mainExp'
          }

rewriteFun :: M.Map Var ProducerShape -> L3.FunDef3 -> PassM L3.FunDef3
rewriteFun producerShapes fn@FunDef{funBody, funMeta}
  | funRec funMeta == NotRec = do
      body_p <- rewriteExp producerShapes funBody
      pure fn { funBody = body_p }
  | otherwise = pure fn

rewriteExp :: M.Map Var ProducerShape -> L3.Exp3 -> PassM L3.Exp3
rewriteExp producerShapes = go
  where
    go ex =
      case ex of
        L3.LetE (v, locs, ty, rhs) bod -> do
          rhs' <- go rhs
          bod' <- go bod
          copyBinds <- copyBindsForRhs producerShapes rhs'
          pure $ L3.LetE (v, locs, ty, rhs') (L3.mkLets copyBinds bod')
        L3.IfE a b c -> L3.IfE <$> go a <*> go b <*> go c
        L3.CaseE scrt brs ->
          L3.CaseE <$> go scrt
                   <*> mapM (\(dc, vars, rhs) -> (dc, vars,) <$> go rhs) brs
        L3.MkProdE ls -> L3.MkProdE <$> mapM go ls
        L3.ProjE i e -> L3.ProjE i <$> go e
        L3.PrimAppE p args -> L3.PrimAppE p <$> mapM go args
        L3.TimeIt e ty b -> L3.TimeIt <$> go e <*> pure ty <*> pure b
        L3.WithArenaE v e -> L3.WithArenaE v <$> go e
        L3.SpawnE fn locs args -> L3.SpawnE fn locs <$> mapM go args
        L3.MapE (v, ty, rhs) bod -> L3.MapE <$> ((v, ty,) <$> go rhs) <*> go bod
        L3.FoldE (v1, ty1, rhs1) (v2, ty2, rhs2) bod ->
          L3.FoldE
            <$> ((v1, ty1,) <$> go rhs1)
            <*> ((v2, ty2,) <$> go rhs2)
            <*> go bod
        L3.DataConE loc dc args -> L3.DataConE loc dc <$> mapM go args
        L3.Ext ext -> L3.Ext <$> rewriteExt ext
        _ -> pure ex

    rewriteExt = traverseExtExps go

copyBindsForRhs
  :: M.Map Var ProducerShape
  -> L3.Exp3
  -> PassM [(Var, [()], L3.Ty3, L3.Exp3)]
copyBindsForRhs producerShapes rhs =
  case rhs of
    L3.AppE fn _ _ args
      | Just ProducerShape{psInput, psOutput} <- M.lookup fn producerShapes
      , Just srcEnds <- argVar (cpsEndArgIx psInput) args
      , Just dstEnds <- argVar (cpsEndArgIx psOutput) args
      , cpsLen psInput == cpsLen psOutput -> do
          copyVar <- gensym "scalar_count_copy"
          pure
            [ ( copyVar
              , []
              , L3.ProdTy []
              , L3.Ext $ L3.ScalarCountCopyAll (cpsLen psInput) dstEnds srcEnds
              )
            ]
    _ -> pure []

producerShapesFor :: DDefs L3.Ty3 -> L3.FunDefs3 -> M.Map Var ProducerShape
producerShapesFor ddefs fundefs =
  M.mapMaybe (producerShape ddefs tagWriters) fundefs
  where
    tagWriters = tagWritingFuns fundefs

-- | Recognize a producer whose per-chunk element counts may be copied from its
-- input.
--
-- Matching the SoA cursor ABI is *not* evidence that a function preserves
-- shape: a function that drops or duplicates elements has exactly the same ABI.
-- Copying the input's footer counts onto such an output installs counts that
-- are far too large, which a later loopified consumer then uses as an
-- unchecked loop trip count and writes past the end of the output chunk.  So
-- the producer must additionally be *provably* shape preserving: every user
-- constructor branch must write exactly one constructor tag on every path,
-- that tag must be the branch's own constructor, and the branch must recurse
-- exactly once per packed field.  When that cannot be proven we emit nothing,
-- which leaves the output's counts unpropagated -- the safe direction.
producerShape :: DDefs L3.Ty3 -> S.Set Var -> L3.FunDef3 -> Maybe ProducerShape
producerShape ddefs tagWriters fn
  | bodyWritesScalarCounts (funBody fn) = Nothing
  | not (isShapePreservingProducer ddefs tagWriters fn) = Nothing
  | otherwise =
      case (soaInputCursorShapes fn, soaOutputCursorShape fn) of
        ([inputShape], Just outputShape)
          | cpsLen inputShape == cpsLen outputShape ->
              Just $ ProducerShape inputShape outputShape
        _ -> Nothing

-- | Producers whose fresh SoA output values are guaranteed to receive valid
-- scalar-count footer metadata from this pass, because (a) they are provably
-- shape preserving and ABI-recognized, and (b) every call site in the program
-- is one this pass actually rewrites.
--
-- `LoopifyTraversals` uses this to decide whether the counts a loopified
-- traversal reads are guaranteed to have been written.
countPropagatedProducers :: L3.Prog3 -> S.Set Var
countPropagatedProducers Prog{ddefs, fundefs, mainExp} =
  S.fromList
    [ fnName
    | (fnName, shape) <- M.toList shapes
    , all (callSiteCovered fnName shape) callSites
    ]
  where
    shapes = producerShapesFor ddefs fundefs

    -- (enclosing function, is the enclosing context rewritten by this pass,
    --  is this call the direct RHS of a LetE, call expression)
    callSites =
      concat
        [ [ (Just (funName fd), funRec (funMeta fd) == NotRec, direct, app)
          | (direct, app) <- collectDirectCalls (funBody fd)
          ]
        | fd <- M.elems fundefs
        ]
        ++ [ (Nothing, True, direct, app)
           | (m, _) <- maybe [] (:[]) mainExp, (direct, app) <- collectDirectCalls m
           ]

    callSiteCovered fnName ProducerShape{psInput, psOutput} (enclosing, rewritten, direct, (callee, args))
      | callee /= fnName = True
      -- A producer's own recursive self-calls build into the same output
      -- buffers as the outermost call, so the single copy emitted at the
      -- materialization boundary already covers them.  This pass deliberately
      -- never rewrites recursive bodies.
      | enclosing == Just fnName = True
      | not rewritten = False
      -- `copyBindsForRhs` only ever attaches a copy to a call that is the
      -- immediate RHS of a LetE (see Note [Coverage must mirror emission]).
      -- Any other position -- a bare IfE/CaseE branch value, a MkProdE
      -- element, a SpawnE, a PrimAppE argument, anything `rewriteExp`'s `go`
      -- does not open up -- gets no copy no matter how its arguments look, so
      -- it must never be reported as covered.
      | not direct = False
      | otherwise =
          cpsLen psInput == cpsLen psOutput
            && argIsVar (cpsEndArgIx psInput) args
            && argIsVar (cpsEndArgIx psOutput) args

    argIsVar ix args =
      case drop ix args of
        L3.VarE _ : _ -> True
        _ -> False

-- Note [Coverage must mirror emission]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- `countPropagatedProducers` decides, for each shape-preserving producer,
-- whether every call to it will actually receive a `ScalarCountCopyAll`.
-- `LoopifyTraversals.countGuaranteedTyCons` treats that decision as a
-- guarantee about the VALUES a loopified consumer will see, so it must be
-- exactly as narrow as what `rewriteExp` (`copyBindsForRhs`) really does --
-- not a structural approximation of it.  `rewriteExp`'s `go` recurses through
-- `LetE`/`IfE`/`CaseE`/`MkProdE`/`ProjE`/`PrimAppE`/`TimeIt`/`WithArenaE`/
-- `SpawnE`/`MapE`/`FoldE`/`DataConE`/`Ext`, and calls `copyBindsForRhs` only
-- from the `LetE` case, on the already-rewritten RHS; a bare `AppE` reached
-- any other way (an `IfE`/`CaseE` branch value, a `MkProdE` element, a
-- `SpawnE`, ...) falls through `go`'s wildcard and is returned untouched, so
-- it never gets a copy.  `collectDirectCalls` below mirrors that exact
-- traversal shape and tags each call site with whether it is the immediate
-- RHS of a `LetE`; `callSiteCovered` refuses every non-direct site outright,
-- so "covered" and "copied" cannot diverge.  Before this, `callSiteCovered`
-- asked only whether a call's arguments were plain variables, which a
-- non-let-bound call satisfies just as easily as a let-bound one -- so a
-- producer called from, say, an `IfE` branch was wrongly certified
-- "count-guaranteed" while its output's footers were never actually copied.
-- A loopified consumer fed that value reads its footers as pristine zero (an
-- untouched chunk reads back the same as a genuine zero-count one), which
-- silently looks like an empty chunk
-- rather than a wrong one.  Proven at the IR level in
-- tests/ScalarCountPropagation.hs
-- (`case_vw09_step82_coverage_gate_must_not_claim_if_branch_call_is_covered`).

-- | Every direct call in an expression, each tagged with whether it is the
-- immediate RHS of a `LetE` -- the only position `copyBindsForRhs` can attach
-- a copy to.  See Note [Coverage must mirror emission].  Unlike `go`, this
-- traversal still recurses into every position (including inside a bare
-- `AppE`'s own arguments) so that a producer call buried anywhere is still
-- found and correctly tagged `False`, rather than silently missed.
collectDirectCalls :: L3.Exp3 -> [(Bool, (Var, [L3.Exp3]))]
collectDirectCalls ex =
  case ex of
    L3.AppE f _ _ args -> (False, (f, args)) : concatMap collectDirectCalls args
    L3.SpawnE f _ args -> (False, (f, args)) : concatMap collectDirectCalls args
    L3.LetE (_, _, _, rhs) bod ->
      case rhs of
        L3.AppE f _ _ args -> (True, (f, args)) : concatMap collectDirectCalls args ++ collectDirectCalls bod
        _ -> collectDirectCalls rhs ++ collectDirectCalls bod
    L3.IfE a b c -> concatMap collectDirectCalls [a, b, c]
    L3.CaseE scrt brs -> collectDirectCalls scrt ++ concatMap (\(_, _, r) -> collectDirectCalls r) brs
    L3.MkProdE ls -> concatMap collectDirectCalls ls
    L3.ProjE _ e -> collectDirectCalls e
    L3.PrimAppE _ args -> concatMap collectDirectCalls args
    L3.TimeIt e _ _ -> collectDirectCalls e
    L3.WithArenaE _ e -> collectDirectCalls e
    L3.MapE (_, _, rhs) bod -> collectDirectCalls rhs ++ collectDirectCalls bod
    L3.FoldE (_, _, r1) (_, _, r2) bod -> concatMap collectDirectCalls [r1, r2, bod]
    L3.DataConE _ _ args -> concatMap collectDirectCalls args
    L3.Ext ext -> collectDirectCallsExt ext
    _ -> []

collectDirectCallsExt :: L3.E3Ext () L3.Ty3 -> [(Bool, (Var, [L3.Exp3]))]
collectDirectCallsExt ext = concatMap collectDirectCalls (extExps ext)

-- | Every function that can (transitively) write a constructor tag.  Calling
-- one of these from a producer body means the callee may contribute output
-- elements this analysis cannot account for.
tagWritingFuns :: L3.FunDefs3 -> S.Set Var
tagWritingFuns fundefs = fixpoint direct
  where
    direct = S.fromList [ funName fd | fd <- M.elems fundefs, writesTag (funBody fd) ]

    calleesOf = M.fromList [ (funName fd, map fst (collectCalls (funBody fd))) | fd <- M.elems fundefs ]

    fixpoint seen =
      let seen' =
            seen `S.union`
              S.fromList
                [ f
                | (f, cs) <- M.toList calleesOf
                , any (`S.member` seen) cs
                ]
       in if seen' == seen then seen else fixpoint seen'

    writesTag ex = bsMaxTags (scanShape "" S.empty ex) > 0 || not (bsOk (scanShape "" S.empty ex))

-- | Collect every direct call (function name, arguments) in an expression.
collectCalls :: L3.Exp3 -> [(Var, [L3.Exp3])]
collectCalls ex =
  case ex of
    L3.AppE f _ _ args -> (f, args) : concatMap collectCalls args
    L3.SpawnE f _ args -> (f, args) : concatMap collectCalls args
    L3.LetE (_, _, _, rhs) bod -> collectCalls rhs ++ collectCalls bod
    L3.IfE a b c -> concatMap collectCalls [a, b, c]
    L3.CaseE scrt brs -> collectCalls scrt ++ concatMap (\(_, _, r) -> collectCalls r) brs
    L3.MkProdE ls -> concatMap collectCalls ls
    L3.ProjE _ e -> collectCalls e
    L3.PrimAppE _ args -> concatMap collectCalls args
    L3.TimeIt e _ _ -> collectCalls e
    L3.WithArenaE _ e -> collectCalls e
    L3.MapE (_, _, rhs) bod -> collectCalls rhs ++ collectCalls bod
    L3.FoldE (_, _, r1) (_, _, r2) bod -> concatMap collectCalls [r1, r2, bod]
    L3.DataConE _ _ args -> concatMap collectCalls args
    L3.Ext ext -> collectCallsExt ext
    _ -> []

collectCallsExt :: L3.E3Ext () L3.Ty3 -> [(Var, [L3.Exp3])]
collectCallsExt ext = concatMap collectCalls (extExps ext)

-- | Abstract per-path summary used by the shape-preservation check: how many
-- constructor tags the expression writes (as a min/max interval over control
-- flow paths), which constructors those are, and how many self recursive calls
-- happen.  `bsOk` becomes False when a form is seen that could add output
-- elements in a way this analysis cannot bound.
data ShapeScan = ShapeScan
  { bsOk :: Bool
  , bsMinTags :: Int
  , bsMaxTags :: Int
  , bsTagCons :: S.Set DataCon
  , bsMinSelf :: Int
  , bsMaxSelf :: Int
  }
  deriving (Eq, Ord, Show)

scanUnit :: ShapeScan
scanUnit = ShapeScan True 0 0 S.empty 0 0

scanBad :: ShapeScan
scanBad = scanUnit { bsOk = False }

scanSeq :: ShapeScan -> ShapeScan -> ShapeScan
scanSeq a b =
  ShapeScan
    { bsOk = bsOk a && bsOk b
    , bsMinTags = bsMinTags a + bsMinTags b
    , bsMaxTags = bsMaxTags a + bsMaxTags b
    , bsTagCons = bsTagCons a `S.union` bsTagCons b
    , bsMinSelf = bsMinSelf a + bsMinSelf b
    , bsMaxSelf = bsMaxSelf a + bsMaxSelf b
    }

scanSeqAll :: [ShapeScan] -> ShapeScan
scanSeqAll = foldl scanSeq scanUnit

scanAlt :: ShapeScan -> ShapeScan -> ShapeScan
scanAlt a b =
  ShapeScan
    { bsOk = bsOk a && bsOk b
    , bsMinTags = min (bsMinTags a) (bsMinTags b)
    , bsMaxTags = max (bsMaxTags a) (bsMaxTags b)
    , bsTagCons = bsTagCons a `S.union` bsTagCons b
    , bsMinSelf = min (bsMinSelf a) (bsMinSelf b)
    , bsMaxSelf = max (bsMaxSelf a) (bsMaxSelf b)
    }

scanAltAll :: [ShapeScan] -> ShapeScan
scanAltAll [] = scanUnit
scanAltAll (x:xs) = foldl scanAlt x xs

-- | Whitelist scan.  `selfName` is the function being analyzed; `tagWriters`
-- is the set of functions that may write constructor tags.
scanShape :: Var -> S.Set Var -> L3.Exp3 -> ShapeScan
scanShape selfName tagWriters = go
  where
    go ex =
      case ex of
        L3.VarE{} -> scanUnit
        L3.LitE{} -> scanUnit
        L3.CharE{} -> scanUnit
        L3.FloatE{} -> scanUnit
        L3.LitSymE{} -> scanUnit
        L3.AppE f _ _ args
          | f == selfName ->
              scanSeqAll (map go args) `scanSeq` scanUnit { bsMinSelf = 1, bsMaxSelf = 1 }
          | f `S.member` tagWriters -> scanBad
          | otherwise -> scanSeqAll (map go args)
        L3.SpawnE{} -> scanBad
        L3.SyncE -> scanUnit
        L3.PrimAppE _ args -> scanSeqAll (map go args)
        L3.LetE (_, _, _, rhs) bod -> go rhs `scanSeq` go bod
        L3.IfE a b c -> go a `scanSeq` (go b `scanAlt` go c)
        L3.MkProdE ls -> scanSeqAll (map go ls)
        L3.ProjE _ e -> go e
        L3.CaseE scrt brs -> go scrt `scanSeq` scanAltAll [ go r | (_, _, r) <- brs ]
        L3.DataConE{} -> scanBad
        L3.TimeIt e _ _ -> go e
        L3.WithArenaE _ e -> go e
        L3.MapE{} -> scanBad
        L3.FoldE{} -> scanBad
        L3.Ext ext -> goExt ext

    goExt ext =
      case ext of
        L3.ReadScalar{} -> scanUnit
        L3.WriteScalar _ _ rhs -> go rhs
        L3.ReadTag{} -> scanUnit
        L3.WriteTag dcon _ -> scanUnit { bsMinTags = 1, bsMaxTags = 1, bsTagCons = S.singleton dcon }
        L3.TagCursor{} -> scanUnit
        L3.ReadTaggedCursor{} -> scanUnit
        L3.ReadCursor{} -> scanUnit
        L3.GrowRegion{} -> scanUnit
        L3.WriteCursorMutable _ rhs -> go rhs
        L3.MakeCursorArray{} -> scanUnit
        L3.IndexCursorArray{} -> scanUnit
        L3.AddCursor _ rhs -> go rhs
        L3.BumpCursorMutable _ rhs -> go rhs
        L3.AddrOfCursor rhs -> go rhs
        L3.DerefMutCursor{} -> scanUnit
        L3.CastPtr{} -> scanUnit
        L3.SubPtr{} -> scanUnit
        L3.NewBuffer{} -> scanUnit
        L3.ScopedBuffer{} -> scanUnit
        L3.NewParBuffer{} -> scanUnit
        L3.ScopedParBuffer{} -> scanUnit
        L3.EndOfBuffer{} -> scanUnit
        L3.MMapFileSize{} -> scanUnit
        L3.SizeOfPacked{} -> scanUnit
        L3.SizeOfScalar{} -> scanUnit
        L3.BoundsCheck{} -> scanUnit
        L3.BoundsCheckVector{} -> scanUnit
        L3.BumpArenaRefCount{} -> scanUnit
        L3.NullCursor -> scanUnit
        L3.InitCursor{} -> scanUnit
        L3.RetE ls -> scanSeqAll (map go ls)
        L3.GetCilkWorkerNum -> scanUnit
        L3.LetAvail _ bod -> go bod
        L3.AllocateTagHere{} -> scanUnit
        L3.AllocateScalarsHere{} -> scanUnit
        L3.StartTagAllocation{} -> scanUnit
        L3.EndTagAllocation{} -> scanUnit
        L3.StartScalarsAllocation{} -> scanUnit
        L3.EndScalarsAllocation{} -> scanUnit
        L3.SSPush{} -> scanUnit
        L3.SSPop{} -> scanUnit
        L3.Assert rhs -> go rhs
        L3.MemCpy _ _ ty ->
          case ty of
            L3.CursorArrayTy{} -> scanUnit
            _ -> scanBad
        -- Everything else (packed tag writes with a computed tag, indirection
        -- and tagged-cursor writes, list/vector writes, loops, SIMD forms,
        -- scalar-count primitives) either changes the element/tag structure of
        -- the output or is not modelled here.  Refuse.
        _ -> scanBad

-- | Is this cursorized function provably a shape-preserving map: does it emit
-- exactly one output element for each input element?
isShapePreservingProducer :: DDefs L3.Ty3 -> S.Set Var -> L3.FunDef3 -> Bool
isShapePreservingProducer ddefs tagWriters fn =
  case splitTopCase (funBody fn) of
    Nothing -> False
    Just (preBinds, _, branches) ->
      let preScan = scanSeqAll [ scanShape selfName tagWriters rhs | (_, _, _, rhs) <- preBinds ]
          userBranches =
            [ br
            | br@(dcon, _, _) <- branches
            , not (isIndirectionTag dcon || isRedirectionTag dcon)
            ]
       in bsOk preScan
            && bsMaxTags preScan == 0
            && bsMaxSelf preScan == 0
            && not (null userBranches)
            && all okBranch userBranches
  where
    selfName = funName fn

    okBranch (dcon, _, rhs) =
      let scan = scanShape selfName tagWriters rhs
          nPacked = length (filter isPackedTy (lookupDataCon ddefs dcon))
       in bsOk scan
            && bsMinTags scan == 1
            && bsMaxTags scan == 1
            && bsTagCons scan == S.singleton dcon
            && bsMinSelf scan == nPacked
            && bsMaxSelf scan == nPacked

splitTopCase :: L3.Exp3 -> Maybe ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3, [(DataCon, [(Var, ())], L3.Exp3)])
splitTopCase = go []
  where
    go acc ex =
      case ex of
        L3.LetE b bod -> go (acc ++ [b]) bod
        L3.CaseE scrt brs -> Just (acc, scrt, brs)
        _ -> Nothing

argVar :: Int -> [L3.Exp3] -> Maybe Var
argVar ix args =
  case drop ix args of
    L3.VarE v : _ -> Just v
    _ -> Nothing

bodyWritesScalarCounts :: L3.Exp3 -> Bool
bodyWritesScalarCounts ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> bodyWritesScalarCounts rhs || bodyWritesScalarCounts bod
    L3.IfE a b c -> any bodyWritesScalarCounts [a,b,c]
    L3.CaseE scrt brs ->
      bodyWritesScalarCounts scrt ||
      any (\(_, _, rhs) -> bodyWritesScalarCounts rhs) brs
    L3.MkProdE ls -> any bodyWritesScalarCounts ls
    L3.ProjE _ e -> bodyWritesScalarCounts e
    L3.PrimAppE _ args -> any bodyWritesScalarCounts args
    L3.TimeIt e _ _ -> bodyWritesScalarCounts e
    L3.WithArenaE _ e -> bodyWritesScalarCounts e
    L3.SpawnE _ _ args -> any bodyWritesScalarCounts args
    L3.MapE (_, _, rhs) bod -> bodyWritesScalarCounts rhs || bodyWritesScalarCounts bod
    L3.FoldE (_, _, rhs1) (_, _, rhs2) bod ->
      any bodyWritesScalarCounts [rhs1, rhs2, bod]
    L3.DataConE _ _ args -> any bodyWritesScalarCounts args
    L3.Ext ext -> extWritesScalarCounts ext
    _ -> False

-- | Fails CLOSED on any extension form this case does not name: rather than
-- assume an unlisted form writes nothing, it recurses into its children via
-- 'extExps', so a 'ScalarCountBump' reachable only through a form added later
-- (a 'RetE', a 'Vec*' node, ...) still disqualifies the producer instead of
-- silently vanishing.
extWritesScalarCounts :: L3.E3Ext () L3.Ty3 -> Bool
extWritesScalarCounts ext =
  case ext of
    L3.ScalarCountBump{} -> True
    L3.ScalarCountSet{} -> True
    L3.ScalarCountCopyAll{} -> True
    _ -> any bodyWritesScalarCounts (extExps ext)
