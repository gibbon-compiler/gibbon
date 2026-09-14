{-# LANGUAGE TupleSections #-}

-- | Assign deferred scalar-count slots and bracket producer calls.
module Gibbon.Passes.AssignScalarCountSlots
  ( assignScalarCountSlots
  , scalarCountProducers
  ) where

import Data.Maybe (isJust)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L3.Traverse (extExps, mapExtExps, traverseExtExps)
import Gibbon.L3.Abi ( CursorPairShape(..), soaOutputCursorShape )
import Gibbon.L3.Syntax as L3

{-

Note [Deferred scalar counts]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A producer annotated @OPT:StoreScalarCounts@ records, per SoA buffer per chunk,
how many elements it wrote there; a loopified consumer reads those counts as its
loop trip counts.  A count that is too large makes the consumer write past the
end of a chunk, so exactness matters more than speed here.

Instead of bumping a footer once per element, the producer increments a global
counter and the batched total is delivered into the correct footer at the two
points where the target can change or is needed:

  per element  : gib_scalar_count_pending[K]++
  at growth    : gib_scalar_count_on_grow flushes before its cyclic transition
  after a call : gib_scalar_count_finalize flushes what is left

Both hooks are required.  A chunk's fill level is only witnessed as it is
abandoned, and a redirection tag in a scalar buffer is byte-indistinguishable
from data, so it cannot be recovered by scanning afterwards.

This counts the same events as the per-element bump and only batches their
delivery, so the footers are identical.  Deriving the count arithmetically
instead -- @(cursor - base) / width@ -- was rejected: it is exact only where the
byte arithmetic holds, and each place it does not (precondition P1 in
LoopifyTraversals, buffers shared by selective buffer sharing, AoS layouts,
the nursery, RAN/indirection tags) fails silently as a short count.

A slot is @base + position@, where @position@ is the buffer's index in the SoA
cursor array (0 = tag buffer, 1.. = field buffers) and @base@ is assigned here
once per producer over the whole program, so two producers cannot collide.

A producer keeps the per-element bump ('noCountSlot') when it cannot be
bracketed: an unrecognized cursor ABI, mutual recursion between producers, or
any call site 'spliceCalls' does not reach.

Note [Coverage must mirror emission]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
'rebaseBumps' moves a producer's accounting onto a slot and 'spliceCalls'
brackets its calls.  If the first happens without the second the slot
accumulates and is never flushed, leaving the footers untouched and a consumer
reading a trip count of zero.  So a producer is deferred only when every call
to it is bracketed: 'countCalls' counts all calls (a total traversal -- no
wildcard, so a new constructor breaks the build), 'countBracketableCalls' walks
the shape 'spliceCalls' does, and unequal means demote to 'noCountSlot'.

The two predicates must agree on BOTH halves of what 'bracketFor' requires:
the syntactic position (an 'AppE' directly in a 'LetE' right-hand side) and
the argument condition ('bracketArgOk' -- the end-array argument must be a
plain variable).  'countBracketableCalls' once checked only the position, so a
call whose end-array argument was not literally a 'VarE' was certified covered
while 'spliceCalls' emitted no bind and no finalize: the slot was never bound,
the footers stayed zero, and a loopified consumer read a trip count of zero
and silently produced empty output, with no diagnostic -- 'flush_slot's
@exit(1)@ needs a flush that never happens, and @--scalar-counts-diff@'s
@atexit@ hook is registered inside the bind that is never called.  The
argument condition is therefore factored into one function both call.

Note [Deferred scalar counts is incompatible with the generational GC]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A slot caches the @GibRegionInfo *@ of the region it counts for.  Under
@--gen-gc@ regions are nursery-allocated and the copying collector relocates
them and rewrites @reg_info@ (gibbon-rts/rts-ng/src/gc.rs) with no hook into
the C-side slot table, so the binding goes stale and later counts are written
where nothing reads them.  @gib_scalar_count_on_promote@ covers only the
relocation inside @gib_grow_region_on_heap@; a collection can move a region at
any allocation point.  The combination is therefore rejected outright.

-}

-- | A footer with this slot is not on the deferred path and keeps the
-- per-element bump.
noCountSlot :: Int
noCountSlot = -1

-- | Mirrors GIB_SCALAR_COUNT_MAX_SLOTS in gibbon-rts/rts-c/gibbon_rts.h.
maxCountSlots :: Int
maxCountSlots = 256

-- | Where a producer's output cursor arrays sit in its argument list.
data OutShape = OutShape
  { osLen      :: Int   -- ^ cursor-array length == number of SoA buffers
  , osEndArgIx :: Int   -- ^ argument index of the output end-cursor array
  }
  deriving (Eq, Show)

-- | Functions that maintain scalar counts, i.e. whose body contains a
-- 'ScalarCountBump'.
scalarCountProducers :: FunDefs3 -> S.Set Var
scalarCountProducers = M.keysSet . M.filter (hasBump . funBody)

assignScalarCountSlots :: Prog3 -> PassM Prog3
assignScalarCountSlots prg@Prog{ddefs, fundefs, mainExp} = do
  dflags <- getDynFlags
  -- The @--gen-gc@ rejection this pass used to carry now lives in
  -- 'Gibbon.Compiler.validateDynFlags'.  It has to run before any pipeline is
  -- chosen: this pass is in the packed branch, so a @--pointer@ build reached
  -- neither the rejection nor anything else that would notice.
  -- See Note [Deferred scalar counts is incompatible with the generational GC].
  let wanted = gopt Opt_DeferScalarCounts dflags || gopt Opt_ScalarCountDiff dflags
  if not wanted
    then pure prg
    else do
      let producers = scalarCountProducers fundefs

      -- Mutual recursion between two producers would put a bracket around a
      -- call that is really a recursive step, rebinding (and so zeroing) a
      -- counter that is still accumulating.
      let calleesOf f = maybe S.empty (callees . funBody) (M.lookup f fundefs)
          mutuallyRecursive =
            S.fromList
              [ f
              | f <- S.toList producers
              , g <- S.toList producers
              , f /= g
              , g `S.member` calleesOf f
              , f `S.member` calleesOf g
              ]

      let abiShapes =
            M.fromList
              [ (f, sh)
              | f <- S.toList producers
              , not (f `S.member` mutuallyRecursive)
              , Just fd <- [M.lookup f fundefs]
              , Just sh <- [outShape fd]
              ]

      -- See Note [Coverage must mirror emission].  A producer is deferred only
      -- if every call to it is one spliceCalls will bracket; a call it cannot
      -- reach would leave that production's counts unflushed and silently
      -- zero.  A producer's own recursive calls are excluded -- those are
      -- deliberately not bracketed.
      let bodies = [ (Just f, funBody fd) | (f, fd) <- M.toList fundefs ]
                     ++ maybe [] (\(e, _) -> [(Nothing, e)]) mainExp
          -- The shape comes from `abiShapes`, which is computed BEFORE
          -- coverage, so asking `bracketArgOk` here is not circular.  A
          -- producer with no recognized shape has nothing to bracket and is
          -- not a candidate in the first place.
          coveredIn f sh =
            and [ countCalls f e == countBracketableCalls sh f e
                | (owner, e) <- bodies, owner /= Just f ]
          shapes = M.filterWithKey coveredIn abiShapes

      let bases = M.fromList (go 0 (L.sort (M.keys shapes)))
            where
              go _ [] = []
              go next (f:fs) =
                let n = maybe 1 osLen (M.lookup f shapes)
                 in (f, next) : go (next + n) fs
          totalSlots = sum [ osLen sh | sh <- M.elems shapes ]

      if totalSlots > maxCountSlots
        then error $
               "assignScalarCountSlots: this program needs " ++ show totalSlots ++
               " deferred scalar-count slots, but the RTS provides " ++
               show maxCountSlots ++ " (GIB_SCALAR_COUNT_MAX_SLOTS). Raise it, " ++
               "or compile without --defer-scalar-counts."
        else do
          let bracketed = M.keysSet bases
          fundefs' <-
            M.traverseWithKey
              (\f fd -> do
                  -- A producer's own body must not bracket its recursive
                  -- calls: the bind belongs at the OUTERMOST call, once per
                  -- production.
                  bod <- spliceCalls bases shapes (S.delete f bracketed)
                           (rebaseBumps
                              ((,) <$> M.lookup f bases <*> M.lookup f shapes)
                              (funBody fd))
                  pure fd { funBody = bod })
              fundefs
          mainExp' <-
            case mainExp of
              Nothing -> pure Nothing
              Just (e, t) -> do
                e' <- spliceCalls bases shapes bracketed e
                pure (Just (e', t))
          pure prg { ddefs = ddefs, fundefs = fundefs', mainExp = mainExp' }

-- | Rewrite a producer's bump slots from cursor-array positions to absolute
-- slots.  Without a base the function keeps the bump ('noCountSlot').
--
-- A producer owns exactly the slots @[base, base + osLen)@, so a position at
-- or past its cursor-array length would rebase onto the NEXT producer's range
-- and add this function's elements to that one's footers.  Such a position is
-- out of range by construction -- it indexes a buffer the function's own
-- output array does not have -- but nothing upstream checks it, so it is
-- checked here and demoted rather than trusted.
rebaseBumps :: Maybe (Int, OutShape) -> Exp3 -> Exp3
rebaseBumps mbase = go
  where
    go ex =
      case ex of
        LetE (v, locs, ty, rhs) bod -> LetE (v, locs, ty, go rhs) (go bod)
        IfE a b c -> IfE (go a) (go b) (go c)
        CaseE scrt brs -> CaseE (go scrt) [ (dc, vs, go rhs) | (dc, vs, rhs) <- brs ]
        MkProdE ls -> MkProdE (L.map go ls)
        ProjE i e -> ProjE i (go e)
        PrimAppE p args -> PrimAppE p (L.map go args)
        TimeIt e t b -> TimeIt (go e) t b
        WithArenaE v e -> WithArenaE v (go e)
        SpawnE f locs args -> SpawnE f locs (L.map go args)
        AppE f rt locs args -> AppE f rt locs (L.map go args)
        DataConE l dc args -> DataConE l dc (L.map go args)
        MapE (v, t, rhs) bod -> MapE (v, t, go rhs) (go bod)
        FoldE (v1,t1,r1) (v2,t2,r2) bod -> FoldE (v1,t1,go r1) (v2,t2,go r2) (go bod)
        Ext (ScalarCountBump dcon footers) ->
          Ext $ ScalarCountBump dcon [ (v, slotFor pos) | (v, pos) <- footers ]
        Ext ext -> Ext (mapExtExps go ext)
        VarE{} -> ex
        LitE{} -> ex
        CharE{} -> ex
        FloatE{} -> ex
        LitSymE{} -> ex
        SyncE -> ex

    slotFor pos =
      case mbase of
        Just (base, sh) | pos >= 0, pos < osLen sh -> base + pos
        _ -> noCountSlot

-- | Wrap every call to a bracketed producer in bind/finalize.  The binders are
-- gensym'd: fixed names are deleted by 'OptimizeL3.removeReDefsExp' when they
-- recur in a scope, which silently unbrackets every call site after the first.
spliceCalls :: M.Map Var Int -> M.Map Var OutShape -> S.Set Var -> Exp3 -> PassM Exp3
spliceCalls bases shapes bracketed = go
  where
    go ex =
      case ex of
        LetE (v, locs, ty, rhs) bod -> do
          rhs' <- go rhs
          bod' <- go bod
          case bracketFor bases shapes bracketed rhs' of
            Nothing -> pure $ LetE (v, locs, ty, rhs') bod'
            Just (base, len, ends) -> do
              bindV <- gensym "scalar_count_bind"
              finV <- gensym "scalar_count_fin"
              -- The region is allocated by the caller, so `ends` already names
              -- live footers here; and the finalize must precede any
              -- ScalarCountCopyAll the propagation pass put in `bod`, which it
              -- does because that pass runs earlier and so its copy is inside
              -- `bod`.
              pure $
                LetE (bindV, [], ProdTy [], Ext $ ScalarCountBind base len ends) $
                  LetE (v, locs, ty, rhs') $
                    LetE (finV, [], ProdTy [], Ext $ ScalarCountFinalize base len ends)
                      bod'
        IfE a b c -> IfE <$> go a <*> go b <*> go c
        CaseE scrt brs ->
          CaseE <$> go scrt
                <*> mapM (\(dc, vs, rhs) -> (dc, vs,) <$> go rhs) brs
        MkProdE ls -> MkProdE <$> mapM go ls
        ProjE i e -> ProjE i <$> go e
        PrimAppE p args -> PrimAppE p <$> mapM go args
        TimeIt e t b -> (\e' -> TimeIt e' t b) <$> go e
        WithArenaE v e -> WithArenaE v <$> go e
        SpawnE f locs args -> SpawnE f locs <$> mapM go args
        AppE f rt locs args -> AppE f rt locs <$> mapM go args
        DataConE l dc args -> DataConE l dc <$> mapM go args
        MapE (v, t, rhs) bod -> MapE <$> ((v, t,) <$> go rhs) <*> go bod
        FoldE (v1,t1,r1) (v2,t2,r2) bod ->
          FoldE <$> ((v1,t1,) <$> go r1) <*> ((v2,t2,) <$> go r2) <*> go bod
        Ext ext -> Ext <$> traverseExtExps go ext
        VarE{} -> pure ex
        LitE{} -> pure ex
        CharE{} -> pure ex
        FloatE{} -> pure ex
        LitSymE{} -> pure ex
        SyncE -> pure ex

bracketFor
  :: M.Map Var Int -> M.Map Var OutShape -> S.Set Var -> Exp3 -> Maybe (Int, Int, Var)
bracketFor bases shapes bracketed rhs =
  case rhs of
    AppE fn _ _ args
      | fn `S.member` bracketed
      , Just base <- M.lookup fn bases
      , Just sh <- M.lookup fn shapes
      , bracketArgOk sh args
      , Just ends <- argVarAt (osEndArgIx sh) args -> Just (base, osLen sh, ends)
    _ -> Nothing

-- | The argument condition 'bracketFor' imposes, factored out so that
-- 'countBracketableCalls' can impose the SAME one.
--
-- 'countBracketableCalls' cannot call 'bracketFor': that needs @bases@ and
-- @shapes@, which are computed FROM coverage.  But the half it was missing
-- needs only the callee's 'OutShape', which is already in @abiShapes@ before
-- coverage runs.  See Note [Coverage must mirror emission].
bracketArgOk :: OutShape -> [Exp3] -> Bool
bracketArgOk sh args = isJust (argVarAt (osEndArgIx sh) args)

argVarAt :: Int -> [Exp3] -> Maybe Var
argVarAt ix as =
  case drop ix as of
    VarE v : _ -> Just v
    _ -> Nothing

-- | Every call to @f@, anywhere.  Pairs with 'countBracketableCalls'; see
-- Note [Coverage must mirror emission].
countCalls :: Var -> Exp3 -> Int
countCalls f = go
  where
    go ex =
      case ex of
        AppE g _ _ args -> (if g == f then 1 else 0) + sum (L.map go args)
        SpawnE g _ args -> (if g == f then 1 else 0) + sum (L.map go args)
        LetE (_, _, _, rhs) bod -> go rhs + go bod
        IfE a b c -> go a + go b + go c
        CaseE scrt brs -> go scrt + sum [ go rhs | (_, _, rhs) <- brs ]
        MkProdE ls -> sum (L.map go ls)
        ProjE _ e -> go e
        PrimAppE _ args -> sum (L.map go args)
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        DataConE _ _ args -> sum (L.map go args)
        MapE (_, _, rhs) bod -> go rhs + go bod
        FoldE (_,_,r1) (_,_,r2) bod -> go r1 + go r2 + go bod
        Ext ext -> sum (L.map go (extExps ext))
        VarE{} -> 0
        LitE{} -> 0
        CharE{} -> 0
        FloatE{} -> 0
        LitSymE{} -> 0
        SyncE -> 0

-- | Calls to @f@ that 'spliceCalls' will actually bracket: an 'AppE' sitting
-- directly in a 'LetE' right-hand side, reached along the same traversal, AND
-- satisfying 'bracketArgOk' -- the same argument condition 'bracketFor'
-- imposes.  A call failing either half gets no bind/finalize, so counting it
-- as covered is how a producer's slot ends up never bound and its footers
-- silently zero.
countBracketableCalls :: OutShape -> Var -> Exp3 -> Int
countBracketableCalls sh f = go
  where
    isCall (AppE g _ _ args) = g == f && bracketArgOk sh args
    isCall _ = False

    go ex =
      case ex of
        LetE (_, _, _, rhs) bod ->
          (if isCall rhs then 1 else 0) + go rhs + go bod
        IfE a b c -> go a + go b + go c
        CaseE scrt brs -> go scrt + sum [ go rhs | (_, _, rhs) <- brs ]
        MkProdE ls -> sum (L.map go ls)
        ProjE _ e -> go e
        PrimAppE _ args -> sum (L.map go args)
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        SpawnE _ _ args -> sum (L.map go args)
        AppE _ _ _ args -> sum (L.map go args)
        DataConE _ _ args -> sum (L.map go args)
        MapE (_, _, rhs) bod -> go rhs + go bod
        FoldE (_,_,r1) (_,_,r2) bod -> go r1 + go r2 + go bod
        Ext ext -> sum (L.map go (extExps ext))
        VarE{} -> 0
        LitE{} -> 0
        CharE{} -> 0
        FloatE{} -> 0
        LitSymE{} -> 0
        SyncE -> 0

-- | Where a producer's output end-cursor array sits, read off the cursorized
-- calling convention.  A producer without a recorded convention, or whose
-- output arrays are not a multi-buffer SoA pair, is left on the bump.
outShape :: FunDef3 -> Maybe OutShape
outShape fn = do
  shape <- soaOutputCursorShape fn
  pure (OutShape (cpsLen shape) (cpsEndArgIx shape))

hasBump :: Exp3 -> Bool
hasBump = go
  where
    go ex =
      case ex of
        Ext ScalarCountBump{} -> True
        LetE (_, _, _, rhs) bod -> go rhs || go bod
        IfE a b c -> any go [a, b, c]
        CaseE scrt brs -> go scrt || any (\(_, _, rhs) -> go rhs) brs
        MkProdE ls -> any go ls
        ProjE _ e -> go e
        PrimAppE _ args -> any go args
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        SpawnE _ _ args -> any go args
        AppE _ _ _ args -> any go args
        DataConE _ _ args -> any go args
        MapE (_, _, rhs) bod -> go rhs || go bod
        FoldE (_,_,r1) (_,_,r2) bod -> go r1 || go r2 || go bod
        Ext ext -> any go (extExps ext)
        VarE{} -> False
        LitE{} -> False
        CharE{} -> False
        FloatE{} -> False
        LitSymE{} -> False
        SyncE -> False

callees :: Exp3 -> S.Set Var
callees = go
  where
    go ex =
      case ex of
        AppE f _ _ args -> S.insert f (S.unions (L.map go args))
        SpawnE f _ args -> S.insert f (S.unions (L.map go args))
        LetE (_, _, _, rhs) bod -> go rhs `S.union` go bod
        IfE a b c -> S.unions [go a, go b, go c]
        CaseE scrt brs -> S.unions (go scrt : [ go rhs | (_, _, rhs) <- brs ])
        MkProdE ls -> S.unions (L.map go ls)
        ProjE _ e -> go e
        PrimAppE _ args -> S.unions (L.map go args)
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        DataConE _ _ args -> S.unions (L.map go args)
        MapE (_, _, rhs) bod -> go rhs `S.union` go bod
        FoldE (_,_,r1) (_,_,r2) bod -> S.unions [go r1, go r2, go bod]
        Ext ext -> S.unions (L.map go (extExps ext))
        VarE{} -> S.empty
        LitE{} -> S.empty
        CharE{} -> S.empty
        FloatE{} -> S.empty
        LitSymE{} -> S.empty
        SyncE -> S.empty

