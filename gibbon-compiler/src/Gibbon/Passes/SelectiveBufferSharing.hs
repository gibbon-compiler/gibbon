-- | Selectively share unchanged SoA buffers.
--
-- The public `selectiveBufferSharing` pass is the current post-loopification
-- L3 nano-pass.  It operates only on functions loopification actually
-- rewrote (the internal `Loopified` marker, not the `OPT:MayVectorize`
-- source annotation -- an annotated function loopification declined to
-- rewrite is left alone here too):
-- the dcon stream can be shared because loopified maps no longer traverse it,
-- and scalar buffers whose loop body is a pure copy can be replaced by one
-- buffer-level indirection.
--
-- This pass expects the loopifier to have emitted the unfused per-buffer loop
-- shape when selective sharing is enabled.  That ordering matters: a fused
-- scalar loop may use one copied buffer as the representative chunk-boundary
-- walker for mutated peer buffers.  Selective sharing should never keep that
-- copied buffer around merely to preserve the walker; instead copied buffers
-- are shared first, and loop fusion is a later nano-pass over the remaining
-- non-shared loops.
--
-- The older L2/pre-loopification version was intentionally removed.  Sharing
-- individual elements in a recursive traversal is the wrong granularity for
-- fully factored SoA layouts; after loopification we can share a whole buffer
-- with one indirection.
--
-- This pass is deliberately opt-in and experimental.  Existing SoA consumers
-- often assume that indirection/redirection boundaries are aligned across peer
-- buffers.  Sharing only one buffer is therefore only safe once the downstream
-- consumers involved in that pipeline can handle independently shared buffers,
-- or once we emit compatible peer-boundary records.
-- The current representation uses a distinct selective-indirection wrapper
-- plus a dcon-buffer mask.  Call-site normalization checks the dcon wrapper
-- first, then unwraps only the masked scalar buffers before passing a
-- selectively shared value to a consumer.  This is intentionally not inserted
-- at every function entry: recursive folds must not pay an unwrap check at
-- each recursive call.
--
module Gibbon.Passes.SelectiveBufferSharing
  ( selectiveBufferSharing
  ) where

import Control.Monad.State.Strict (StateT, lift, modify', runStateT)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isNothing, mapMaybe, maybeToList)
import qualified Data.Set as S

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L2.Syntax (Modality(..))
import qualified Gibbon.L3.Syntax as L3
import Gibbon.L3.Abi ( CursorPairShape(..), soaOutputCursorShape )
import Gibbon.L3.Traverse (extExps, traverseExtExps)
import Gibbon.Passes.LoopifyTraversals
  ( LoopBufferKey
  , LoopBufferSuffix(..)
  , isLoopBufferName
  , isOwnLoopBufferName
  , loopBufferIx
  , loopBufferKey
  , loopBufferSeed
  , loopificationReport
  )

{-
Note [Normalisation coverage is closed over the whole body]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Sharing is committed in 'rewriteLoopifiedFun' BEFORE any consumer is examined,
so every consumer of a shared value must afterwards be found and given an
'UnwrapSelectiveIndirections'.  The guarantee is program-wide: no marked
@(ends, curs)@ pair reaches a call without an unwrap for it already in scope.

Two checks establish it, and both read the SAME selective-pair state.

At each call site, 'checkConsumerArgsResolved' refuses a consumer whose
cursor-array argument does not resolve to a variable -- such a call cannot be
looked up in the selective-pair set at all, so no unwrap could be emitted for
it -- and 'rewriteSpawn' routes a spawned consumer through the same path an
ordinary one takes.

After the walk, 'sweepUnwrapCoverage' re-reads the finished body and refuses
any call handed a marked pair with no unwrap for it in the enclosing let
chain.  The pairs it tests are the walk's OWN accumulated 'ShareEnv', threaded
out of the walk rather than rebuilt: a predicate that must mirror an emitter
but is written twice drifts from it.  The sweep is total over 'PreExp' and
reaches into extension forms through 'extExps', so a call in a position the
rewriting walk does not open up is a refusal rather than an unnormalised
consumer.

Sharing is all-or-nothing per function, so both refusals are available: the
program compiles without @--opt-selective-buffer-sharing@.
-}

selectiveBufferSharing :: L3.Prog3 -> PassM L3.Prog3
selectiveBufferSharing prog@Prog{fundefs, mainExp} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_EnableSelectiveBufferSharing dflags
      loopificationOn = gopt Opt_EnableLoopification dflags || gopt Opt_AutoLoopification dflags
  if enabled && not loopificationOn
    then error $
      "selectiveBufferSharing: --opt-selective-buffer-sharing is enabled, " ++
      "but neither --opt-loopification nor --auto-loopification is.\n" ++
      "Selective buffer sharing only ever rewrites functions loopification " ++
      "already rewrote, so it has nothing to do without it.\n" ++
      "Add --opt-loopification (with --store-scalar-field-counts) or " ++
      "--auto-loopification to the compile command."
  else if not enabled
    then pure prog
    else do
      rewritten <- mapM rewriteSelectiveFun (M.elems fundefs)
      let fds' = [ fd | (fd, _, _) <- rewritten ]
          producerShapes =
            M.fromList
              [ (funName fd, shape)
              | (fd, Just shape, _) <- rewritten
              ]
          shareLines =
            [ fromVar (funName fd) ++ ": " ++
              either (("no buffers shared: " ++) . shareDeclineReason)
                     (const "buffers shared")
                     outcome
            | (fd, _, outcome) <- rewritten
            ]
          consumerShapes =
            M.fromList
              [ (funName fd, candidateInputCursorShapes (funArgs fd) (fst (funTy fd)))
              | fd <- fds'
              ]
      fds'' <- mapM (rewriteSelectiveCallSites producerShapes consumerShapes) fds'
      mainExp' <-
        mapM
          (\(mainBody, mainTy) -> do
              mainBody' <- rewriteSelectiveCallSiteExp producerShapes consumerShapes mainBody
              pure (mainBody', mainTy))
          mainExp
      pure $
        loopificationReport (gopt Opt_LoopificationReport dflags)
                            "selective buffer sharing" shareLines $
        prog
          { fundefs = M.fromList [ (funName f, f) | f <- fds'' ]
          , mainExp = mainExp'
          }

-- | Rewrite one function, sharing copied buffers where that is legal.
--
-- Sharing a buffer installs a selective-indirection wrapper in the function's
-- *output* value.  Every consumer of that value must be normalized with
-- `UnwrapSelectiveIndirections` before it reads the buffer, and the only
-- mechanism this pass has for finding those consumers is
-- `producerOutputPairs`, which needs the producer's (output ends, output
-- cursors) argument pair.  If we cannot identify that pair we cannot mark the
-- produced value as selectively shared, so no call site would ever be
-- normalized and the consumer would read the raw wrapper tag.  Therefore:
-- refuse to share at all unless the output cursor ABI is recognized.
rewriteSelectiveFun :: L3.FunDef3
                    -> PassM (L3.FunDef3, Maybe CursorPairShape, Either ShareDecline ())
rewriteSelectiveFun fn =
  case soaOutputCursorShape fn of
    Nothing -> pure (fn, Nothing, Left ShareNoOutputAbi)
    Just outputShape -> do
      (fn', shared) <- rewriteLoopifiedFun fn
      pure (fn', either (const Nothing) (const (Just outputShape)) shared, shared)

-- | Every ordered (ends, cursors) argument pair a consumer *might* be handed.
--
-- The cursorized SoA ABI is genuinely ambiguous from types alone: a
-- one-packed-input/one-packed-output map has arguments
-- @(in_ends, out_ends, out_curs, in_curs)@ while a two-packed-input fold has
-- @(ends_x, ends_y, curs_x, curs_y)@ -- both are four cursor arrays of the
-- same length.  A positional guess therefore mispairs one input's ends array
-- with another input's cursor array, and the resulting pair is never a marked
-- selective pair, so no unwrap is emitted for a value that *was* shared.  That
-- is a crash, not a missed optimization.
--
-- Instead of guessing, enumerate every ordered pair of equal-length cursor
-- array arguments and let `isSelectivePair` -- which is keyed on the actual
-- variables flowing into the call, not on positions -- decide which pairs are
-- really selectively shared values.  Over-approximating here is harmless: a
-- pair that is not a marked selective pair produces no unwrap.
--
-- Deliberately NOT the recorded convention (`Gibbon.L3.Abi`): this runs over a
-- CALLEE whose formals the caller's arguments flow into, and narrowing it to
-- the pairs the convention names would drop an unwrap the call site needs.
candidateInputCursorShapes :: [Var] -> [L3.Ty3] -> [CursorPairShape]
candidateInputCursorShapes args tys =
  [ CursorPairShape n1 endIx curIx
  | (endIx, _, n1) <- cursorArrays
  , (curIx, _, n2) <- cursorArrays
  , endIx /= curIx
  , n1 == n2
  , n1 > 1
  ]
  where
    cursorArrays =
      [ (ix, v, n)
      | (ix, (v, L3.CursorArrayTy n)) <- zip [0..] (zip args tys)
      ]

rewriteLoopifiedFun :: L3.FunDef3 -> PassM (L3.FunDef3, Either ShareDecline ())
rewriteLoopifiedFun fn@FunDef{funMeta, funBody}
  | Loopified `notElem` funOpt funMeta = pure (fn, Left ShareNotLoopified)
  | otherwise = do
      (body', shared) <- rewriteLoopifiedBody funBody
      pure (fn { funBody = body' }, shared)

-- | Why no buffer was shared in a function.
data ShareDecline
  = ShareNotLoopified
    -- ^ Loopification did not rewrite it, so there are no per-buffer loops.
  | ShareNoOutputAbi
    -- ^ The output cursor ABI is unrecognized, so consumers could not be found
    -- and normalized; sharing would leave them reading a raw wrapper tag.
  | ShareNothingToShare
    -- ^ No buffer in the function is copied unchanged.
  | ShareNoTagBuffer
    -- ^ The tag buffer is not among the shared ones; the wrapper is written
    -- into it, so it has to be.
  | ShareNegativeIx
  | ShareTooWide Int
    -- ^ A buffer index at or past the bitmask's usable width.
  deriving (Eq, Show)

-- | Buffer indices the wrapper's bitmask can represent.  The mask is a 64-bit
-- word with the top two bits reserved.
shareMaskMaxIx :: Int
shareMaskMaxIx = 62

shareDeclineReason :: ShareDecline -> String
shareDeclineReason d =
  case d of
    ShareNotLoopified -> "not loopified, so there are no per-buffer loops to share between"
    ShareNoOutputAbi -> "the output cursor ABI is unrecognized, so consumers could not be normalized"
    ShareNothingToShare -> "no buffer is copied unchanged"
    ShareNoTagBuffer -> "the tag buffer is not among the shareable ones"
    ShareNegativeIx -> "a negative buffer index"
    ShareTooWide ix ->
      "buffer index " ++ show ix ++ " is at or past the share bitmask's limit of " ++
      show shareMaskMaxIx ++ ", so this datatype gets no sharing at all"

data BufferLocs = BufferLocs
  { blInputEnd :: Maybe Var
  , blInLoc :: Maybe Var
  , blOutLoc :: Maybe Var
  , blOutEndLoc :: Maybe Var
  }
  deriving Show

emptyBufferLocs :: BufferLocs
emptyBufferLocs = BufferLocs Nothing Nothing Nothing Nothing

-- | Per-buffer cursors learned from the binds preceding a loop.
--
-- Keyed on the loop too: buffer indices restart at zero in every loop, so
-- keying on the index alone lets one loop's cursors answer for another's.
data BufferEnv = BufferEnv
  { beLocs :: M.Map LoopBufferKey BufferLocs
  }

emptyBufferEnv :: BufferEnv
emptyBufferEnv = BufferEnv M.empty

rewriteLoopifiedBody :: L3.Exp3 -> PassM (L3.Exp3, Either ShareDecline ())
rewriteLoopifiedBody ex = do
  let (binds, tailExp) = unLets3 ex
      globalShares = collectSharePlan binds
  case shareMask globalShares of
    Left d -> pure (ex, Left d)
    Right mask -> do
      (binds', tail') <- go mask emptyBufferEnv binds tailExp
      pure (L3.mkLets binds' tail', Right ())
  where
    collectSharePlan :: [(Var, [()], L3.Ty3, L3.Exp3)] -> S.Set ShareInfo
    collectSharePlan = goPlan emptyBufferEnv S.empty

    goPlan _ shares [] = shares
    goPlan env shares (b@(_, _, _, rhs):bs) =
      case rhs of
        L3.Ext (L3.WhileCursor _ bod) ->
          let loopInfo = classifyLoop bod
              loopShares = S.fromList $ mapMaybeShare env (liShareKeys loopInfo)
           in goPlan env (shares <> loopShares) bs
        _ ->
          goPlan (learnBufferBind env b) shares bs

    shareMask :: S.Set ShareInfo -> Either ShareDecline Int
    shareMask shares
      | S.null shares = Left ShareNothingToShare
      | 0 `S.notMember` ixs = Left ShareNoTagBuffer
      | any (< 0) (S.toList ixs) = Left ShareNegativeIx
      -- The wrapper carries the share set as a bitmask in a 64-bit word, with
      -- the top two bits reserved.  A datatype wide enough to reach buffer 62
      -- therefore gets no sharing at all, silently.
      | Just ix <- L.find (>= shareMaskMaxIx) (S.toList ixs) = Left (ShareTooWide ix)
      | otherwise = Right $ sum [ 2 ^ ix | ix <- S.toList ixs ]
      where
        ixs = S.map siIx shares

    go _ _ [] tailExp = pure ([], tailExp)
    go mask env (b:bs) tailExp =
      case rewriteTopBind env b of
        TopBindNormal env' b' -> do
          (rest, tailExp') <- go mask env' bs tailExp
          pure (b' : rest, tailExp')
        TopBindLoop env' shares mbLoop -> do
          shareBinds <- concat <$> mapM (mkShareBinds mask) (S.toList shares)
          (rest, tailExp') <- go mask env' bs tailExp
          pure (shareBinds ++ maybe rest (: rest) mbLoop, tailExp')

    -- This pass only targets the loopified top-level let-chain.  Preserve the
    -- original tail expression from `unLets3`; recursive subexpressions are
    -- intentionally not searched, because loopification emits the relevant
    -- loops at the outer body level.
    unLets3 :: L3.Exp3 -> ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    unLets3 e =
      case e of
        L3.LetE b bod ->
          let (bs, tailExp) = unLets3 bod
           in (b : bs, tailExp)
        _ -> ([], e)

    mkShareBinds :: Int -> ShareInfo -> PassM [(Var, [()], L3.Ty3, L3.Exp3)]
    mkShareBinds mask ShareInfo{siIx, siInputEnd, siInLoc, siOutLoc, siOutEndLoc} = do
      dst <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_dst")
      src <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_src")
      bound <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_bound")
      room <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_room")
      written <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_written")
      update <- gensym $ toVar ("selective_share_buf" ++ show siIx ++ "_update")
      pure
        [ (dst, [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor siOutLoc)
        , (bound, [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor siOutEndLoc)
          -- The loop this replaces wrote one element at a time and grew the
          -- chunk as it went; the wrapper is written in one go, at whatever
          -- cursor the loop left behind, so it needs its own room.  Growing
          -- rewrites both the cursor and the bound through their loc, so the
          -- write below sees the new chunk.
          -- Bound at IntTy W64, the placeholder the L3 typechecker expects
          -- for this side-effecting form.
        , (room, [], L3.IntTy W64
          , L3.Ext $ L3.BoundsCheck selectiveIndirectionSize bound dst
                       (Just (siOutEndLoc, siOutLoc)) OutputMutable)
        , (src, [], L3.CursorTy, L3.Ext $ L3.DerefMutCursor siInLoc)
        , (written, [], L3.CursorTy, L3.Ext $ L3.WriteCursorSelectiveIndirection dst src siInputEnd (L3.mkLitE64 mask))
        , (update, [], L3.ProdTy [], L3.Ext $ L3.WriteCursorMutable siOutLoc (L3.VarE written))
        ]

data ShareEnv = ShareEnv
  { seSelectivePairs :: S.Set (Var, Var)
  , seAliases :: M.Map Var Var
  }
  deriving Show

emptyShareEnv :: ShareEnv
emptyShareEnv = ShareEnv S.empty M.empty

-- | Everything either side marked, for accumulating a whole body's marks out
-- of the scoped environments the walk makes its decisions with.
unionShareEnv :: ShareEnv -> ShareEnv -> ShareEnv
unionShareEnv a b =
  ShareEnv (seSelectivePairs a `S.union` seSelectivePairs b)
           (seAliases a `M.union` seAliases b)

-- | The rewriting walk, carrying the union of every scoped 'ShareEnv' it
-- decided with.  'sweepUnwrapCoverage' reads that union, so the sweep and the
-- emitter cannot disagree about which pairs are selectively shared.
type Learn = StateT ShareEnv PassM

learn :: ShareEnv -> Learn ()
learn env = modify' (unionShareEnv env)

rewriteSelectiveCallSites
  :: M.Map Var CursorPairShape
  -> M.Map Var [CursorPairShape]
  -> L3.FunDef3
  -> PassM L3.FunDef3
rewriteSelectiveCallSites producers consumers fn@FunDef{funBody} = do
  body' <- rewriteSelectiveCallSiteExp producers consumers funBody
  pure $ fn { funBody = body' }

rewriteSelectiveCallSiteExp
  :: M.Map Var CursorPairShape
  -> M.Map Var [CursorPairShape]
  -> L3.Exp3
  -> PassM L3.Exp3
rewriteSelectiveCallSiteExp producers consumers body = do
  (body', marked) <- runStateT (rewriteWalk producers consumers body) emptyShareEnv
  sweepUnwrapCoverage producers consumers marked body'
  pure body'

rewriteWalk
  :: M.Map Var CursorPairShape
  -> M.Map Var [CursorPairShape]
  -> L3.Exp3
  -> Learn L3.Exp3
rewriteWalk producers consumers = go emptyShareEnv
  where
    go :: ShareEnv -> L3.Exp3 -> Learn L3.Exp3
    go env ex =
      case ex of
        L3.LetE (v, locs, ty, rhs) bod -> do
          (preBinds, rhs') <- rewriteRhs env rhs
          let envAfterPre =
                foldl (learnCallSiteBind producers) env preBinds
              env' = learnCallSiteBind producers envAfterPre (v, locs, ty, rhs')
          learn env'
          bod' <- go env' bod
          pure $ L3.mkLets preBinds (L3.LetE (v, locs, ty, rhs') bod')
        L3.AppE fn cty locs args -> do
          (preBinds, app') <- rewriteApp env fn cty locs args
          pure $ L3.mkLets preBinds app'
        L3.IfE a b c -> L3.IfE <$> go env a <*> go env b <*> go env c
        L3.CaseE scrt brs ->
          L3.CaseE <$> go env scrt
                   <*> mapM (\(dc, vars, rhs) -> (dc, vars,) <$> go env rhs) brs
        L3.MkProdE ls -> L3.MkProdE <$> mapM (go env) ls
        L3.ProjE i e -> L3.ProjE i <$> go env e
        L3.PrimAppE p args -> L3.PrimAppE p <$> mapM (go env) args
        L3.TimeIt e ty b -> L3.TimeIt <$> go env e <*> pure ty <*> pure b
        L3.WithArenaE v e -> L3.WithArenaE v <$> go env e
        L3.SpawnE fn locs args -> do
          (preBinds, spawn') <- rewriteSpawn env fn locs args
          pure $ L3.mkLets preBinds spawn'
        L3.MapE (v, ty, rhs) bod -> L3.MapE <$> ((v, ty,) <$> go env rhs) <*> go env bod
        L3.FoldE (v1, ty1, rhs1) (v2, ty2, rhs2) bod ->
          L3.FoldE
            <$> ((v1, ty1,) <$> go env rhs1)
            <*> ((v2, ty2,) <$> go env rhs2)
            <*> go env bod
        L3.DataConE loc dc args -> L3.DataConE loc dc <$> mapM (go env) args
        L3.Ext ext -> L3.Ext <$> rewriteExt env ext
        _ -> pure ex

    rewriteRhs :: ShareEnv -> L3.Exp3 -> Learn ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    rewriteRhs env rhs =
      case rhs of
        L3.AppE fn cty locs args ->
          rewriteApp env fn cty locs args
        L3.TimeIt timed ty includeAlloc -> do
          (preBinds, timed') <- rewriteTimedBody env timed
          pure (preBinds, L3.TimeIt timed' ty includeAlloc)
        _ -> do
          rhs' <- go env rhs
          pure ([], rhs')

    -- Keep selective-sharing normalization out of benchmark measurements.
    -- The benchmark harness usually wraps a traversal call as:
    --
    --   timeit (let call = f ... inlineCopiedCursorArg ... in ...)
    --
    -- `rewriteApp` may need to hoist the inline cursor-array copy and emit an
    -- `UnwrapSelectiveIndirections` before that call.  If those binds stayed
    -- inside `TimeIt`, the benchmark would charge normalization to the
    -- traversal.  We only hoist from the top-level timed call or the first
    -- let-bound timed call; other shapes fall back to ordinary recursive
    -- rewriting so we do not move code across unknown local dependencies.
    rewriteTimedBody
      :: ShareEnv
      -> L3.Exp3
      -> Learn ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    rewriteTimedBody env timed =
      case timed of
        L3.AppE fn cty locs args ->
          rewriteApp env fn cty locs args
        L3.LetE (v, locs, ty, rhs@(L3.AppE{})) bod -> do
          (preBinds, rhs') <- rewriteRhs env rhs
          let envAfterPre =
                foldl (learnCallSiteBind producers) env preBinds
              env' = learnCallSiteBind producers envAfterPre (v, locs, ty, rhs')
          learn env'
          bod' <- go env' bod
          pure (preBinds, L3.LetE (v, locs, ty, rhs') bod')
        _ -> do
          timed' <- go env timed
          pure ([], timed')

    rewriteApp
      :: ShareEnv
      -> Var
      -> TailRecType
      -> [()]
      -> [L3.Exp3]
      -> Learn ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    rewriteApp env fn cty locs args =
      rewriteCall env fn args (\args' -> L3.AppE fn cty locs args')

    -- A spawned consumer needs the same unwrap an ordinary one does; it used
    -- to get none, because `go` mapped over a 'SpawnE's arguments and never
    -- reached here.
    rewriteSpawn
      :: ShareEnv
      -> Var
      -> [()]
      -> [L3.Exp3]
      -> Learn ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    rewriteSpawn env fn locs args =
      rewriteCall env fn args (\args' -> L3.SpawnE fn locs args')

    rewriteCall
      :: ShareEnv
      -> Var
      -> [L3.Exp3]
      -> ([L3.Exp3] -> L3.Exp3)
      -> Learn ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    rewriteCall env fn args rebuild = do
      let (argBinds, args') = materializeConsumerCursorArgs fn args
          envAfterArgs = foldl (learnCallSiteBind producers) env argBinds
      learn envAfterArgs
      lift $ checkConsumerArgsResolved envAfterArgs fn args'
      unwrapBinds <- lift $ unwrapBindsForCall consumers envAfterArgs fn args'
      pure (argBinds ++ unwrapBinds, rebuild args')

    -- See Note [Normalisation coverage is checked here, not program-wide].
    --
    -- A consumer's cursor-array argument that does not resolve to a variable
    -- cannot be looked up in the selective-pair set, so the call would proceed
    -- UNNORMALISED and the consumer would read the 25-byte wrapper as data --
    -- a loud "Unknown tag" for buffer 0, a silent wrong number for a scalar
    -- buffer.  Only a body where some producer output was actually marked can
    -- contain a wrapper, so the refusal is scoped to those.
    checkConsumerArgsResolved :: ShareEnv -> Var -> [L3.Exp3] -> PassM ()
    checkConsumerArgsResolved env fn args
      | S.null (seSelectivePairs env) = pure ()
      | otherwise =
          case [ ix
               | shape <- fromMaybe [] (M.lookup fn consumers)
               , ix <- [cpsEndArgIx shape, cpsCurArgIx shape]
               , isNothing (argVar ix args)
               ] of
            [] -> pure ()
            ixs -> error $
              "selectiveBufferSharing: call to " ++ show fn ++ " passes a " ++
              "cursor-array argument at position(s) " ++ show ixs ++ " that " ++
              "is not a variable, in a function where selective buffer " ++
              "sharing marked a producer output.\n" ++
              "The call cannot be checked against the shared-buffer set, so " ++
              "no UnwrapSelectiveIndirections can be emitted for it, and the " ++
              "consumer would read the 25-byte sharing wrapper as data.\n" ++
              "Compile without --opt-selective-buffer-sharing."

    -- Cursorized main expressions often pass a packed value start cursor array
    -- through an inline copy expression:
    --
    --   f ends (let copy = InitCursor; _ = MemCpy copy start; copy)
    --
    -- Selective sharing needs to unwrap that copied start array before the
    -- call.  Hoisting just the cursor-array arguments of known SoA consumers
    -- keeps the transformation local and avoids adding entry checks to
    -- recursive consumers.
    materializeConsumerCursorArgs
      :: Var
      -> [L3.Exp3]
      -> ([(Var, [()], L3.Ty3, L3.Exp3)], [L3.Exp3])
    materializeConsumerCursorArgs fn args =
      goArgs 0 args
      where
        argIxs =
          L.nub $
            concat
              [ [cpsEndArgIx shape, cpsCurArgIx shape]
              | shape <- fromMaybe [] (M.lookup fn consumers)
              ]

        goArgs _ [] = ([], [])
        goArgs ix (arg:rest) =
          let (argBinds, arg') =
                if ix `elem` argIxs
                then materializeCursorArrayArg arg
                else ([], arg)
              (restBinds, rest') = goArgs (ix + 1) rest
           in (argBinds ++ restBinds, arg' : rest')

    materializeCursorArrayArg
      :: L3.Exp3
      -> ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
    materializeCursorArrayArg arg =
      case arg of
        L3.VarE{} -> ([], arg)
        _ ->
          let (binds, tailExp) = unLetsL3 arg
           in case tailExp of
                L3.VarE v
                  | not (null binds) && cursorArrayResult v binds ->
                      (binds, L3.VarE v)
                _ -> ([], arg)

    cursorArrayResult :: Var -> [(Var, [()], L3.Ty3, L3.Exp3)] -> Bool
    cursorArrayResult v =
      any (\(v', _, ty, _) -> v == v' && isCursorArrayTy ty)

    rewriteExt :: ShareEnv -> L3.E3Ext () L3.Ty3 -> Learn (L3.E3Ext () L3.Ty3)
    rewriteExt env = traverseExtExps (go env)

learnCallSiteBind
  :: M.Map Var CursorPairShape
  -> ShareEnv
  -> (Var, [()], L3.Ty3, L3.Exp3)
  -> ShareEnv
learnCallSiteBind producers env (v, _, ty, rhs) =
  let envWithAliases =
        case rhs of
          L3.Ext (L3.MemCpy dst src (L3.CursorArrayTy _)) ->
            addAlias dst src env
          L3.VarE src
            | isCursorArrayTy ty ->
                addAlias v src env
          _ -> env
   in foldl
        (\acc (ends, curs) -> markSelectivePair ends curs acc)
        envWithAliases
        (producerOutputPairs producers rhs)

producerOutputPairs :: M.Map Var CursorPairShape -> L3.Exp3 -> [(Var, Var)]
producerOutputPairs producers ex =
  case ex of
    L3.AppE fn _ _ args ->
      case M.lookup fn producers of
        Just shape ->
          maybeToList (cursorPairArgs shape args)
        Nothing -> []
    L3.LetE (_, _, _, rhs) bod ->
      producerOutputPairs producers rhs ++ producerOutputPairs producers bod
    L3.IfE a b c ->
      concatMap (producerOutputPairs producers) [a,b,c]
    L3.CaseE scrt brs ->
      producerOutputPairs producers scrt ++
      concatMap (producerOutputPairs producers . (\(_, _, rhs) -> rhs)) brs
    L3.MkProdE ls ->
      concatMap (producerOutputPairs producers) ls
    L3.ProjE _ rhs ->
      producerOutputPairs producers rhs
    L3.PrimAppE _ args ->
      concatMap (producerOutputPairs producers) args
    L3.TimeIt rhs _ _ ->
      producerOutputPairs producers rhs
    L3.WithArenaE _ rhs ->
      producerOutputPairs producers rhs
    L3.SpawnE fn _ args ->
      (case M.lookup fn producers of
         Just shape -> maybeToList (cursorPairArgs shape args)
         Nothing -> [])
        ++ concatMap (producerOutputPairs producers) args
    L3.MapE (_, _, rhs) bod ->
      producerOutputPairs producers rhs ++ producerOutputPairs producers bod
    L3.FoldE (_, _, rhs1) (_, _, rhs2) bod ->
      concatMap (producerOutputPairs producers) [rhs1, rhs2, bod]
    L3.DataConE _ _ args ->
      concatMap (producerOutputPairs producers) args
    L3.Ext ext ->
      producerOutputPairsExt producers ext
    _ -> []

producerOutputPairsExt :: M.Map Var CursorPairShape -> L3.E3Ext () L3.Ty3 -> [(Var, Var)]
producerOutputPairsExt producers ext =
  concatMap (producerOutputPairs producers) (extExps ext)

unwrapBindsForCall
  :: M.Map Var [CursorPairShape]
  -> ShareEnv
  -> Var
  -> [L3.Exp3]
  -> PassM [(Var, [()], L3.Ty3, L3.Exp3)]
unwrapBindsForCall consumers env fn args = do
  let requests =
        L.nub
          [ (cpsLen shape, ends, curs)
          | shape <- fromMaybe [] (M.lookup fn consumers)
          , Just (ends, curs) <- [cursorPairArgs shape args]
          , isSelectivePair ends curs env
          ]
  mapM mkUnwrap requests
  where
    mkUnwrap :: (Int, Var, Var) -> PassM (Var, [()], L3.Ty3, L3.Exp3)
    mkUnwrap (arrLen, ends, curs) = do
      v <- gensym "unwrap_selective_call"
      pure (v, [], L3.ProdTy [], L3.Ext $ L3.UnwrapSelectiveIndirections arrLen ends curs)

-- | What the sweep knows at one point in a body: which selectively shared
-- pairs have been produced, and which of those an unwrap has already
-- normalised.
data SweepState = SweepState
  { ssShared :: S.Set (Var, Var)
  , ssUnwrapped :: S.Set (Var, Var)
  }

-- | Refuse any call handed a selectively shared @(ends, curs)@ pair with no
-- 'UnwrapSelectiveIndirections' for it in the enclosing let chain.
--
-- The marked pairs are the rewriting walk's own accumulated 'ShareEnv', so
-- this cannot disagree with the emitter about what was shared; what it adds is
-- the closed world.  It is total over 'PreExp' and descends into extension
-- forms through 'extExps', so a call the walk never opened up is a compile
-- time refusal rather than a consumer that reads the 25-byte sharing wrapper
-- as data.  See Note [Normalisation coverage is closed over the whole body].
sweepUnwrapCoverage
  :: M.Map Var CursorPairShape
  -> M.Map Var [CursorPairShape]
  -> ShareEnv
  -> L3.Exp3
  -> PassM ()
sweepUnwrapCoverage producers consumers env body
  | S.null (seSelectivePairs env) = pure ()
  | otherwise = go (SweepState S.empty S.empty) body
  where
    go :: SweepState -> L3.Exp3 -> PassM ()
    go unwrapped ex =
      case ex of
        L3.VarE{} -> pure ()
        L3.LitE{} -> pure ()
        L3.CharE{} -> pure ()
        L3.FloatE{} -> pure ()
        L3.LitSymE{} -> pure ()
        L3.SyncE -> pure ()
        L3.AppE fn _ _ args -> checkCall unwrapped fn args >> mapM_ (go unwrapped) args
        L3.SpawnE fn _ args -> checkCall unwrapped fn args >> mapM_ (go unwrapped) args
        L3.PrimAppE _ args -> mapM_ (go unwrapped) args
        L3.LetE (_, _, _, rhs) bod -> do
          go unwrapped rhs
          go (record unwrapped rhs) bod
        L3.IfE a b c -> mapM_ (go unwrapped) [a, b, c]
        L3.MkProdE ls -> mapM_ (go unwrapped) ls
        L3.ProjE _ e -> go unwrapped e
        L3.CaseE scrt brs ->
          go unwrapped scrt >> mapM_ (\(_, _, rhs) -> go unwrapped rhs) brs
        L3.DataConE _ _ args -> mapM_ (go unwrapped) args
        L3.TimeIt e _ _ -> go unwrapped e
        L3.WithArenaE _ e -> go unwrapped e
        L3.MapE (_, _, rhs) bod -> go unwrapped rhs >> go unwrapped bod
        L3.FoldE (_, _, r1) (_, _, r2) bod -> mapM_ (go unwrapped) [r1, r2, bod]
        L3.Ext ext -> mapM_ (go unwrapped) (extExps ext)

    -- A pair is only in play once the producer call that shares it has run,
    -- and only until an unwrap for it appears.  Both are read off the finished
    -- binds with the same 'producerOutputPairs' the walk marks with, so the
    -- call that establishes a pair is never itself asked to unwrap it.
    record st rhs =
      let st' = case rhs of
                  L3.Ext (L3.UnwrapSelectiveIndirections _ ends curs) ->
                    st { ssUnwrapped =
                           S.insert (key ends curs) (ssUnwrapped st) }
                  _ -> st
       in st' { ssShared =
                  foldr (\(ends, curs) -> S.insert (key ends curs))
                        (ssShared st')
                        (producerOutputPairs producers rhs) }

    key ends curs = (canonicalVar env ends, canonicalVar env curs)

    checkCall st fn args =
      case [ (ends, curs)
           | shape <- fromMaybe [] (M.lookup fn consumers)
           , Just (ends, curs) <- [cursorPairArgs shape args]
           , isSelectivePair ends curs env
           , key ends curs `S.member` ssShared st
           , key ends curs `S.notMember` ssUnwrapped st
           ] of
        [] -> pure ()
        ((ends, curs) : _) -> error $
          "selectiveBufferSharing: call to " ++ show fn ++ " is handed the " ++
          "selectively shared cursor arrays (" ++ fromVar ends ++ ", " ++
          fromVar curs ++ ") with no UnwrapSelectiveIndirections for them in " ++
          "scope, so the consumer would read the 25-byte sharing wrapper as " ++
          "data.\n" ++
          "Compile without --opt-selective-buffer-sharing."

cursorPairArgs :: CursorPairShape -> [L3.Exp3] -> Maybe (Var, Var)
cursorPairArgs CursorPairShape{cpsEndArgIx, cpsCurArgIx} args = do
  ends <- argVar cpsEndArgIx args
  curs <- argVar cpsCurArgIx args
  pure (ends, curs)

argVar :: Int -> [L3.Exp3] -> Maybe Var
argVar ix args =
  case drop ix args of
    L3.VarE v : _ -> Just v
    _ -> Nothing

isCursorArrayTy :: L3.Ty3 -> Bool
isCursorArrayTy L3.CursorArrayTy{} = True
isCursorArrayTy _ = False

addAlias :: Var -> Var -> ShareEnv -> ShareEnv
addAlias dst src env@ShareEnv{seAliases} =
  env { seAliases = M.insert dst (canonicalVar env src) seAliases }

markSelectivePair :: Var -> Var -> ShareEnv -> ShareEnv
markSelectivePair ends curs env@ShareEnv{seSelectivePairs} =
  env { seSelectivePairs = S.insert (canonicalVar env ends, canonicalVar env curs) seSelectivePairs }

isSelectivePair :: Var -> Var -> ShareEnv -> Bool
isSelectivePair ends curs env@ShareEnv{seSelectivePairs} =
  (canonicalVar env ends, canonicalVar env curs) `S.member` seSelectivePairs

canonicalVar :: ShareEnv -> Var -> Var
canonicalVar ShareEnv{seAliases} = go S.empty
  where
    go seen v
      | v `S.member` seen = v
      | otherwise =
          case M.lookup v seAliases of
            Just v' -> go (S.insert v seen) v'
            Nothing -> v

data TopBindRewrite
  = TopBindNormal BufferEnv (Var, [()], L3.Ty3, L3.Exp3)
  | TopBindLoop BufferEnv (S.Set ShareInfo) (Maybe (Var, [()], L3.Ty3, L3.Exp3))

data ShareInfo = ShareInfo
  { siIx :: Int
  , siInputEnd :: Var
  , siInLoc :: Var
  , siOutLoc :: Var
  , siOutEndLoc :: Var
  }
  deriving (Eq, Ord, Show)

rewriteTopBind :: BufferEnv -> (Var, [()], L3.Ty3, L3.Exp3) -> TopBindRewrite
rewriteTopBind env b@(v, locs, ty, rhs) =
  case rhs of
    L3.Ext (L3.WhileCursor cond bod) ->
      let loopInfo = classifyLoop bod
          shares = S.fromList $ mapMaybeShare env (liShareKeys loopInfo)
       in if S.null shares
            then TopBindNormal env b
            else
              let shareIxs = S.map siIx shares
                  keepLoop = liKeepLoop loopInfo
                  bod' = rewriteLoopBodyForSharing shareIxs bod
                  mbLoop = if keepLoop
                           then Just (v, locs, ty, L3.Ext $ L3.WhileCursor cond bod')
                           else Nothing
               in TopBindLoop env shares mbLoop
    _ ->
      TopBindNormal (learnBufferBind env b) b

mapMaybeShare :: BufferEnv -> S.Set LoopBufferKey -> [ShareInfo]
mapMaybeShare env =
  mapMaybe (\k -> shareInfoFor k env) . S.toList

shareInfoFor :: LoopBufferKey -> BufferEnv -> Maybe ShareInfo
shareInfoFor key@(_, ix) BufferEnv{beLocs} = do
  BufferLocs{blInputEnd, blInLoc, blOutLoc, blOutEndLoc} <- M.lookup key beLocs
  ShareInfo ix <$> blInputEnd <*> blInLoc <*> blOutLoc <*> blOutEndLoc

learnBufferBind :: BufferEnv -> (Var, [()], L3.Ty3, L3.Exp3) -> BufferEnv
learnBufferBind env@(BufferEnv locs) (v, _, ty, rhs) =
  case (loopBufferKey v, ty, rhs) of
    (Just ix, L3.CursorTy, _)
      | isLoopBufferName LbInputEnd v ->
          update ix (\bl -> bl { blInputEnd = Just v })
    (Just ix, L3.MutCursorTy, L3.Ext (L3.AddrOfCursor (L3.Ext L3.IndexCursorArray{})))
      | isLoopBufferName LbInLoc v ->
          update ix (\bl -> bl { blInLoc = Just v })
      | isLoopBufferName LbOutLoc v ->
          update ix (\bl -> bl { blOutLoc = Just v })
      | isLoopBufferName LbOutEndLoc v ->
          update ix (\bl -> bl { blOutEndLoc = Just v })
    _ -> env
  where
    update ix f =
      BufferEnv $ M.alter (Just . f . fromMaybe emptyBufferLocs) ix locs

data LoopInfo = LoopInfo
  { liShareKeys :: S.Set LoopBufferKey
  , liKeepLoop :: Bool
  }

classifyLoop :: L3.Exp3 -> LoopInfo
classifyLoop bod =
  case findForBody bod of
    Just forBody
      | containsWriteTagPacked forBody && not (containsWriteScalar forBody) ->
          -- The tag stream is buffer 0 of whichever loop this is; a body with
          -- no named buffer at all names no loop, and shares nothing.
          LoopInfo (S.fromList [ (seed, 0) | seed <- maybeToList (loopSeedOf forBody) ]) False
      | otherwise ->
          let scalarKeys = scalarInnerBodyKeys forBody
              copyKeys = scalarCopyKeys forBody
           in LoopInfo
                copyKeys
                (not (scalarKeys `S.isSubsetOf` copyKeys))
    Nothing ->
      LoopInfo S.empty True

-- | The loop a body's bindings belong to, if they agree on one.
loopSeedOf :: L3.Exp3 -> Maybe String
loopSeedOf ex =
  case L.nub [ seed | (v, _, _, _) <- fst (unLetsL3 ex)
                    , Just seed <- [loopBufferSeed v] ] of
    [seed] -> Just seed
    _ -> Nothing

rewriteLoopBodyForSharing :: S.Set Int -> L3.Exp3 -> L3.Exp3
rewriteLoopBodyForSharing shareIxs = go
  where
    go ex =
      case ex of
        L3.LetE b@(v, locs, ty, rhs) bod
          | shouldDropLoopBind shareIxs b ->
              go bod
          | otherwise ->
              L3.LetE (v, locs, ty, rewriteRhs rhs) (go bod)
        L3.IfE a b c -> L3.IfE (go a) (go b) (go c)
        L3.Ext (L3.ForE i bound forBody) ->
          L3.Ext $ L3.ForE i bound (rewriteForBody shareIxs forBody)
        L3.Ext (L3.WhileCursor cond bod) ->
          L3.Ext $ L3.WhileCursor cond (go bod)
        _ -> ex

    rewriteRhs rhs =
      case rhs of
        L3.Ext (L3.ForE i bound forBody) ->
          L3.Ext $ L3.ForE i bound (rewriteForBody shareIxs forBody)
        L3.IfE a b c -> L3.IfE (go a) (go b) (go c)
        _ -> rhs

rewriteForBody :: S.Set Int -> L3.Exp3 -> L3.Exp3
rewriteForBody shareIxs ex =
  let (binds, tailExp) = unLetsL3 ex
      binds' =
        [ b
        | b@(v, _, _, rhs) <- binds
        , not (maybe False (\ix -> ix `S.member` shareIxs && isScalarCopyInner ix rhs)
                           (loopBufferIx v))
        ]
   in L3.mkLets binds' tailExp

shouldDropLoopBind :: S.Set Int -> (Var, [()], L3.Ty3, L3.Exp3) -> Bool
shouldDropLoopBind shareIxs (v, _, _, rhs) =
  case loopBufferIx v of
    Nothing -> False
    Just ix
      | ix `S.notMember` shareIxs -> False
      | isLoopBufferName LbCurrentOutEnd v -> True
      | isLoopBufferName LbSetChunkCount v -> True
      | isLoopBufferName LbGrowOut v -> True
      | otherwise ->
          case rhs of
            L3.Ext (L3.GrowRegion _ _) -> True
            _ -> False

findForBody :: L3.Exp3 -> Maybe L3.Exp3
findForBody ex =
  case ex of
    L3.Ext (L3.ForE _ _ bod) -> Just bod
    L3.LetE (_, _, _, rhs) bod -> findForBody rhs <|> findForBody bod
    L3.IfE a b c -> findForBody a <|> findForBody b <|> findForBody c
    L3.Ext (L3.WhileCursor _ bod) -> findForBody bod
    L3.Ext (L3.WhileCursorEnd _ _ bod) -> findForBody bod
    _ -> Nothing

scalarInnerBodyKeys :: L3.Exp3 -> S.Set LoopBufferKey
scalarInnerBodyKeys ex =
  S.fromList
    [ key
    | (v, _, _, rhs) <- fst (unLetsL3 ex)
    , Just key <- [loopBufferKey v]
    , containsWriteScalar rhs
    ]

scalarCopyKeys :: L3.Exp3 -> S.Set LoopBufferKey
scalarCopyKeys ex =
  S.fromList
    [ key
    | (v, _, _, rhs) <- fst (unLetsL3 ex)
    , Just key@(_, ix) <- [loopBufferKey v]
    , isScalarCopyInner ix rhs
    ]

-- | Is buffer @ix@'s inner loop body a pure copy of buffer @ix@ itself?
--
-- The value written must come from a read of *this* buffer's own input cursor.
-- `LoopifyTraversals` emits cross-buffer dependency reads with exactly the same
-- @ReadScalar@ / @ProjE 0@ shape, but on a separate @..._buf<ix>_dep<n>_read_cur@
-- cursor (see `LoopifyTraversals.mkDependencyRead`).  Accepting those made a
-- write of *another* buffer's value look like a same-buffer copy, so the pass
-- shared the buffer with the input and deleted the loop that was supposed to
-- overwrite it -- a silent wrong answer.  Requiring the buffer's own
-- @..._buf<ix>_read_cur@ / @..._buf<ix>_write_cur@ cursors rejects that.
isScalarCopyInner :: Int -> L3.Exp3 -> Bool
isScalarCopyInner ix ex =
  let binds = fst (unLetsL3 ex)
      readPairs =
        S.fromList
          [ v
          | (v, _, _, L3.Ext (L3.ReadScalar _ cur)) <- binds
          , isOwnLoopBufferName ix LbReadCur cur
          ]
      readVals =
        S.fromList
          [ v
          | (v, _, _, L3.ProjE 0 (L3.VarE pair)) <- binds
          , pair `S.member` readPairs
          ]
      aliases =
        M.fromList
          [ (v, rhs)
          | (v, _, _, L3.VarE rhs) <- binds
          ]
      writes =
        [ (isOwnLoopBufferName ix LbWriteCur cur, rhs)
        | (_, _, _, L3.Ext (L3.WriteScalar _ cur rhs)) <- binds
        ]
      resolveVar v =
        case M.lookup v aliases of
          Just v' | v' /= v -> resolveVar v'
          _ -> v
      resolvesToReadVal rhs =
        case rhs of
          L3.VarE v -> resolveVar v `S.member` readVals
          _ -> False
   in case writes of
        [(ownWriteCur, rhs)] -> ownWriteCur && resolvesToReadVal rhs
        _ -> False

containsWriteScalar :: L3.Exp3 -> Bool
containsWriteScalar = containsExt p
  where
    p L3.WriteScalar{} = True
    p _ = False

containsWriteTagPacked :: L3.Exp3 -> Bool
containsWriteTagPacked = containsExt p
  where
    p L3.WriteTagPacked{} = True
    p _ = False

containsExt :: (L3.E3Ext () L3.Ty3 -> Bool) -> L3.Exp3 -> Bool
containsExt p ex =
  case ex of
    L3.LetE (_, _, _, rhs) bod -> containsExt p rhs || containsExt p bod
    L3.IfE a b c -> any (containsExt p) [a, b, c]
    L3.CaseE scrt brs -> containsExt p scrt || any (containsExt p . (\(_, _, rhs) -> rhs)) brs
    L3.AppE _ _ _ args -> any (containsExt p) args
    L3.PrimAppE _ args -> any (containsExt p) args
    L3.MkProdE ls -> any (containsExt p) ls
    L3.ProjE _ e -> containsExt p e
    L3.DataConE _ _ args -> any (containsExt p) args
    L3.TimeIt e _ _ -> containsExt p e
    L3.WithArenaE _ e -> containsExt p e
    L3.SpawnE _ _ args -> any (containsExt p) args
    L3.MapE (_, _, e1) e2 -> containsExt p e1 || containsExt p e2
    L3.FoldE (_, _, e1) (_, _, e2) e3 -> any (containsExt p) [e1, e2, e3]
    -- Fails CLOSED via 'extExps': an unlisted form's expression children are
    -- still visited, so e.g. a 'WriteScalar' reachable only through a 'RetE'
    -- still surfaces here instead of making a tag+scalar loop look pure.
    L3.Ext ext
      | p ext -> True
      | otherwise -> any (containsExt p) (extExps ext)
    _ -> False

unLetsL3 :: L3.Exp3 -> ([(Var, [()], L3.Ty3, L3.Exp3)], L3.Exp3)
unLetsL3 ex =
  case ex of
    L3.LetE b bod ->
      let (bs, tailExp) = unLetsL3 bod
       in (b : bs, tailExp)
    _ -> ([], ex)

(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> y = y
x <|> _ = x
