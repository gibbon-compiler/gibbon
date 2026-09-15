-- | Conservative SIMD vectorization for loopified fully-factored traversals.
--
-- This pass runs after loopification, selective buffer sharing, and optional
-- loop fusion.  It intentionally starts with one small recognizer, but the IR it
-- emits is not a semantic "map add" node.  Instead it lowers supported scalar
-- loops to explicit vector-register operations:
--
--   VecBroadcast, VecLoad, VecAdd, VecSub, VecMul, VecDiv, VecMod, VecEq, VecSelect, VecStore
--
-- The first recognizer handles scalar-buffer arithmetic DAGs produced by
-- loopification.  It accepts conservative expression trees whose leaves are
-- scalar reads from input buffers or loop-invariant scalar expressions, and
-- whose internal nodes are supported arithmetic primitives.  It rewrites a
-- loop only when all top-level scalar writes in that loop are supported,
-- yielding a stride-4 vector loop plus a scalar remainder loop.  For 64-bit
-- Int/Sym values, stride 4 is represented
-- as two SSE2 2-lane vector groups per iteration.  For Float values, stride 4 is
-- one SSE 4-lane group.  Byte-sized Char/Bool primitives use 16-lane SSE2
-- register operations when such loops become useful.  This keeps the compiler IR
-- extensible for later AVX2 and AVX512 backends without baking the whole
-- traversal into one primitive.
module Gibbon.Passes.VectorizeTraversals
  ( vectorizeTraversals
  , validateVectorizationFired
  ) where

import Control.Monad (guard, forM, foldM)
import Control.Monad.State.Strict (StateT, runStateT, get, modify')
import Control.Monad.Trans.Class (lift)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3
import Gibbon.Passes.LoopifyTraversals
  ( EffectClass(..), collectMentionedDataCons, isGeneratedPackedHelper
  , loopBufferKey, scalarExprClass )

{-
Note [What the vectorizer assumes LoopifyTraversals guarantees]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This pass only ever rewrites a loop 'LoopifyTraversals' emitted -- the gate is
the internal 'Loopified' marker in 'vectorizeFun', not the @OPT:MayVectorize@
source annotation.  Four properties of such a loop are what make the rewrite
legal, and each is established by a specific refusal or emission over there.

* NO LOOP-CARRIED DEPENDENCY.  The vector body computes @lanes@ elements at
  once, so element @i+1@ may not depend on element @i@.  Established by
  'LoopifyTraversals.hasParentChildDependency', asked from
  'extractTraversalPlan' before any plan exists, and by 'scanBranchBody',
  which admits a per-element body only if every binding in it is a read of
  this element, a whitelisted scalar computation, or the write.

* UNIT STRIDE.  Each cursor must advance exactly one element per iteration, or
  a vector group would straddle records.  Established by 'mkScalarLoopBody',
  which emits @BumpCursorMutable cur (LitE scalarBytes)@ for the input and the
  output of every buffer.  Checked here: 'opHasRequiredBumps' and
  'hasCursorBump' require that literal bump, at exactly
  @simdScalarBytes scalar@, for every cursor of every op.  That check is also
  what keeps an AoS-loopified body out: its loops are 'WhileCursor', never
  'ForE', and it emits no such per-element bump.

* UNIFORM ELEMENT WIDTH PER CURSOR.  One cursor advanced once per group has
  one distance to advance by.  A fused loop may mix widths ACROSS buffers --
  'matchSimdLoop' handles that with a logical stride -- but not within one
  cursor.  Checked here: 'mkVectorLoopBody' errors on a cursor appearing under
  two scalar widths in one iteration.

* EFFECTS LIMITED TO THE RECOGNISED READS, WRITES AND BUMPS.
  'mkVectorLoopBody' rebuilds the vector body from the matched ops alone, so
  anything else in the scalar body would simply be dropped.  Established by
  'scanBranchBody' and 'branchDropsEffect' upstream; checked here by
  'loopEffectsSafe', which admits an 'Ext' binding only if it is a recognised
  read, deref, write or expected bump, and every other right-hand side only if
  'scalarExprClass' -- the same rule the loopifier admitted it under -- can
  classify it.

The buffer identity behind these is the loop buffer name contract
('LoopifyTraversals.loopBufferKey'), which is what 'sameLoopBuffer' below reads
when it has to decide whether two cursors belong to the same buffer.
-}

type Bind3 = (Var, [()], L3.Ty3, L3.Exp3)

-- | The two byte widths every lane computation depends on.
--
-- These were both plain 'Int' parameters called @intBytes@, with the register
-- width left implicit as a constant.  Bundling them makes it impossible to
-- pass the machine integer width where the register width was meant -- an
-- error that would not fail to compile and would emit cursor arithmetic that
-- silently walks off the end of a buffer.
data SimdCfg = SimdCfg
  { scIntBytes :: Int   -- ^ Width of a machine @GibInt@, in bytes.
  , scRegBytes :: Int   -- ^ Width of one SIMD register, in bytes: 16 for
                        --   baseline SSE2, 32 for AVX2.
  , scW64Mul :: Bool    -- ^ Whether the emulated 64-bit packed multiply may be
                        --   used.  Off by default: it is correct SIMD but
                        --   slower than the scalar multiply it replaces.
  }

vectorizeTraversals :: L3.Prog3 -> PassM L3.Prog3
vectorizeTraversals prog@Prog{fundefs} = do
  dflags <- getDynFlags
  let loopificationOn = gopt Opt_EnableLoopification dflags || gopt Opt_AutoLoopification dflags
  if gopt Opt_EnableVectorization dflags && not loopificationOn
    then error $
      "vectorizeTraversals: --opt-vectorization is enabled, but neither " ++
      "--opt-loopification nor --auto-loopification is.\n" ++
      "Vectorization only ever rewrites loops loopification already " ++
      "produced, so it has nothing to do without it.\n" ++
      "Add --opt-loopification (with --store-scalar-field-counts) or " ++
      "--auto-loopification to the compile command."
  else if not (gopt Opt_EnableVectorization dflags)
    then pure prog
    else do
      -- The byte width of the one integer scalar this backend can vectorize
      -- (IntS W64).  A narrow integer scalar never reaches this point at all
      -- -- 'scalarSupported' below keeps it on the scalar path.  GibInt itself
      -- is unconditionally
      -- 8 bytes, matching 'Gibbon.Passes.Codegen.simdScalarWidthBytes'.
      -- Baseline SSE2 unless the compilation asked for the best SIMD the
      -- machine has, which is what --opt-vectorization means unless
      -- --simd-baseline-sse2 opts back out.  Every lane count, cursor bump
      -- and trip count downstream derives from this one choice.
      -- ONE decision, shared with the C compiler: 'simdIsaOf' also chooses the
      -- -m flag the generated C is compiled with, so Gibbon's vectorizer and
      -- the C compiler's auto-vectorizer can never target different
      -- instruction sets.  Every lane count, cursor bump and trip count
      -- downstream derives from this.
      let cfg = SimdCfg { scIntBytes = 8
                        , scRegBytes = simdIsaRegisterBytes (simdIsaOf dflags)
                        , scW64Mul = gopt Opt_SimdW64Multiply dflags }
      fds' <- mapM (vectorizeFun cfg) (M.elems fundefs)
      pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

vectorizeFun :: SimdCfg -> L3.FunDef3 -> PassM L3.FunDef3
vectorizeFun cfg fn@FunDef{funMeta, funBody}
  | Loopified `notElem` funOpt funMeta = pure fn
  | otherwise = do
      body' <- vectorizeExp cfg funBody
      pure $ fn { funBody = body' }

vectorizeExp :: SimdCfg -> L3.Exp3 -> PassM L3.Exp3
vectorizeExp cfg ex =
  case ex of
    LetE (v, locs, ty, Ext (L3.ForE idx bound loopBody)) bod -> do
      bod' <- vectorizeExp cfg bod
      case matchSimdLoop cfg idx loopBody of
        Just simdLoop -> do
          bound' <- vectorizeExp cfg bound
          vecLoop <- mkVectorizedScalarLoop cfg idx bound' loopBody simdLoop
          pure $ LetE (v, locs, ty, vecLoop) bod'
        Nothing -> do
          bound' <- vectorizeExp cfg bound
          loopBody' <- vectorizeExp cfg loopBody
          pure $ LetE (v, locs, ty, Ext (L3.ForE idx bound' loopBody')) bod'

    LetE (v, locs, ty, rhs) bod -> do
      rhs' <- vectorizeExp cfg rhs
      bod' <- vectorizeExp cfg bod
      pure $ LetE (v, locs, ty, rhs') bod'

    IfE tst a b -> IfE <$> vectorizeExp cfg tst <*> vectorizeExp cfg a <*> vectorizeExp cfg b
    CaseE scrt brs -> do
      scrt' <- vectorizeExp cfg scrt
      brs' <- mapM (\(dc, vs, rhs) -> (dc, vs,) <$> vectorizeExp cfg rhs) brs
      pure $ CaseE scrt' brs'
    MkProdE es -> MkProdE <$> mapM (vectorizeExp cfg) es
    ProjE i e -> ProjE i <$> vectorizeExp cfg e
    PrimAppE p es -> PrimAppE p <$> mapM (vectorizeExp cfg) es
    DataConE loc dc es -> DataConE loc dc <$> mapM (vectorizeExp cfg) es
    AppE f c locs es -> AppE f c locs <$> mapM (vectorizeExp cfg) es
    SpawnE f locs es -> SpawnE f locs <$> mapM (vectorizeExp cfg) es
    WithArenaE v e -> WithArenaE v <$> vectorizeExp cfg e
    TimeIt e ty isIter -> TimeIt <$> vectorizeExp cfg e <*> pure ty <*> pure isIter
    MapE (v, ty, rhs) bod -> MapE . (v, ty,) <$> vectorizeExp cfg rhs <*> vectorizeExp cfg bod
    FoldE (v1, t1, rhs1) (v2, t2, rhs2) bod ->
      FoldE <$> ((v1, t1,) <$> vectorizeExp cfg rhs1)
            <*> ((v2, t2,) <$> vectorizeExp cfg rhs2)
            <*> vectorizeExp cfg bod

    Ext ext -> Ext <$> vectorizeExt cfg ext
    VarE{} -> pure ex
    LitE{} -> pure ex
    CharE{} -> pure ex
    FloatE{} -> pure ex
    LitSymE{} -> pure ex
    SyncE -> pure ex

vectorizeExt :: SimdCfg -> L3.E3Ext () L3.Ty3 -> PassM (L3.E3Ext () L3.Ty3)
vectorizeExt cfg ext =
  case ext of
    L3.WriteScalar s v rhs -> L3.WriteScalar s v <$> vectorizeExp cfg rhs
    L3.WriteTagPacked v rhs -> L3.WriteTagPacked v <$> vectorizeExp cfg rhs
    L3.WriteCursorSelectiveIndirection a b c mask ->
      L3.WriteCursorSelectiveIndirection a b c <$> vectorizeExp cfg mask
    L3.WriteTaggedCursor v rhs -> L3.WriteTaggedCursor v <$> vectorizeExp cfg rhs
    L3.WriteCursorMutable v rhs -> L3.WriteCursorMutable v <$> vectorizeExp cfg rhs
    L3.WriteList v rhs ty -> L3.WriteList v <$> vectorizeExp cfg rhs <*> pure ty
    L3.WriteVector v rhs ty -> L3.WriteVector v <$> vectorizeExp cfg rhs <*> pure ty
    L3.AddCursor v rhs -> L3.AddCursor v <$> vectorizeExp cfg rhs
    L3.BumpCursorMutable v rhs -> L3.BumpCursorMutable v <$> vectorizeExp cfg rhs
    L3.AddrOfCursor rhs -> L3.AddrOfCursor <$> vectorizeExp cfg rhs
    L3.RetE es -> L3.RetE <$> mapM (vectorizeExp cfg) es
    L3.LetAvail vs bod -> L3.LetAvail vs <$> vectorizeExp cfg bod
    L3.ForE idx bound bod -> L3.ForE idx <$> vectorizeExp cfg bound <*> vectorizeExp cfg bod
    L3.WhileCursor ref bod -> L3.WhileCursor ref <$> vectorizeExp cfg bod
    L3.WhileCursorEnd ref end bod -> L3.WhileCursorEnd ref end <$> vectorizeExp cfg bod
    L3.VecBroadcast s lanes val -> L3.VecBroadcast s lanes <$> vectorizeExp cfg val
    L3.VecLoad{} -> pure ext
    L3.VecAdd s lanes a b -> L3.VecAdd s lanes <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecSub s lanes a b -> L3.VecSub s lanes <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecMul s lanes a b -> L3.VecMul s lanes <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecDiv s lanes a b -> L3.VecDiv s lanes <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecMod s lanes a b -> L3.VecMod s lanes <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecCmp s lanes c a b -> L3.VecCmp s lanes c <$> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecSelect s lanes m a b -> L3.VecSelect s lanes <$> vectorizeExp cfg m <*> vectorizeExp cfg a <*> vectorizeExp cfg b
    L3.VecStore s lanes ref val -> L3.VecStore s lanes ref <$> vectorizeExp cfg val
    L3.Assert rhs -> L3.Assert <$> vectorizeExp cfg rhs
    _ -> pure ext

data ScalarDag
  = DagRead Var
  | DagInvariant [Bind3] L3.Exp3
  | DagBin (Prim L3.Ty3) ScalarDag ScalarDag
  | DagIf CondDag ScalarDag ScalarDag
  -- | A value computed ONCE and referred to by name.
  --
  -- Without these two constructors the DAG is a tree and 'resolveVarRhs'
  -- re-expands a let-bound variable at every use, so a chain of bindings each
  -- used twice costs 2^depth -- the 431-operation arithmetic kernel reached
  -- 66k lines of C at 143 operations and exhausted 8 GB at 431.  A 'DagLet'
  -- keeps the binding, and every use is a constant-size 'DagShared'.
  --
  -- 'DagLet' nodes are only ever built around the ROOT, and only for variables
  -- bound in the loop body's straight-line binding list, so the value they
  -- name is one the scalar loop also evaluated unconditionally.  That is what
  -- lets every traversal below treat them as ordinary unconditional positions.
  | DagLet Var ScalarDag ScalarDag
  | DagShared Var
  deriving (Show, Eq)

data CondDag
  = CondCmp L3.Scalar L3.VecCmpOp ScalarDag ScalarDag
  deriving (Show, Eq)

data VectorDag
  = VDagRead Var
  | VDagInvariant Var
  | VDagBin (Prim L3.Ty3) VectorDag VectorDag
  | VDagIf VectorCondDag VectorDag VectorDag
  | VDagLet Var VectorDag VectorDag
  | VDagShared Var
  deriving (Show, Eq)

data VectorCondDag
  = VCondCmp L3.Scalar L3.VecCmpOp VectorDag VectorDag
  deriving (Show, Eq)

data SimdOp = SimdOp
  { soScalar :: L3.Scalar
  , soInRefs :: S.Set Var
  , soOutRef :: Var
  , soDag :: ScalarDag
  }
  deriving (Show, Eq)

data PreparedSimdOp = PreparedSimdOp
  { poScalar :: L3.Scalar
  , poInRefs :: S.Set Var
  , poOutRef :: Var
  , poDag :: VectorDag
  }
  deriving (Show, Eq)

-- | A loop the vectorizer accepted, together with the ONE logical stride every
-- one of its scalar buffers advances by (see 'L3.simdLogicalStride').  The
-- stride is computed once, from all the loop's scalars together, and then used
-- for the trip counts, the group counts and the cursor bumps -- so those three
-- cannot drift apart.
data SimdLoop = SimdLoop
  { slStride :: Int
  , slOps :: [SimdOp]
  }

mkVectorizedScalarLoop :: SimdCfg -> Var -> L3.Exp3 -> L3.Exp3 -> SimdLoop -> PassM L3.Exp3
mkVectorizedScalarLoop cfg _idx bound scalarLoopBody SimdLoop{slStride, slOps} = do
  vecCount <- gensym "simd_vec_count"
  tailCount <- gensym "simd_tail_count"
  vecLoopIdx <- gensym "simd_i"
  tailLoopIdx <- gensym "simd_tail_i"
  vecLoopUnit <- gensym "simd_vec_loop"
  tailLoopUnit <- gensym "simd_tail_loop"
  prepared <- forM slOps $ \SimdOp{soScalar, soInRefs, soOutRef, soDag} -> do
    (broadcasts, vdag) <- prepareVectorDag cfg soScalar soDag
    pure (broadcasts, PreparedSimdOp soScalar soInRefs soOutRef vdag)
  let broadcasts = concatMap fst prepared
      ops = map snd prepared
      -- The loop-level stride, decided once in 'matchSimdLoop' from ALL the
      -- loop's scalars.  Never re-derived per scalar: that is exactly how the
      -- trip count and the cursor bumps would come to disagree.
      stride = slStride
      unitTy = ProdTy []
  vecBody <- mkVectorLoopBody cfg stride ops
  let binds =
        [ (vecCount, [], (IntTy W64), PrimAppE divP64 [bound, mkLitE64 (fromIntegral stride)])
        , (tailCount, [], (IntTy W64), PrimAppE modP64 [bound, mkLitE64 (fromIntegral stride)])
        ] ++ broadcasts ++
        [ (vecLoopUnit, [], unitTy, Ext (L3.ForE vecLoopIdx (VarE vecCount) vecBody))
        , (tailLoopUnit, [], unitTy, Ext (L3.ForE tailLoopIdx (VarE tailCount) scalarLoopBody))
        ]
  pure $ mkLets binds (MkProdE [])

prepareVectorDag :: SimdCfg -> L3.Scalar -> ScalarDag -> PassM ([Bind3], VectorDag)
prepareVectorDag cfg scalar dag =
  case dag of
    DagRead ref -> pure ([], VDagRead ref)
    DagInvariant deps ex -> do
      -- Re-emit the body-local bindings this invariant needs, outside the loop
      -- and ahead of it, under fresh names so that two invariants sharing a
      -- dependency cannot bind the same variable twice.
      (depBinds, sub) <-
        foldM (\(acc, sb) (dv, _, dty, drhs) -> do
                 dv' <- gensym "simd_invariant_dep"
                 pure ( acc ++ [(dv', [], dty, substInvariantVars sb drhs)]
                      , M.insert dv dv' sb ))
              ([], M.empty) deps
      scalarV <- gensym "simd_invariant_scalar"
      v <- gensym "simd_invariant_vec"
      let lanes = vectorLanes cfg scalar
          scalarTy = L3.scalarToTy scalar
          vecTy = L3.SimdTy scalarTy lanes
      pure ( depBinds ++
             [ (scalarV, [], scalarTy, substInvariantVars sub ex)
             , (v, [], vecTy, Ext (L3.VecBroadcast scalar lanes (VarE scalarV)))
             ]
           , VDagInvariant v)
    DagShared v -> pure ([], VDagShared v)
    DagLet v rhs bod -> do
      (rb, rv) <- prepareVectorDag cfg scalar rhs
      (bb, bv) <- prepareVectorDag cfg scalar bod
      pure (rb ++ bb, VDagLet v rv bv)
    DagBin prim a b -> do
      (ab, av) <- prepareVectorDag cfg scalar a
      (bb, bv) <- prepareVectorDag cfg scalar b
      pure (ab ++ bb, VDagBin prim av bv)
    DagIf cond thenDag elseDag -> do
      (cb, cvec) <- prepareVectorCondDag cfg cond
      (tb, tvec) <- prepareVectorDag cfg scalar thenDag
      (eb, evec) <- prepareVectorDag cfg scalar elseDag
      pure (cb ++ tb ++ eb, VDagIf cvec tvec evec)

prepareVectorCondDag :: SimdCfg -> CondDag -> PassM ([Bind3], VectorCondDag)
prepareVectorCondDag cfg cond =
  case cond of
    CondCmp scalar cmp a b -> do
      (ab, av) <- prepareVectorDag cfg scalar a
      (bb, bv) <- prepareVectorDag cfg scalar b
      pure (ab ++ bb, VCondCmp scalar cmp av bv)

-- | Emit one logical stride of vector work.  Fused loopified traversals can put
-- several independent scalar-buffer writes in the same `ForE`; this routine
-- handles all of them together.  Loads are keyed by (scalar kind, cursor ref),
-- so a DAG that mentions the same input more than once still performs one vector
-- load per group.
mkVectorLoopBody :: SimdCfg -> Int -> [PreparedSimdOp] -> PassM L3.Exp3
mkVectorLoopBody cfg stride ops = do
  -- Group counts come from the LOOP's stride, so a narrow field emits fewer,
  -- wider registers than a wide one while both cover the same records:
  -- at stride 16, W8 emits 1 group, W16 2, W32 4, W64 8.  A field appears in
  -- group indices [0 .. itsGroups-1], so the W8 buffer is loaded once and the
  -- W64 buffer eight times, and every cursor ends the iteration having
  -- advanced exactly @stride * scalarBytes@.
  let groupsOf scalar = L3.simdGroups (scRegBytes cfg) stride scalar
      maxGroups = maximum (map (groupsOf . poScalar) ops)
  groups <- forM [0 .. maxGroups - 1] $ \groupIx -> do
    let groupOps = filter (\op -> groupIx < groupsOf (poScalar op)) ops
        readPairs =
          [ (poScalar op, ref)
          | op <- groupOps
          , ref <- S.toList (vectorReadRefs (poDag op))
          ]
        skipPairs =
          [ (poScalar op, ref)
          | op <- groupOps
          , ref <- S.toList (poInRefs op `S.difference` vectorReadRefs (poDag op))
          ]
        -- Deduplicated by CURSOR, not by (scalar, cursor).  Each entry emits a
        -- bump, so one cursor appearing under two scalars -- or once as a read
        -- and once as a skip -- advanced it twice in one iteration, walking
        -- past its own data.  Keying on the cursor collapses the repeats; a
        -- genuine disagreement about the width is caught below.
        readKeys = L.nubBy (\a b -> snd a == snd b) readPairs
        skipKeys =
          [ k
          | k <- L.nubBy (\a b -> snd a == snd b) skipPairs
          , snd k `notElem` map snd readKeys
          ]
        widthConflicts =
          [ ref
          | ref <- L.nub (map snd (readPairs ++ skipPairs))
          , let ss = L.nub [ sc | (sc, r) <- readPairs ++ skipPairs, r == ref ]
          , length (L.nub (map (scalarWidthBytes cfg) ss)) > 1
          ]
        unitTy = ProdTy []
    case widthConflicts of
      [] -> pure ()
      (ref:_) ->
        error $ "mkVectorLoopBody: cursor " ++ fromVar ref ++ " is read at more "
          ++ "than one scalar width in one vector iteration, so there is no one "
          ++ "distance to advance it by."
    loaded <- forM readKeys $ \(scalar, ref) -> do
      loadV <- gensym "simd_load"
      bumpIn <- gensym "simd_bump_in"
      let lanes = vectorLanes cfg scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          bytes = fromIntegral (vectorBytes cfg scalar)
      pure ( ((scalar, ref), loadV)
           , [ (loadV, [], vecTy, Ext (L3.VecLoad scalar lanes ref))
             , (bumpIn, [], unitTy, Ext (L3.BumpCursorMutable ref (mkLitE64 bytes)))
             ]
           )
    skipped <- forM skipKeys $ \(scalar, ref) -> do
      bumpIn <- gensym "simd_skip_in"
      let bytes = fromIntegral (vectorBytes cfg scalar)
      pure (bumpIn, [], unitTy, Ext (L3.BumpCursorMutable ref (mkLitE64 bytes)))
    let loadEnv = M.fromList (map fst loaded)
        loadBinds = concatMap snd loaded
    opBinds <- forM groupOps $ \PreparedSimdOp{poScalar, poOutRef, poDag} -> do
      storeU <- gensym "simd_store"
      bumpOut <- gensym "simd_bump_out"
      (dagBinds, resultV) <- emitVectorDag cfg poScalar loadEnv poDag
      let lanes = vectorLanes cfg poScalar
          bytes = fromIntegral (vectorBytes cfg poScalar)
      pure $ dagBinds ++
        [ (storeU, [], unitTy, Ext (L3.VecStore poScalar lanes poOutRef (VarE resultV)))
        , (bumpOut, [], unitTy, Ext (L3.BumpCursorMutable poOutRef (mkLitE64 bytes)))
        ]
    pure $ loadBinds ++ skipped ++ concat opBinds
  pure $ mkLets (concat groups) (MkProdE [])

vectorReadRefs :: VectorDag -> S.Set Var
vectorReadRefs dag =
  case dag of
    VDagRead ref -> S.singleton ref
    VDagInvariant{} -> S.empty
    -- A shared value's own reads are collected once, at its 'VDagLet'; the
    -- references to it contribute nothing further.
    VDagShared{} -> S.empty
    VDagLet _ rhs bod -> vectorReadRefs rhs `S.union` vectorReadRefs bod
    VDagBin _ a b -> vectorReadRefs a `S.union` vectorReadRefs b
    VDagIf c a b -> vectorCondReadRefs c `S.union` vectorReadRefs a `S.union` vectorReadRefs b

vectorCondReadRefs :: VectorCondDag -> S.Set Var
vectorCondReadRefs cond =
  case cond of
    VCondCmp _ _ a b -> vectorReadRefs a `S.union` vectorReadRefs b

emitVectorDag :: SimdCfg -> L3.Scalar -> M.Map (L3.Scalar, Var) Var -> VectorDag -> PassM ([Bind3], Var)
emitVectorDag cfg scalar loadEnv = emitVectorDagIn cfg scalar loadEnv M.empty

-- | Lower a vector DAG, carrying the registers that shared values landed in.
emitVectorDagIn :: SimdCfg -> L3.Scalar -> M.Map (L3.Scalar, Var) Var -> M.Map Var Var
                -> VectorDag -> PassM ([Bind3], Var)
emitVectorDagIn cfg scalar loadEnv sharedEnv dag =
  case dag of
    VDagRead ref ->
      pure ([], fromMaybe (error $ "emitVectorDag: missing vector load for " ++ show (scalar, ref))
                          (M.lookup (scalar, ref) loadEnv))
    VDagInvariant v -> pure ([], v)
    -- Emit the shared value once, then make every reference to it name the
    -- register it landed in.  This is the whole point of the sharing nodes: a
    -- value used k times costs one vector operation, not k.
    VDagLet v rhs bod -> do
      (rb, rv) <- emitVectorDagIn cfg scalar loadEnv sharedEnv rhs
      (bb, bv) <- emitVectorDagIn cfg scalar loadEnv (M.insert v rv sharedEnv) bod
      pure (rb ++ bb, bv)
    VDagShared v ->
      pure ([], fromMaybe (error $ "emitVectorDag: unbound shared node " ++ show v)
                          (M.lookup v sharedEnv))
    VDagBin prim a b -> do
      (ab, av) <- emitVectorDagIn cfg scalar loadEnv sharedEnv a
      (bb, bv) <- emitVectorDagIn cfg scalar loadEnv sharedEnv b
      out <- gensym "simd_binop"
      let lanes = vectorLanes cfg scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          rhs = vectorPrimExt scalar lanes prim (VarE av) (VarE bv)
      pure (ab ++ bb ++ [(out, [], vecTy, rhs)], out)
    VDagIf cond thenDag elseDag -> do
      (cb, maskV) <- emitVectorCondDag cfg loadEnv sharedEnv cond
      (tb, thenV) <- emitVectorDagIn cfg scalar loadEnv sharedEnv thenDag
      (eb, elseV) <- emitVectorDagIn cfg scalar loadEnv sharedEnv elseDag
      out <- gensym "simd_select"
      let lanes = vectorLanes cfg scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          rhs = Ext (L3.VecSelect scalar lanes (VarE maskV) (VarE thenV) (VarE elseV))
      pure (cb ++ tb ++ eb ++ [(out, [], vecTy, rhs)], out)

emitVectorCondDag :: SimdCfg -> M.Map (L3.Scalar, Var) Var -> M.Map Var Var
                  -> VectorCondDag -> PassM ([Bind3], Var)
emitVectorCondDag cfg loadEnv sharedEnv cond =
  case cond of
    VCondCmp condScalar cmp a b -> do
      (ab, av) <- emitVectorDagIn cfg condScalar loadEnv sharedEnv a
      (bb, bv) <- emitVectorDagIn cfg condScalar loadEnv sharedEnv b
      out <- gensym "simd_cmp"
      let lanes = vectorLanes cfg condScalar
          vecTy = L3.SimdTy (L3.scalarToTy condScalar) lanes
          rhs = Ext (L3.VecCmp condScalar lanes cmp (VarE av) (VarE bv))
      pure (ab ++ bb ++ [(out, [], vecTy, rhs)], out)

vectorPrimExt :: L3.Scalar -> Int -> Prim L3.Ty3 -> L3.Exp3 -> L3.Exp3 -> L3.Exp3
vectorPrimExt scalar lanes prim a b =
  case prim of
    AddP{}  -> Ext (L3.VecAdd scalar lanes a b)
    FAddP -> Ext (L3.VecAdd scalar lanes a b)
    SubP{}  -> Ext (L3.VecSub scalar lanes a b)
    FSubP -> Ext (L3.VecSub scalar lanes a b)
    MulP{}  -> Ext (L3.VecMul scalar lanes a b)
    FMulP -> Ext (L3.VecMul scalar lanes a b)
    DivP{}  -> Ext (L3.VecDiv scalar lanes a b)
    FDivP -> Ext (L3.VecDiv scalar lanes a b)
    ModP{}  -> Ext (L3.VecMod scalar lanes a b)
    _ -> error $ "vectorPrimExt: unsupported vector op " ++ show prim

matchSimdLoop :: SimdCfg -> Var -> L3.Exp3 -> Maybe SimdLoop
matchSimdLoop cfg idx body = do
  binds <- flattenUnitLoopBody body
  let writes = writeScalarBinds binds
  guard (not (null writes))
  ops <- mapM (matchWrite (scW64Mul cfg) binds idx) writes
  guard (all (scalarSupported . soScalar) ops)
  -- ONE logical stride for the whole fused loop, derived from every scalar it
  -- writes (see 'L3.simdLogicalStride').  A fused loopified traversal can put
  -- several independent scalar-buffer writes of DIFFERENT widths in one
  -- `ForE`; they must advance in lockstep over the same records even though
  -- their registers hold different numbers of elements.  The stride is the
  -- widest lane count present, so every participating scalar covers it with a
  -- whole number of registers and each cursor advances exactly
  -- @stride * scalarBytes@.
  --
  -- This replaces the previous blanket "all writes must share one lane width"
  -- rejection, which left every mixed-width fused loop scalar.
  let loopScalars = map soScalar ops
      stride = L3.simdLogicalStride (scRegBytes cfg) loopScalars
  -- Defensive: the division above is exact by construction (lane counts are
  -- powers of two and the stride is their maximum), but a shape that somehow
  -- fails it must stay scalar rather than emit a drifting cursor.
  guard (L3.simdStrideValid (scRegBytes cfg) stride loopScalars)
  -- A `DagIf` is lowered to an unconditional evaluation of *both* arms followed
  -- by a `VecSelect` (see `emitVectorDag`).  That is only legal for total
  -- expressions: speculating a partial operation the scalar program had
  -- guarded turns a correct program into a trap (integer division by zero
  -- raises #DE / SIGFPE).  Leave such loops scalar.
  guard (all (not . dagSpeculatesPartialOp . soDag) ops)
  guard (all (opHasRequiredBumps cfg binds) ops)
  guard (loopEffectsSafe cfg ops binds)
  pure $ SimdLoop stride ops

writeScalarBinds :: [Bind3] -> [(Int, Bind3)]
writeScalarBinds binds = filter (isWriteScalar . snd) (zip [0..] binds)
  where
    isWriteScalar (_, _, _, Ext (L3.WriteScalar{})) = True
    isWriteScalar _ = False

matchWrite :: Bool -> [Bind3] -> Var -> (Int, Bind3) -> Maybe SimdOp
matchWrite w64Mul binds idx (writeIx, (_writeVal, _, _writeTy, Ext (L3.WriteScalar scalar writeCur rhs))) = do
  outRef <- derefSource writeCur binds
  let op = case rhs of
             VarE opVar -> resolveVarRhs binds S.empty opVar
             _ -> rhs
  dag <- matchScalarDag w64Mul scalar idx binds op
  inRefs <- inputRefsForDag binds writeIx scalar outRef dag
  pure $ SimdOp scalar inRefs outRef dag
matchWrite _ _ _ _ = Nothing

-- | The input cursors one write's DAG advances.
--
-- A write whose expression reads nothing -- a constant field -- still has to
-- advance an input cursor, because the scalar loop it replaces advanced one
-- per element.  There is no read in the DAG to name it, so it is borrowed from
-- the nearest preceding read of the same scalar kind.  That borrow is only
-- meaningful if it lands on the SAME buffer the write is writing: borrowing a
-- peer buffer's cursor would advance a cursor this write has no business
-- advancing.  'sameLoopBuffer' decides that from the loop buffer name
-- contract rather than from position, and a borrow it cannot confirm leaves
-- the whole loop scalar.
inputRefsForDag :: [Bind3] -> Int -> L3.Scalar -> Var -> ScalarDag -> Maybe (S.Set Var)
inputRefsForDag binds writeIx scalar outRef dag =
  let refs = readRefs dag
  in if S.null refs
     then do
       ref <- nearestInputRefBefore binds writeIx scalar
       guard (sameLoopBuffer ref outRef)
       pure (S.singleton ref)
     else Just refs

-- | Do these two loop bindings belong to the same buffer of the same loop?
--
-- Buffer indices restart at zero in every loop, so the loop seed is part of
-- the identity.  A name that is not a loop buffer binding at all answers
-- False: this is asked where being unable to tell means declining.
sameLoopBuffer :: Var -> Var -> Bool
sameLoopBuffer a b =
  case (loopBufferKey a, loopBufferKey b) of
    (Just ka, Just kb) -> ka == kb
    _ -> False

nearestInputRefBefore :: [Bind3] -> Int -> L3.Scalar -> Maybe Var
nearestInputRefBefore binds writeIx scalar =
  listToMaybe
    [ ref
    | (_, _, _, Ext (L3.ReadScalar scalar' cur)) <- reverse (take writeIx binds)
    , scalar == scalar'
    , Just ref <- [derefSource cur binds]
    ]

opHasRequiredBumps :: SimdCfg -> [Bind3] -> SimdOp -> Bool
opHasRequiredBumps cfg binds SimdOp{soScalar, soInRefs, soOutRef} =
  all (\ref -> hasCursorBump cfg ref soScalar binds) (S.toList soInRefs) &&
  hasCursorBump cfg soOutRef soScalar binds

loopEffectsSafe :: SimdCfg -> [SimdOp] -> [Bind3] -> Bool
loopEffectsSafe cfg ops binds =
  all safeEffect binds
  where
    expected = expectedBumps cfg ops
    safeEffect (_, _, _, Ext ext) =
      case ext of
        L3.ReadScalar{} -> True
        L3.DerefMutCursor{} -> True
        L3.WriteScalar{} -> True
        L3.BumpCursorMutable ref (LitE _ n) -> (ref, fromIntegral n) `elem` expected
        _ -> False
    -- Everything else has to be a pure scalar computation, judged by the same
    -- rule the loopifier admitted the expression under.  Accepting whatever
    -- was left over meant a call, a region operation or an allocation in the
    -- loop body was carried into the vector body, where it would run once per
    -- vector iteration instead of once per element.
    safeEffect (_, _, _, rhs) = isJust (scalarExprClass rhs)

expectedBumps :: SimdCfg -> [SimdOp] -> [(Var, Int)]
expectedBumps cfg ops = L.nub $ concatMap opBumps ops
  where
    opBumps SimdOp{soScalar, soInRefs, soOutRef} =
      let bytes = scalarWidthBytes cfg soScalar
      in (soOutRef, bytes) : [ (ref, bytes) | ref <- S.toList soInRefs ]

-- | Flatten unit-valued loop bodies for recognition only.  Loop fusion wraps
-- several scalar-buffer loop bodies as nested `let u :: () = <unit-body>`
-- statements.  The original scalar body is still used for the remainder loop;
-- this flattening only exposes the ordered reads/computations/writes so the
-- vectorizer can decide whether the entire loop is safe to rewrite.
flattenUnitLoopBody :: L3.Exp3 -> Maybe [Bind3]
flattenUnitLoopBody = go
  where
    go expr =
      case expr of
        MkProdE [] -> Just []
        LetE (v, locs, ty, rhs) bod -> do
          rhsBinds <-
            if ty == ProdTy [] && not (mentionsVar v bod)
            then case go rhs of
                   Just bs -> Just bs
                   Nothing -> Just [(v, locs, ty, rhs)]
            else Just [(v, locs, ty, rhs)]
          bodBinds <- go bod
          Just (rhsBinds ++ bodBinds)
        IfE tst thenExp elseExp -> conditionalWriteBinds tst thenExp elseExp
        _ -> Nothing

conditionalWriteBinds :: L3.Exp3 -> L3.Exp3 -> L3.Exp3 -> Maybe [Bind3]
conditionalWriteBinds tst thenExp elseExp = do
  ((thenV, locs, ty, _), thenScalar, thenCur, thenVal) <- branchScalarWrite thenExp
  (_elseBind, elseScalar, elseCur, elseVal) <- branchScalarWrite elseExp
  guard (thenScalar == elseScalar)
  guard (thenCur == elseCur)
  pure [(thenV, locs, ty, Ext (L3.WriteScalar thenScalar thenCur (IfE tst thenVal elseVal)))]

branchScalarWrite :: L3.Exp3 -> Maybe (Bind3, L3.Scalar, Var, L3.Exp3)
branchScalarWrite ex = do
  let (bs, tailExp) = unLets3 ex
      normalize val =
        case val of
          VarE v -> resolveVarRhs bs S.empty v
          _ -> val
  guard (tailExp == MkProdE [])
  -- Exactly one.  Taking the first of several turned the arm into a single
  -- conditional write and dropped the rest, silently losing every write but
  -- one.
  case [ (bind, scalar, cur, normalize val)
       | bind@(_, _, _, Ext (L3.WriteScalar scalar cur val)) <- bs
       ] of
    [w] -> Just w
    _ -> Nothing

mentionsVar :: Var -> L3.Exp3 -> Bool
mentionsVar v ex = v `S.member` expVars ex

expVars :: L3.Exp3 -> S.Set Var
expVars ex =
  case ex of
    VarE v -> S.singleton v
    LitE{} -> S.empty
    CharE{} -> S.empty
    FloatE{} -> S.empty
    LitSymE{} -> S.empty
    LetE (v, _, _, rhs) bod -> expVars rhs `S.union` S.delete v (expVars bod)
    IfE a b c -> S.unions (map expVars [a,b,c])
    MkProdE es -> S.unions (map expVars es)
    ProjE _ e -> expVars e
    CaseE scrt brs ->
      expVars scrt `S.union`
      S.unions [ expVars rhs S.\\ S.fromList (map fst args) | (_, args, rhs) <- brs ]
    DataConE _ _ es -> S.unions (map expVars es)
    TimeIt e _ _ -> expVars e
    WithArenaE v e -> S.insert v (expVars e)
    SpawnE _ _ es -> S.unions (map expVars es)
    SyncE -> S.empty
    AppE _ _ _ es -> S.unions (map expVars es)
    PrimAppE _ es -> S.unions (map expVars es)
    MapE (v, _, rhs) bod -> expVars rhs `S.union` S.delete v (expVars bod)
    FoldE (v1, _, rhs1) (v2, _, rhs2) bod ->
      S.unions [expVars rhs1, expVars rhs2, S.delete v1 (S.delete v2 (expVars bod))]
    Ext ext -> extVars ext

extVars :: L3.E3Ext () L3.Ty3 -> S.Set Var
extVars ext =
  case ext of
    L3.ReadScalar _ v -> S.singleton v
    L3.WriteScalar _ v rhs -> S.insert v (expVars rhs)
    L3.ReadTag v -> S.singleton v
    L3.WriteTag _ v -> S.singleton v
    L3.WriteTagPacked v rhs -> S.insert v (expVars rhs)
    L3.TagCursor a b -> S.fromList [a,b]
    L3.WriteCursorIndirection a b c -> S.fromList [a,b,c]
    L3.WriteCursorSelectiveIndirection a b c mask -> S.insert a (S.insert b (S.insert c (expVars mask)))
    L3.UnwrapSelectiveIndirections _ a b -> S.fromList [a,b]
    L3.WriteTaggedCursor v rhs -> S.insert v (expVars rhs)
    L3.MemCpy a b _ -> S.fromList [a,b]
    L3.ReadTaggedCursor v -> S.singleton v
    L3.ReadCursor v -> S.singleton v
    L3.GrowRegion a b -> S.fromList [a,b]
    L3.WriteCursorMutable v rhs -> S.insert v (expVars rhs)
    L3.ReadList v _ -> S.singleton v
    L3.WriteList v rhs _ -> S.insert v (expVars rhs)
    L3.ReadVector v _ -> S.singleton v
    L3.WriteVector v rhs _ -> S.insert v (expVars rhs)
    L3.MakeCursorArray _ vs -> S.fromList vs
    L3.IndexCursorArray v _ -> S.singleton v
    L3.AddCursor v rhs -> S.insert v (expVars rhs)
    L3.BumpCursorMutable v rhs -> S.insert v (expVars rhs)
    L3.AddrOfCursor rhs -> expVars rhs
    L3.DerefMutCursor v -> S.singleton v
    L3.CastPtr v _ -> S.singleton v
    L3.SubPtr a b -> S.fromList [a,b]
    L3.NewBuffer{} -> S.empty
    L3.ScopedBuffer{} -> S.empty
    L3.NewParBuffer{} -> S.empty
    L3.ScopedParBuffer{} -> S.empty
    L3.EndOfBuffer{} -> S.empty
    L3.MMapFileSize v -> S.singleton v
    L3.SizeOfPacked a b -> S.fromList [a,b]
    L3.SizeOfScalar v -> S.singleton v
    L3.BoundsCheck _ a b mb _ -> S.fromList (a:b:maybe [] (\(x,y) -> [x,y]) mb)
    L3.BoundsCheckVector xs -> S.fromList (concatMap (\(_, a, b, (c,d)) -> [a,b,c,d]) xs)
    L3.IndirectionBarrier _ (a,b,c,d) -> S.fromList [a,b,c,d]
    L3.BumpArenaRefCount a b -> S.fromList [a,b]
    L3.NullCursor -> S.empty
    L3.InitCursor{} -> S.empty
    L3.RetE es -> S.unions (map expVars es)
    L3.GetCilkWorkerNum -> S.empty
    L3.LetAvail vs bod -> S.fromList vs `S.union` expVars bod
    L3.AllocateTagHere v _ -> S.singleton v
    L3.AllocateScalarsHere v -> S.singleton v
    L3.StartTagAllocation v -> S.singleton v
    L3.EndTagAllocation v -> S.singleton v
    L3.StartScalarsAllocation v -> S.singleton v
    L3.EndScalarsAllocation v -> S.singleton v
    L3.ScalarCountBump _ vs -> S.fromList (L.map fst vs)
    L3.ScalarCountBind _ _ ends -> S.singleton ends
    L3.ScalarCountFinalize _ _ ends -> S.singleton ends
    L3.ScalarCountSet a b -> S.fromList [a,b]
    L3.ScalarCountCopyAll _ a b -> S.fromList [a,b]
    L3.ReadScalarCount v -> S.singleton v
    L3.ReadScalarCountFirstFooter v -> S.singleton v
    L3.ReadScalarCountNextFooter v -> S.singleton v
    L3.ForE i bound bod -> expVars bound `S.union` S.delete i (expVars bod)
    L3.WhileCursor v bod -> S.insert v (expVars bod)
    L3.WhileCursorEnd a b bod -> S.insert a (S.insert b (expVars bod))
    L3.VecBroadcast _ _ rhs -> expVars rhs
    L3.VecLoad _ _ v -> S.singleton v
    L3.VecAdd _ _ a b -> expVars a `S.union` expVars b
    L3.VecSub _ _ a b -> expVars a `S.union` expVars b
    L3.VecMul _ _ a b -> expVars a `S.union` expVars b
    L3.VecDiv _ _ a b -> expVars a `S.union` expVars b
    L3.VecMod _ _ a b -> expVars a `S.union` expVars b
    L3.VecCmp _ _ _ a b -> expVars a `S.union` expVars b
    L3.VecSelect _ _ m a b -> S.unions [expVars m, expVars a, expVars b]
    L3.VecStore _ _ v rhs -> S.insert v (expVars rhs)
    L3.SSPush _ a b _ -> S.fromList [a,b]
    L3.SSPop _ a b -> S.fromList [a,b]
    L3.Assert rhs -> expVars rhs

-- | The shared values discovered while building one write's DAG.
--
-- @dpOrder@ is most-recent-first, and a value is only appended after
-- everything it needs, so reversing it yields dependency order.
data DagPool = DagPool
  { dpOrder :: [(Var, ScalarDag)]
  , dpDone :: S.Set Var
  , dpBusy :: S.Set Var
  }

emptyDagPool :: DagPool
emptyDagPool = DagPool [] S.empty S.empty

type DagM = StateT DagPool Maybe

-- | Build the scalar DAG for a write's right-hand side, naming every value the
-- loop body binds instead of re-expanding it at each use.
--
-- @binds0@ is the loop body's straight-line binding list, so a variable it
-- binds names a value the scalar loop evaluated exactly once and
-- unconditionally.  Those are the variables that become 'DagLet's, which is
-- what makes the whole construction linear: without it, 'resolveVarRhs'
-- re-expands a variable at every use and a chain of bindings each used twice
-- costs 2^depth.
--
-- Bindings looked through inside a conditional arm (see 'administrativeBind')
-- are deliberately NOT shared: a 'DagLet' sits at the root, and hoisting an
-- arm-local computation there would move it out of the guard that dominates
-- it.
matchScalarDag :: Bool -> L3.Scalar -> Var -> [Bind3] -> L3.Exp3 -> Maybe ScalarDag
matchScalarDag w64Mul scalar idx binds0 expr0 = do
  (root, pool) <- runStateT (matchScalarDagM w64Mul scalar idx outer binds0 expr0) emptyDagPool
  pure $ L.foldr (\(v, d) acc -> DagLet v d acc) root (reverse (dpOrder pool))
  where
    outer = S.fromList [ v | (v, _, _, _) <- binds0 ]

matchScalarDagM :: Bool -> L3.Scalar -> Var -> S.Set Var -> [Bind3] -> L3.Exp3 -> DagM ScalarDag
matchScalarDagM w64Mul scalar idx outer binds expr0 =
  case expr0 of
    VarE v ->
      case resolveVarRhs binds S.empty v of
        VarE v' | v == v' -> matchNonVar expr0
        rhs
          | v `S.member` outer -> shareVar v rhs
          | otherwise -> recur rhs
    _ -> matchNonVar expr0
  where
    recur = matchScalarDagM w64Mul scalar idx outer binds

    -- Record @v@'s DAG once and hand back a reference to it.
    --
    -- A value whose DAG contains a partial operation is expanded inline
    -- instead, exactly as before this sharing existed: 'dagSpeculatesPartialOp'
    -- decides safety from the operation's POSITION, and moving a division to
    -- the root would change the position it judges.  Divisions are rare and
    -- shallow, so re-expanding them cannot drive the blow-up that sharing
    -- exists to prevent.
    shareVar v rhs = do
      pool <- get
      if v `S.member` dpDone pool
        then pure (DagShared v)
        else if v `S.member` dpBusy pool
               then lift Nothing   -- cyclic binding: keep the loop scalar
               else do
                 modify' $ \p -> p { dpBusy = S.insert v (dpBusy p) }
                 d <- recur rhs
                 modify' $ \p -> p { dpBusy = S.delete v (dpBusy p) }
                 if dagHasPartialOp d
                   then pure d
                   else do
                     modify' $ \p -> p { dpOrder = (v, d) : dpOrder p
                                       , dpDone = S.insert v (dpDone p) }
                     pure (DagShared v)

    matchNonVar expr =
      case readValueInputRef scalar binds expr of
        Just ref -> pure (DagRead ref)
        Nothing
          | Just (deps, ex) <- loopInvariantHoistExpr scalar idx binds expr ->
              pure (DagInvariant deps ex)
        Nothing ->
          case expr of
            -- A conversion between one width and itself is the identity, so
            -- match its operand instead of declining.  Widening or narrowing
            -- is NOT looked through: 'matchScalarDagM' threads the write's
            -- scalar into every operand, so an operand of a different width
            -- would be loaded with the wrong lane count.
            PrimAppE prim [a]
              | identityIntConvert prim -> recur a
            PrimAppE prim [a, b]
              | simdPrimSupported w64Mul scalar prim ->
                  DagBin prim <$> recur a <*> recur b
            IfE tst thenExp elseExp ->
              DagIf <$> matchCondDagM w64Mul scalar idx outer binds tst
                    <*> recur thenExp
                    <*> recur elseExp
            -- Look THROUGH an administrative let, never around it.
            --
            -- `LoopifyTraversals.anfScalarExpr` keeps the bindings it creates
            -- for an `IfE` arm inside that arm, which is what stops a guarded
            -- division being hoisted above its guard.  Those arms therefore
            -- arrive here as `let anfN = ... in anfN` rather than a bare
            -- variable, and without this case every conditional -- total ones
            -- included -- would stop vectorising.
            --
            -- Extending the local environment is exactly "see through": the
            -- binding is added to `binds` so `resolveVarRhs` can follow it, and
            -- it is NOT lifted anywhere.  The DAG that results still describes
            -- the arm, so `dagSpeculatesPartialOp` still sees a division inside
            -- it and still refuses the loop.
            LetE bnd bod
              | administrativeBind bnd bod ->
                  matchScalarDagM w64Mul scalar idx outer (binds ++ [bnd]) bod
            _ -> lift Nothing

matchCondDagM :: Bool -> L3.Scalar -> Var -> S.Set Var -> [Bind3] -> L3.Exp3 -> DagM CondDag
matchCondDagM w64Mul resultScalar idx outer binds expr0 =
  case expr0 of
    VarE v ->
      case resolveVarRhs binds S.empty v of
        VarE v' | v == v' -> matchNonVar expr0
        rhs -> matchCondDagM w64Mul resultScalar idx outer binds rhs
    _ -> matchNonVar expr0
  where
    scalarArg = matchScalarDagM w64Mul resultScalar idx outer binds

    matchNonVar expr =
      case expr of
        -- Every source comparison, not just equality.  Structural on the
        -- annotated primitive (never `elem`), and gated on the SAME shared
        -- capability matrix the backend consults -- so an ordered comparison
        -- at a width with no packed instruction (W64, Float) answers Nothing
        -- here and the whole loop stays scalar.
        PrimAppE pr [a, b]
          | Just cmp <- intCmpPrim pr
          , L3.isIntScalar resultScalar
          , L3.simdCapable (L3.vecCmpOp cmp) resultScalar ->
          CondCmp resultScalar cmp <$> scalarArg a <*> scalarArg b
        PrimAppE EqFloatP [a, b]
          | resultScalar == L3.FloatS
          , L3.simdCapable L3.VecOpEq L3.FloatS ->
          CondCmp L3.FloatS L3.VecCmpEq
            <$> matchScalarDagM w64Mul L3.FloatS idx outer binds a
            <*> matchScalarDagM w64Mul L3.FloatS idx outer binds b
        -- Same administrative-let transparency as 'matchScalarDagM'; a
        -- condition can be ANF'd into a let too.
        LetE bnd bod
          | administrativeBind bnd bod ->
              matchCondDagM w64Mul resultScalar idx outer (binds ++ [bnd]) bod
        _ -> lift Nothing

-- | May this binding be looked through when matching a scalar DAG, given the
-- body it scopes over?
--
-- "Look through" must never become "discard".  The DAG has no representation
-- for a binding: `resolveVarRhs` re-expands the variable at each use, so a
-- binder used twice would duplicate its sub-DAG, and a binder used zero times
-- would vanish from the vector body entirely.  Both are fine for a total,
-- effect-free right-hand side -- recomputing or skipping pure total arithmetic
-- changes nothing observable -- and neither is acceptable otherwise.
--
-- So the rule is: the RHS must be a scalar expression whose primitives are all
-- classified, and it must be either
--
--   * total and effect-free, or
--   * referenced exactly once in the body.
--
-- Anything else -- a read, a write, any 'Ext', an unclassified primitive,
-- `ErrorP`, a trapping division bound but unused -- keeps the whole buffer loop
-- scalar.  A conservative scalar fallback is always correct here; dropping or
-- duplicating a right-hand side is not.
administrativeBind :: Bind3 -> L3.Exp3 -> Bool
administrativeBind (v, _, _, rhs) bod =
  case scalarExprClass rhs of
    Nothing -> False
    Just EffTotal -> True
    Just _ -> occurrencesOf v bod == 1

-- | Free occurrences of a variable, counted over the shapes a scalar
-- expression can take.  Any other form is opaque and reported as "many", so an
-- expression this function does not understand can never be mistaken for a
-- single-use one.
occurrencesOf :: Var -> L3.Exp3 -> Int
occurrencesOf v = go
  where
    go ex =
      case ex of
        VarE v' -> if v' == v then 1 else 0
        LitE{} -> 0
        CharE{} -> 0
        FloatE{} -> 0
        LitSymE{} -> 0
        PrimAppE _ args -> sum (map go args)
        ProjE _ e -> go e
        IfE a b c -> sum (map go [a, b, c])
        LetE (_, _, _, rhs) bod -> go rhs + go bod
        _ -> 2   -- unknown shape: never treat as single-use

-- | The comparison a width-annotated integer comparison primitive performs.
--
-- Structural: these primitives carry an 'IntPrimAnn', so an equality test
-- against a bare constructor would silently match only one width.
intCmpPrim :: Prim L3.Ty3 -> Maybe L3.VecCmpOp
intCmpPrim pr =
  case pr of
    EqIntP{} -> Just L3.VecCmpEq
    LtP{}    -> Just L3.VecCmpLt
    GtP{}    -> Just L3.VecCmpGt
    LtEqP{}  -> Just L3.VecCmpLtEq
    GtEqP{}  -> Just L3.VecCmpGtEq
    _ -> Nothing

-- | Does this DAG evaluate a partial (potentially trapping) operation inside a
-- conditional arm?
--
-- `emitVectorDag` lowers `DagIf` by evaluating both arms and then selecting, so
-- an operation that the scalar program only reached under a guard becomes
-- unconditional.  For @if d == 0 then 0 else n / d@ that is a SIGFPE.  Only the
-- speculated positions matter: a partial operation that the scalar loop also
-- evaluates unconditionally is evaluated for exactly the same elements by the
-- vector loop plus its scalar remainder, so it stays correct.
dagSpeculatesPartialOp :: ScalarDag -> Bool
dagSpeculatesPartialOp dag =
  case dag of
    DagRead{} -> False
    DagInvariant{} -> False
    DagShared{} -> False
    -- A 'DagLet' sits outside every 'DagIf' by construction, so its
    -- right-hand side occupies an unconditional position, exactly like the
    -- scalar binding it came from.
    DagLet _ rhs bod -> dagSpeculatesPartialOp rhs || dagSpeculatesPartialOp bod
    DagBin _ a b -> dagSpeculatesPartialOp a || dagSpeculatesPartialOp b
    DagIf cond thenDag elseDag ->
      condSpeculatesPartialOp cond ||
      dagHasPartialOp thenDag ||
      dagHasPartialOp elseDag

condSpeculatesPartialOp :: CondDag -> Bool
condSpeculatesPartialOp (CondCmp _ _ a b) =
  dagSpeculatesPartialOp a || dagSpeculatesPartialOp b

-- | Does this DAG contain a partial operation anywhere?
dagHasPartialOp :: ScalarDag -> Bool
dagHasPartialOp dag =
  case dag of
    DagRead{} -> False
    -- Check the hoisted dependencies too, not just the invariant expression:
    -- they are spliced outside the loop and so run even on a zero-trip loop,
    -- which is precisely the hazard the partial-op exclusion exists to prevent.
    DagInvariant deps ex ->
      exprHasPartialPrim ex ||
      any (\(_, _, _, rhs) -> exprHasPartialPrim rhs) deps
    DagShared{} -> False
    DagLet _ rhs bod -> dagHasPartialOp rhs || dagHasPartialOp bod
    DagBin prim a b -> isPartialPrim prim || dagHasPartialOp a || dagHasPartialOp b
    DagIf cond thenDag elseDag ->
      condHasPartialOp cond || dagHasPartialOp thenDag || dagHasPartialOp elseDag

condHasPartialOp :: CondDag -> Bool
condHasPartialOp (CondCmp _ _ a b) = dagHasPartialOp a || dagHasPartialOp b

exprHasPartialPrim :: L3.Exp3 -> Bool
exprHasPartialPrim ex =
  case ex of
    PrimAppE prim args -> isPartialPrim prim || any exprHasPartialPrim args
    IfE a b c -> any exprHasPartialPrim [a, b, c]
    ProjE _ e -> exprHasPartialPrim e
    _ -> False

-- | Primitives that are undefined (and on x86 trap) for some operand values.
-- Integer division and remainder raise #DE on a zero divisor; float division is
-- listed too because the vectorizer must not be the thing that decides an
-- IEEE-special result is acceptable.
-- | Structural constructor tests for the width-annotated integer primitives.
-- Never compare these with (==) or `elem`: the width annotation is part of the
-- constructor, so equality would only match one width.
isAddSub :: Prim ty -> Bool
isAddSub p = case p of { AddP{} -> True ; SubP{} -> True ; _ -> False }

isAddSubMul :: Prim ty -> Bool
isAddSubMul p = case p of { MulP{} -> True ; _ -> isAddSub p }

isDivMod :: Prim ty -> Bool
isDivMod p = case p of { DivP{} -> True ; ModP{} -> True ; _ -> False }

isSimpleArithPrim :: Prim ty -> Bool
isSimpleArithPrim p =
  case p of
    FAddP -> True ; FSubP -> True ; FMulP -> True
    _     -> isAddSubMul p

isPartialPrim :: Prim L3.Ty3 -> Bool
isPartialPrim prim = case prim of
                       DivP{} -> True
                       ModP{} -> True
                       FDivP  -> True
                       _      -> False

nonEmptyReadRefs :: ScalarDag -> Maybe (S.Set Var)
nonEmptyReadRefs dag =
  let refs = readRefs dag
  in if S.null refs then Nothing else Just refs

readRefs :: ScalarDag -> S.Set Var
readRefs dag =
  case dag of
    DagRead ref -> S.singleton ref
    DagInvariant{} -> S.empty
    DagShared{} -> S.empty
    DagLet _ rhs bod -> readRefs rhs `S.union` readRefs bod
    DagBin _ a b -> readRefs a `S.union` readRefs b
    DagIf c a b -> condReadRefs c `S.union` readRefs a `S.union` readRefs b

condReadRefs :: CondDag -> S.Set Var
condReadRefs cond =
  case cond of
    CondCmp _ _ a b -> readRefs a `S.union` readRefs b

readValueInputRef :: L3.Scalar -> [Bind3] -> L3.Exp3 -> Maybe Var
readValueInputRef scalar binds expr = do
  pair <- readPairOf expr
  readCur <- readScalarCursor scalar pair binds
  derefSource readCur binds
  where
    readPairOf e =
      case e of
        ProjE 0 (VarE pair) -> Just pair
        VarE v -> lookupProjAlias v binds
        _ -> Nothing

lookupProjAlias :: Var -> [Bind3] -> Maybe Var
lookupProjAlias v binds =
  case lookupBind v binds of
    ProjE 0 (VarE pair) -> Just pair
    _ -> Nothing

readScalarCursor :: L3.Scalar -> Var -> [Bind3] -> Maybe Var
readScalarCursor scalar pair binds =
  case lookupBind pair binds of
    Ext (L3.ReadScalar scalar' cur)
      | scalar == scalar' -> Just cur
    _ -> Nothing

derefSource :: Var -> [Bind3] -> Maybe Var
derefSource cur binds =
  case lookupBind cur binds of
    Ext (L3.DerefMutCursor ref) -> Just ref
    _ -> Nothing

lookupBind :: Var -> [Bind3] -> L3.Exp3
lookupBind v binds =
  case L.find (\(v', _, _, _) -> v == v') binds of
    Just (_, _, _, rhs) -> rhs
    Nothing -> VarE v

-- | Decide whether @expr@ can be hoisted out of the loop, and if so return the
-- loop-body-local bindings it depends on (in dependency order) together with
-- the expression itself.
--
-- `prepareVectorDag` splices hoisted binds *outside* the loop, where the loop
-- body's own let-bindings are not in scope.  Hoisting an invariant that
-- mentions a body-local variable therefore emitted a dangling reference:
--
--     Var loop_mut_<n>_buf1_anf0 not found   (L3/Typecheck.hs:1157)
--
-- triggered by a two-level invariant such as
--
--     t1 = k + 1        -- body-local, itself invariant
--     m1 = t1 * 2       -- invariant, but mentions t1
--     x1 = i * m1 + 1
--
-- A single-level invariant (@m1 = 2 * k@) worked only because @k@ is a function
-- parameter and so already in scope outside the loop.
--
-- The dependencies are returned as BINDINGS rather than being substituted into
-- one expression: L3 is in A-normal form and `Lower` rejects a nested
-- @PrimAppE@ operand ("expected trivial in prim rand"), so the fix has to
-- preserve the let-structure, not flatten it.
--
-- The invariance, totality and no-read checks are applied to every dependency
-- as well as to the expression, so a variable whose right-hand side depends on
-- the loop index or performs a read can no longer slip through behind a
-- @VarE@.
loopInvariantHoistExpr :: L3.Scalar -> Var -> [Bind3] -> L3.Exp3
                       -> Maybe ([Bind3], L3.Exp3)
loopInvariantHoistExpr _scalar idx binds expr
  -- Screen the shape FIRST: `gFreeVars` errors out on L3 extensions such as
  -- `DerefMutCursor`, so nothing that is not already a simple scalar form may
  -- reach the dependency walk below.
  | not (isSimpleScalarExpr expr) = Nothing
  | otherwise = do
  (_, deps) <- collectInvariantDeps binds (S.empty, []) expr
  let exprs = expr : [ rhs | (_, _, _, rhs) <- deps ]
  if all ok exprs && all (\e -> idx `S.notMember` gFreeVars e) exprs
    then Just (deps, expr)
    else Nothing
  where
    ok e = isSimpleScalarExpr e && not (exprContainsAnyRead binds e)

-- | Transitively collect the loop-body-local bindings an expression depends on,
-- in dependency order (a binding always appears after everything it needs).
-- Variables not bound in the loop body are already in scope outside it and are
-- left alone.  The @seen@ set makes cyclic bindings terminate rather than loop.
collectInvariantDeps :: [Bind3] -> (S.Set Var, [Bind3]) -> L3.Exp3
                     -> Maybe (S.Set Var, [Bind3])
collectInvariantDeps binds st expr = foldM go st (S.toList (gFreeVars expr))
  where
    go (seen, acc) v
      | v `S.member` seen = Just (seen, acc)
      | otherwise =
          case L.find (\(v', _, _, _) -> v == v') binds of
            Nothing -> Just (S.insert v seen, acc)
            -- Only descend into right-hand sides that are themselves simple
            -- scalar forms.  A binding that reads a buffer or dereferences a
            -- mutable cursor is not hoistable, and `gFreeVars` cannot even be
            -- applied to it, so bail out rather than recursing.
            Just b@(_, _, _, rhs)
              | isSimpleScalarExpr rhs -> do
                  (seen', acc') <- collectInvariantDeps binds (S.insert v seen, acc) rhs
                  pure (seen', acc' ++ [b])
              | otherwise -> Nothing

-- | Rename variables in the restricted expression forms a hoisted invariant can
-- contain.  Used to freshen dependency bindings so that two invariants sharing
-- a dependency do not emit the same binder twice.
substInvariantVars :: M.Map Var Var -> L3.Exp3 -> L3.Exp3
substInvariantVars sub e =
  case e of
    VarE v -> VarE (M.findWithDefault v v sub)
    PrimAppE p args -> PrimAppE p (map (substInvariantVars sub) args)
    _ -> e

exprContainsAnyRead :: [Bind3] -> L3.Exp3 -> Bool
exprContainsAnyRead binds expr =
  case expr of
    VarE v ->
      case resolveVarRhs binds S.empty v of
        VarE v' | v == v' -> False
        Ext (L3.ReadScalar{}) -> True
        rhs -> exprContainsAnyRead binds rhs
    ProjE _ arg -> exprContainsAnyRead binds arg
    PrimAppE _ args -> any (exprContainsAnyRead binds) args
    IfE a b c -> any (exprContainsAnyRead binds) [a,b,c]
    Ext (L3.ReadScalar{}) -> True
    _ -> False

-- | Expressions that may be hoisted out of the loop and evaluated once per
-- chunk by `prepareVectorDag` / `mkVectorizedScalarLoop`.
--
-- `mkVectorizedScalarLoop` splices the hoisted binds *before* both the vector
-- loop and the scalar remainder loop, so they run even when the trip count is
-- zero and the scalar loop body never executed.  Hoisting is therefore only
-- valid for TOTAL expressions: an invariant @k / m@ with @m == 0@ must not be
-- evaluated on behalf of a loop that runs zero times.  Partial primitives
-- (`DivP`, `ModP`, `FDivP`) are excluded here; they are still vectorizable, but
-- as ordinary `DagBin` nodes inside the loop body, where they execute exactly
-- as often as the scalar loop would have executed them.
isSimpleScalarExpr :: L3.Exp3 -> Bool
isSimpleScalarExpr expr =
  case expr of
    VarE{} -> True
    LitE{} -> True
    CharE{} -> True
    FloatE{} -> True
    LitSymE{} -> True
    PrimAppE p [arg]
      | identityIntConvert p -> isSimpleScalarExpr arg
    PrimAppE p args
      | isSimpleArithPrim p ->
          all isSimpleScalarExpr args
    _ -> False

-- | An integer conversion from a width to itself.
--
-- It computes nothing, but it is not an arithmetic primitive either, so
-- without this it disqualifies whatever expression it appears in -- and with
-- it the whole loop, because a loop is vectorized only when every one of its
-- writes matches.  Conversions that really change width stay out: see
-- 'matchScalarDagM'.
identityIntConvert :: Prim ty -> Bool
identityIntConvert p =
  case p of
    IntConvertP (IntPrimWidth src) dst -> src == dst
    _ -> False

-- | The vector operation a scalar primitive would lower to, if any.
--
-- Structural, never an `elem` over annotated constructors: an integer
-- primitive carries a width, so equality against a bare constructor silently
-- stops matching every width but one.
primVecOp :: Prim L3.Ty3 -> Maybe L3.VecOp
primVecOp prim =
  case prim of
    AddP{} -> Just L3.VecOpAdd
    SubP{} -> Just L3.VecOpSub
    MulP{} -> Just L3.VecOpMul
    DivP{} -> Just L3.VecOpDiv
    ModP{} -> Just L3.VecOpMod
    EqIntP{} -> Just L3.VecOpEq
    FAddP -> Just L3.VecOpAdd
    FSubP -> Just L3.VecOpSub
    FMulP -> Just L3.VecOpMul
    FDivP -> Just L3.VecOpDiv
    EqFloatP -> Just L3.VecOpEq
    _ -> Nothing

-- | Can this primitive be vectorized at this scalar width?
--
-- Asks the ONE shared capability matrix ('L3.simdCapable'), so the vectorizer
-- can never answer "yes" to something the backend cannot lower.  In
-- particular @MulP@\/@DivP@\/@ModP@ at W32 answer False here, which leaves the
-- whole candidate loop scalar rather than emitting vector IR whose helper
-- would spill lanes to a scalar array.
simdPrimSupported :: Bool -> L3.Scalar -> Prim L3.Ty3 -> Bool
simdPrimSupported w64Mul scalar prim =
  case primVecOp prim of
    Nothing -> False
    Just op -> L3.simdCapableWith w64Mul op scalar

resolveVarRhs :: [Bind3] -> S.Set Var -> Var -> L3.Exp3
resolveVarRhs binds seen v
  | v `S.member` seen = VarE v
  | otherwise =
      case lookupBind v binds of
        VarE v'
          | v' /= v -> resolveVarRhs binds (S.insert v seen) v'
        rhs -> rhs

hasCursorBump :: SimdCfg -> Var -> L3.Scalar -> [Bind3] -> Bool
hasCursorBump cfg ref scalar binds =
  any matches binds
  where
    bytes = scalarWidthBytes cfg scalar
    matches (_, _, _, Ext (L3.BumpCursorMutable ref' (LitE _ n))) = ref == ref' && n == fromIntegral bytes
    matches _ = False

-- | Which scalars the vectorizer can currently handle.
--
-- Structural, never an `elem` over constructors: the integer scalar carries a
-- width, so a list comparison would silently answer False for every width but
-- one.
--
-- A scalar with no emitted SIMD helper is declared unsupported here rather
-- than have lane counts miscomputed for it, and is left on the scalar path.
scalarSupported :: L3.Scalar -> Bool
scalarSupported = L3.simdScalarEnabled

vectorLanes :: SimdCfg -> L3.Scalar -> Int
vectorLanes cfg = L3.simdLanes (scRegBytes cfg)

vectorBytes :: SimdCfg -> L3.Scalar -> Int
vectorBytes cfg scalar = vectorLanes cfg scalar * scalarWidthBytes cfg scalar

scalarWidthBytes :: SimdCfg -> L3.Scalar -> Int
scalarWidthBytes _ = L3.simdScalarBytes

unLets3 :: L3.Exp3 -> ([Bind3], L3.Exp3)
unLets3 (LetE b bod) =
  let (bs, tailExp) = unLets3 bod
  in (b:bs, tailExp)
unLets3 e = ([], e)

infixl 3 <|>
(<|>) :: Maybe a -> Maybe a -> Maybe a
Just x <|> _ = Just x
Nothing <|> y = y

-- | @--opt-vectorization@ with nothing to vectorize.
--
-- The asymmetry this removes: omitting @--opt-loopification@ is the hard error
-- in 'vectorizeTraversals', while omitting @--use-mutable-cursors@ produced a
-- silent exit 0 with no vectorized call site anywhere.  In the real pipeline
-- neither loopification pass can emit a loop without it -- the AoS pass
-- requires mutable-cursor ABI formals, which only 'InferCallType' installs
-- under the flag, and an SoA candidate's returned cursors, threaded through
-- the recursion, read as a parent-child dependency.
--
-- Checked here rather than inside 'vectorizeTraversals' because it is a
-- property of the whole compile: the pass on its own can be handed a program
-- already in mutable-cursor form, and then it does loopify.
--
-- Asked of the program, not of the flags alone: a program that nominated no
-- function has nothing to vectorize either way, and saying so would be a false
-- alarm.
validateVectorizationFired :: DynFlags -> L3.Prog3 -> IO ()
validateVectorizationFired dflags Prog{fundefs}
  | gopt Opt_EnableVectorization dflags
  , not (gopt Opt_UseMutableCursors dflags)
  , not (any (\fd -> Loopified `elem` funOpt (funMeta fd)) (M.elems fundefs))
  , (gopt Opt_AutoLoopification dflags && hasPackedTraversal) || not (null nominated)
  = error $
      "vectorizeTraversals: --opt-vectorization is enabled and " ++
      described ++ ", but --use-mutable-cursors is not.\n" ++
      "Without it neither loopification pass emits a loop, so no function is " ++
      "vectorized and the compile would otherwise succeed silently with no " ++
      "vectorized call site at all.\n" ++
      "Add --use-mutable-cursors to the compile command."
  | otherwise = pure ()
  where
    nominated =
      L.sort [ fromVar (funName fd)
             | fd <- M.elems fundefs
             , MayVectorize `elem` funOpt (funMeta fd) ]
    -- Under --auto-loopification nothing is annotated, so the question is
    -- whether the program has any packed traversal to infer from at all.  A
    -- program with no packed data has nothing to vectorize with or without
    -- mutable cursors.
    hasPackedTraversal =
      any (not . null . collectMentionedDataCons . funBody)
          [ fd | fd <- M.elems fundefs, not (isGeneratedPackedHelper (funName fd)) ]
    described =
      case nominated of
        (f0 : _) -> show f0 ++ " carries OPT:MayVectorize"
        [] -> "--auto-loopification is inferring candidates"
