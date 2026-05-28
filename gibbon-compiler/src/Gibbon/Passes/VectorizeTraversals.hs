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
  ) where

import Control.Monad (guard, forM)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, listToMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3

type Bind3 = (Var, [()], L3.Ty3, L3.Exp3)

vectorizeTraversals :: L3.Prog3 -> PassM L3.Prog3
vectorizeTraversals prog@Prog{fundefs} = do
  dflags <- getDynFlags
  if not (gopt Opt_EnableVectorization dflags)
    then pure prog
    else do
      let intBytes = if gopt Opt_Int32 dflags then 4 else 8
      fds' <- mapM (vectorizeFun intBytes) (M.elems fundefs)
      pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

vectorizeFun :: Int -> L3.FunDef3 -> PassM L3.FunDef3
vectorizeFun intBytes fn@FunDef{funMeta, funBody}
  | CanVectorize `notElem` funOpt funMeta = pure fn
  | otherwise = do
      body' <- vectorizeExp intBytes funBody
      pure $ fn { funBody = body' }

vectorizeExp :: Int -> L3.Exp3 -> PassM L3.Exp3
vectorizeExp intBytes ex =
  case ex of
    LetE (v, locs, ty, Ext (L3.ForE idx bound loopBody)) bod -> do
      bod' <- vectorizeExp intBytes bod
      case matchSimdLoop intBytes idx loopBody of
        Just simdLoop -> do
          bound' <- vectorizeExp intBytes bound
          vecLoop <- mkVectorizedScalarLoop intBytes idx bound' loopBody simdLoop
          pure $ LetE (v, locs, ty, vecLoop) bod'
        Nothing -> do
          bound' <- vectorizeExp intBytes bound
          loopBody' <- vectorizeExp intBytes loopBody
          pure $ LetE (v, locs, ty, Ext (L3.ForE idx bound' loopBody')) bod'

    LetE (v, locs, ty, rhs) bod -> do
      rhs' <- vectorizeExp intBytes rhs
      bod' <- vectorizeExp intBytes bod
      pure $ LetE (v, locs, ty, rhs') bod'

    IfE tst a b -> IfE <$> vectorizeExp intBytes tst <*> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    CaseE scrt brs -> do
      scrt' <- vectorizeExp intBytes scrt
      brs' <- mapM (\(dc, vs, rhs) -> (dc, vs,) <$> vectorizeExp intBytes rhs) brs
      pure $ CaseE scrt' brs'
    MkProdE es -> MkProdE <$> mapM (vectorizeExp intBytes) es
    ProjE i e -> ProjE i <$> vectorizeExp intBytes e
    PrimAppE p es -> PrimAppE p <$> mapM (vectorizeExp intBytes) es
    DataConE loc dc es -> DataConE loc dc <$> mapM (vectorizeExp intBytes) es
    AppE f c locs es -> AppE f c locs <$> mapM (vectorizeExp intBytes) es
    SpawnE f locs es -> SpawnE f locs <$> mapM (vectorizeExp intBytes) es
    WithArenaE v e -> WithArenaE v <$> vectorizeExp intBytes e
    TimeIt e ty isIter -> TimeIt <$> vectorizeExp intBytes e <*> pure ty <*> pure isIter
    MapE (v, ty, rhs) bod -> MapE . (v, ty,) <$> vectorizeExp intBytes rhs <*> vectorizeExp intBytes bod
    FoldE (v1, t1, rhs1) (v2, t2, rhs2) bod ->
      FoldE <$> ((v1, t1,) <$> vectorizeExp intBytes rhs1)
            <*> ((v2, t2,) <$> vectorizeExp intBytes rhs2)
            <*> vectorizeExp intBytes bod

    Ext ext -> Ext <$> vectorizeExt intBytes ext
    VarE{} -> pure ex
    LitE{} -> pure ex
    CharE{} -> pure ex
    FloatE{} -> pure ex
    LitSymE{} -> pure ex
    SyncE -> pure ex

vectorizeExt :: Int -> L3.E3Ext () L3.Ty3 -> PassM (L3.E3Ext () L3.Ty3)
vectorizeExt intBytes ext =
  case ext of
    L3.WriteScalar s v rhs -> L3.WriteScalar s v <$> vectorizeExp intBytes rhs
    L3.WriteTagPacked v rhs -> L3.WriteTagPacked v <$> vectorizeExp intBytes rhs
    L3.WriteCursorSelectiveIndirection a b c mask ->
      L3.WriteCursorSelectiveIndirection a b c <$> vectorizeExp intBytes mask
    L3.WriteTaggedCursor v rhs -> L3.WriteTaggedCursor v <$> vectorizeExp intBytes rhs
    L3.WriteCursorMutable v rhs -> L3.WriteCursorMutable v <$> vectorizeExp intBytes rhs
    L3.WriteList v rhs ty -> L3.WriteList v <$> vectorizeExp intBytes rhs <*> pure ty
    L3.WriteVector v rhs ty -> L3.WriteVector v <$> vectorizeExp intBytes rhs <*> pure ty
    L3.AddCursor v rhs -> L3.AddCursor v <$> vectorizeExp intBytes rhs
    L3.BumpCursorMutable v rhs -> L3.BumpCursorMutable v <$> vectorizeExp intBytes rhs
    L3.AddrOfCursor rhs -> L3.AddrOfCursor <$> vectorizeExp intBytes rhs
    L3.RetE es -> L3.RetE <$> mapM (vectorizeExp intBytes) es
    L3.LetAvail vs bod -> L3.LetAvail vs <$> vectorizeExp intBytes bod
    L3.ForE idx bound bod -> L3.ForE idx <$> vectorizeExp intBytes bound <*> vectorizeExp intBytes bod
    L3.WhileCursor ref bod -> L3.WhileCursor ref <$> vectorizeExp intBytes bod
    L3.WhileCursorEnd ref end bod -> L3.WhileCursorEnd ref end <$> vectorizeExp intBytes bod
    L3.VecBroadcast s lanes val -> L3.VecBroadcast s lanes <$> vectorizeExp intBytes val
    L3.VecLoad{} -> pure ext
    L3.VecAdd s lanes a b -> L3.VecAdd s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecSub s lanes a b -> L3.VecSub s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecMul s lanes a b -> L3.VecMul s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecDiv s lanes a b -> L3.VecDiv s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecMod s lanes a b -> L3.VecMod s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecEq s lanes a b -> L3.VecEq s lanes <$> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecSelect s lanes m a b -> L3.VecSelect s lanes <$> vectorizeExp intBytes m <*> vectorizeExp intBytes a <*> vectorizeExp intBytes b
    L3.VecStore s lanes ref val -> L3.VecStore s lanes ref <$> vectorizeExp intBytes val
    L3.Assert rhs -> L3.Assert <$> vectorizeExp intBytes rhs
    _ -> pure ext

data ScalarDag
  = DagRead Var
  | DagInvariant L3.Exp3
  | DagBin (Prim L3.Ty3) ScalarDag ScalarDag
  | DagIf CondDag ScalarDag ScalarDag
  deriving (Show, Eq)

data CondDag
  = CondEq L3.Scalar ScalarDag ScalarDag
  deriving (Show, Eq)

data VectorDag
  = VDagRead Var
  | VDagInvariant Var
  | VDagBin (Prim L3.Ty3) VectorDag VectorDag
  | VDagIf VectorCondDag VectorDag VectorDag
  deriving (Show, Eq)

data VectorCondDag
  = VCondEq L3.Scalar VectorDag VectorDag
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

newtype SimdLoop = SimdLoop
  { slOps :: [SimdOp]
  }

mkVectorizedScalarLoop :: Int -> Var -> L3.Exp3 -> L3.Exp3 -> SimdLoop -> PassM L3.Exp3
mkVectorizedScalarLoop intBytes _idx bound scalarLoopBody SimdLoop{slOps} = do
  vecCount <- gensym "simd_vec_count"
  tailCount <- gensym "simd_tail_count"
  vecLoopIdx <- gensym "simd_i"
  tailLoopIdx <- gensym "simd_tail_i"
  vecLoopUnit <- gensym "simd_vec_loop"
  tailLoopUnit <- gensym "simd_tail_loop"
  prepared <- forM slOps $ \SimdOp{soScalar, soInRefs, soOutRef, soDag} -> do
    (broadcasts, vdag) <- prepareVectorDag intBytes soScalar soDag
    pure (broadcasts, PreparedSimdOp soScalar soInRefs soOutRef vdag)
  let broadcasts = concatMap fst prepared
      ops = map snd prepared
      stride = case ops of
                 op:_ -> vectorStride intBytes (poScalar op)
                 [] -> error "mkVectorizedScalarLoop: empty SIMD operation list"
      unitTy = ProdTy []
  vecBody <- mkVectorLoopBody intBytes stride ops
  let binds =
        [ (vecCount, [], IntTy, PrimAppE DivP [bound, LitE (fromIntegral stride)])
        , (tailCount, [], IntTy, PrimAppE ModP [bound, LitE (fromIntegral stride)])
        ] ++ broadcasts ++
        [ (vecLoopUnit, [], unitTy, Ext (L3.ForE vecLoopIdx (VarE vecCount) vecBody))
        , (tailLoopUnit, [], unitTy, Ext (L3.ForE tailLoopIdx (VarE tailCount) scalarLoopBody))
        ]
  pure $ mkLets binds (MkProdE [])

prepareVectorDag :: Int -> L3.Scalar -> ScalarDag -> PassM ([Bind3], VectorDag)
prepareVectorDag intBytes scalar dag =
  case dag of
    DagRead ref -> pure ([], VDagRead ref)
    DagInvariant ex -> do
      scalarV <- gensym "simd_invariant_scalar"
      v <- gensym "simd_invariant_vec"
      let lanes = vectorLanes intBytes scalar
          scalarTy = L3.scalarToTy scalar
          vecTy = L3.SimdTy scalarTy lanes
      pure ( [ (scalarV, [], scalarTy, ex)
             , (v, [], vecTy, Ext (L3.VecBroadcast scalar lanes (VarE scalarV)))
             ]
           , VDagInvariant v)
    DagBin prim a b -> do
      (ab, av) <- prepareVectorDag intBytes scalar a
      (bb, bv) <- prepareVectorDag intBytes scalar b
      pure (ab ++ bb, VDagBin prim av bv)
    DagIf cond thenDag elseDag -> do
      (cb, cvec) <- prepareVectorCondDag intBytes cond
      (tb, tvec) <- prepareVectorDag intBytes scalar thenDag
      (eb, evec) <- prepareVectorDag intBytes scalar elseDag
      pure (cb ++ tb ++ eb, VDagIf cvec tvec evec)

prepareVectorCondDag :: Int -> CondDag -> PassM ([Bind3], VectorCondDag)
prepareVectorCondDag intBytes cond =
  case cond of
    CondEq scalar a b -> do
      (ab, av) <- prepareVectorDag intBytes scalar a
      (bb, bv) <- prepareVectorDag intBytes scalar b
      pure (ab ++ bb, VCondEq scalar av bv)

-- | Emit one logical stride of vector work.  Fused loopified traversals can put
-- several independent scalar-buffer writes in the same `ForE`; this routine
-- handles all of them together.  Loads are keyed by (scalar kind, cursor ref),
-- so a DAG that mentions the same input more than once still performs one vector
-- load per group.
mkVectorLoopBody :: Int -> Int -> [PreparedSimdOp] -> PassM L3.Exp3
mkVectorLoopBody intBytes _stride ops = do
  let maxGroups = maximum (map (vectorGroups intBytes . poScalar) ops)
  groups <- forM [0 .. maxGroups - 1] $ \groupIx -> do
    let groupOps = filter (\op -> groupIx < vectorGroups intBytes (poScalar op)) ops
        readKeys = L.nub
          [ (poScalar op, ref)
          | op <- groupOps
          , ref <- S.toList (vectorReadRefs (poDag op))
          ]
        skipKeys = L.nub
          [ (poScalar op, ref)
          | op <- groupOps
          , ref <- S.toList (poInRefs op `S.difference` vectorReadRefs (poDag op))
          ]
        unitTy = ProdTy []
    loaded <- forM readKeys $ \(scalar, ref) -> do
      loadV <- gensym "simd_load"
      bumpIn <- gensym "simd_bump_in"
      let lanes = vectorLanes intBytes scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          bytes = fromIntegral (vectorBytes intBytes scalar)
      pure ( ((scalar, ref), loadV)
           , [ (loadV, [], vecTy, Ext (L3.VecLoad scalar lanes ref))
             , (bumpIn, [], unitTy, Ext (L3.BumpCursorMutable ref (LitE bytes)))
             ]
           )
    skipped <- forM skipKeys $ \(scalar, ref) -> do
      bumpIn <- gensym "simd_skip_in"
      let bytes = fromIntegral (vectorBytes intBytes scalar)
      pure (bumpIn, [], unitTy, Ext (L3.BumpCursorMutable ref (LitE bytes)))
    let loadEnv = M.fromList (map fst loaded)
        loadBinds = concatMap snd loaded
    opBinds <- forM groupOps $ \PreparedSimdOp{poScalar, poOutRef, poDag} -> do
      storeU <- gensym "simd_store"
      bumpOut <- gensym "simd_bump_out"
      (dagBinds, resultV) <- emitVectorDag intBytes poScalar loadEnv poDag
      let lanes = vectorLanes intBytes poScalar
          bytes = fromIntegral (vectorBytes intBytes poScalar)
      pure $ dagBinds ++
        [ (storeU, [], unitTy, Ext (L3.VecStore poScalar lanes poOutRef (VarE resultV)))
        , (bumpOut, [], unitTy, Ext (L3.BumpCursorMutable poOutRef (LitE bytes)))
        ]
    pure $ loadBinds ++ skipped ++ concat opBinds
  pure $ mkLets (concat groups) (MkProdE [])

vectorReadRefs :: VectorDag -> S.Set Var
vectorReadRefs dag =
  case dag of
    VDagRead ref -> S.singleton ref
    VDagInvariant{} -> S.empty
    VDagBin _ a b -> vectorReadRefs a `S.union` vectorReadRefs b
    VDagIf c a b -> vectorCondReadRefs c `S.union` vectorReadRefs a `S.union` vectorReadRefs b

vectorCondReadRefs :: VectorCondDag -> S.Set Var
vectorCondReadRefs cond =
  case cond of
    VCondEq _ a b -> vectorReadRefs a `S.union` vectorReadRefs b

emitVectorDag :: Int -> L3.Scalar -> M.Map (L3.Scalar, Var) Var -> VectorDag -> PassM ([Bind3], Var)
emitVectorDag intBytes scalar loadEnv dag =
  case dag of
    VDagRead ref ->
      pure ([], fromMaybe (error $ "emitVectorDag: missing vector load for " ++ show (scalar, ref))
                          (M.lookup (scalar, ref) loadEnv))
    VDagInvariant v -> pure ([], v)
    VDagBin prim a b -> do
      (ab, av) <- emitVectorDag intBytes scalar loadEnv a
      (bb, bv) <- emitVectorDag intBytes scalar loadEnv b
      out <- gensym "simd_binop"
      let lanes = vectorLanes intBytes scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          rhs = vectorPrimExt scalar lanes prim (VarE av) (VarE bv)
      pure (ab ++ bb ++ [(out, [], vecTy, rhs)], out)
    VDagIf cond thenDag elseDag -> do
      (cb, maskV) <- emitVectorCondDag intBytes loadEnv cond
      (tb, thenV) <- emitVectorDag intBytes scalar loadEnv thenDag
      (eb, elseV) <- emitVectorDag intBytes scalar loadEnv elseDag
      out <- gensym "simd_select"
      let lanes = vectorLanes intBytes scalar
          vecTy = L3.SimdTy (L3.scalarToTy scalar) lanes
          rhs = Ext (L3.VecSelect scalar lanes (VarE maskV) (VarE thenV) (VarE elseV))
      pure (cb ++ tb ++ eb ++ [(out, [], vecTy, rhs)], out)

emitVectorCondDag :: Int -> M.Map (L3.Scalar, Var) Var -> VectorCondDag -> PassM ([Bind3], Var)
emitVectorCondDag intBytes loadEnv cond =
  case cond of
    VCondEq condScalar a b -> do
      (ab, av) <- emitVectorDag intBytes condScalar loadEnv a
      (bb, bv) <- emitVectorDag intBytes condScalar loadEnv b
      out <- gensym "simd_cmp"
      let lanes = vectorLanes intBytes condScalar
          vecTy = L3.SimdTy (L3.scalarToTy condScalar) lanes
          rhs = Ext (L3.VecEq condScalar lanes (VarE av) (VarE bv))
      pure (ab ++ bb ++ [(out, [], vecTy, rhs)], out)

vectorPrimExt :: L3.Scalar -> Int -> Prim L3.Ty3 -> L3.Exp3 -> L3.Exp3 -> L3.Exp3
vectorPrimExt scalar lanes prim a b =
  case prim of
    AddP  -> Ext (L3.VecAdd scalar lanes a b)
    FAddP -> Ext (L3.VecAdd scalar lanes a b)
    SubP  -> Ext (L3.VecSub scalar lanes a b)
    FSubP -> Ext (L3.VecSub scalar lanes a b)
    MulP  -> Ext (L3.VecMul scalar lanes a b)
    FMulP -> Ext (L3.VecMul scalar lanes a b)
    DivP  -> Ext (L3.VecDiv scalar lanes a b)
    FDivP -> Ext (L3.VecDiv scalar lanes a b)
    ModP  -> Ext (L3.VecMod scalar lanes a b)
    _ -> error $ "vectorPrimExt: unsupported vector op " ++ show prim

matchSimdLoop :: Int -> Var -> L3.Exp3 -> Maybe SimdLoop
matchSimdLoop intBytes idx body = do
  binds <- flattenUnitLoopBody body
  let writes = writeScalarBinds binds
  guard (not (null writes))
  ops <- mapM (matchWrite binds idx) writes
  let strides = S.fromList (map (vectorStride intBytes . soScalar) ops)
  guard (S.size strides == 1)
  guard (all (scalarSupported . soScalar) ops)
  guard (all (opHasRequiredBumps intBytes binds) ops)
  guard (loopEffectsSafe intBytes ops binds)
  pure $ SimdLoop ops

writeScalarBinds :: [Bind3] -> [(Int, Bind3)]
writeScalarBinds binds = filter (isWriteScalar . snd) (zip [0..] binds)
  where
    isWriteScalar (_, _, _, Ext (L3.WriteScalar{})) = True
    isWriteScalar _ = False

matchWrite :: [Bind3] -> Var -> (Int, Bind3) -> Maybe SimdOp
matchWrite binds idx (writeIx, (_writeVal, _, _writeTy, Ext (L3.WriteScalar scalar writeCur rhs))) = do
  outRef <- derefSource writeCur binds
  let op = case rhs of
             VarE opVar -> resolveVarRhs binds S.empty opVar
             _ -> rhs
  dag <- matchScalarDag scalar idx binds op
  inRefs <- inputRefsForDag binds writeIx scalar dag
  pure $ SimdOp scalar inRefs outRef dag
matchWrite _ _ _ = Nothing

inputRefsForDag :: [Bind3] -> Int -> L3.Scalar -> ScalarDag -> Maybe (S.Set Var)
inputRefsForDag binds writeIx scalar dag =
  let refs = readRefs dag
  in if S.null refs
     then S.singleton <$> nearestInputRefBefore binds writeIx scalar
     else Just refs

nearestInputRefBefore :: [Bind3] -> Int -> L3.Scalar -> Maybe Var
nearestInputRefBefore binds writeIx scalar =
  listToMaybe
    [ ref
    | (_, _, _, Ext (L3.ReadScalar scalar' cur)) <- reverse (take writeIx binds)
    , scalar == scalar'
    , Just ref <- [derefSource cur binds]
    ]

opHasRequiredBumps :: Int -> [Bind3] -> SimdOp -> Bool
opHasRequiredBumps intBytes binds SimdOp{soScalar, soInRefs, soOutRef} =
  all (\ref -> hasCursorBump intBytes ref soScalar binds) (S.toList soInRefs) &&
  hasCursorBump intBytes soOutRef soScalar binds

loopEffectsSafe :: Int -> [SimdOp] -> [Bind3] -> Bool
loopEffectsSafe intBytes ops binds =
  all safeEffect binds
  where
    expected = expectedBumps intBytes ops
    safeEffect (_, _, _, Ext ext) =
      case ext of
        L3.ReadScalar{} -> True
        L3.DerefMutCursor{} -> True
        L3.WriteScalar{} -> True
        L3.BumpCursorMutable ref (LitE n) -> (ref, fromIntegral n) `elem` expected
        _ -> False
    safeEffect _ = True

expectedBumps :: Int -> [SimdOp] -> [(Var, Int)]
expectedBumps intBytes ops = L.nub $ concatMap opBumps ops
  where
    opBumps SimdOp{soScalar, soInRefs, soOutRef} =
      let bytes = scalarWidthBytes intBytes soScalar
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
  listToMaybe
    [ (bind, scalar, cur, normalize val)
    | bind@(_, _, _, Ext (L3.WriteScalar scalar cur val)) <- bs
    ]

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
    L3.ScalarCountBump _ vs -> S.fromList vs
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
    L3.VecEq _ _ a b -> expVars a `S.union` expVars b
    L3.VecSelect _ _ m a b -> S.unions [expVars m, expVars a, expVars b]
    L3.VecStore _ _ v rhs -> S.insert v (expVars rhs)
    L3.SSPush _ a b _ -> S.fromList [a,b]
    L3.SSPop _ a b -> S.fromList [a,b]
    L3.Assert rhs -> expVars rhs

matchScalarDag :: L3.Scalar -> Var -> [Bind3] -> L3.Exp3 -> Maybe ScalarDag
matchScalarDag scalar idx binds expr0 =
  case expr0 of
    VarE v ->
      case resolveVarRhs binds S.empty v of
        VarE v' | v == v' -> matchNonVar expr0
        rhs -> matchScalarDag scalar idx binds rhs
    _ -> matchNonVar expr0
  where
    matchNonVar expr =
      case readValueInputRef scalar binds expr of
        Just ref -> Just (DagRead ref)
        Nothing
          | isLoopInvariantScalarExpr scalar idx binds expr -> Just (DagInvariant expr)
        Nothing ->
          case expr of
            PrimAppE prim [a, b]
              | simdPrimSupported scalar prim ->
                  DagBin prim <$> matchScalarDag scalar idx binds a <*> matchScalarDag scalar idx binds b
            IfE tst thenExp elseExp ->
              DagIf <$> matchCondDag scalar idx binds tst
                    <*> matchScalarDag scalar idx binds thenExp
                    <*> matchScalarDag scalar idx binds elseExp
            _ -> Nothing

matchCondDag :: L3.Scalar -> Var -> [Bind3] -> L3.Exp3 -> Maybe CondDag
matchCondDag _resultScalar idx binds expr0 =
  case expr0 of
    VarE v ->
      case resolveVarRhs binds S.empty v of
        VarE v' | v == v' -> matchNonVar expr0
        rhs -> matchCondDag L3.IntS idx binds rhs
    _ -> matchNonVar expr0
  where
    matchNonVar expr =
      case expr of
        PrimAppE EqIntP [a, b] ->
          CondEq L3.IntS <$> matchScalarDag L3.IntS idx binds a <*> matchScalarDag L3.IntS idx binds b
        PrimAppE EqFloatP [a, b] ->
          CondEq L3.FloatS <$> matchScalarDag L3.FloatS idx binds a <*> matchScalarDag L3.FloatS idx binds b
        _ -> Nothing

nonEmptyReadRefs :: ScalarDag -> Maybe (S.Set Var)
nonEmptyReadRefs dag =
  let refs = readRefs dag
  in if S.null refs then Nothing else Just refs

readRefs :: ScalarDag -> S.Set Var
readRefs dag =
  case dag of
    DagRead ref -> S.singleton ref
    DagInvariant{} -> S.empty
    DagBin _ a b -> readRefs a `S.union` readRefs b
    DagIf c a b -> condReadRefs c `S.union` readRefs a `S.union` readRefs b

condReadRefs :: CondDag -> S.Set Var
condReadRefs cond =
  case cond of
    CondEq _ a b -> readRefs a `S.union` readRefs b

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

isLoopInvariantScalarExpr :: L3.Scalar -> Var -> [Bind3] -> L3.Exp3 -> Bool
isLoopInvariantScalarExpr _scalar idx binds expr =
  idx `S.notMember` gFreeVars expr &&
  isSimpleScalarExpr expr &&
  not (exprContainsAnyRead binds expr)

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

isSimpleScalarExpr :: L3.Exp3 -> Bool
isSimpleScalarExpr expr =
  case expr of
    VarE{} -> True
    LitE{} -> True
    CharE{} -> True
    FloatE{} -> True
    LitSymE{} -> True
    PrimAppE p args
      | p `elem` [AddP, SubP, MulP, DivP, ModP, FAddP, FSubP, FMulP, FDivP] ->
          all isSimpleScalarExpr args
    _ -> False

simdPrimSupported :: L3.Scalar -> Prim L3.Ty3 -> Bool
simdPrimSupported scalar prim =
  case scalar of
    L3.FloatS -> prim `elem` [FAddP, FSubP, FMulP, FDivP]
    L3.IntS -> prim `elem` [AddP, SubP, MulP, DivP, ModP]
    L3.SymS -> prim `elem` [AddP, SubP]
    L3.CharS -> prim `elem` [AddP, SubP]
    L3.BoolS -> prim `elem` [AddP, SubP]

resolveVarRhs :: [Bind3] -> S.Set Var -> Var -> L3.Exp3
resolveVarRhs binds seen v
  | v `S.member` seen = VarE v
  | otherwise =
      case lookupBind v binds of
        VarE v'
          | v' /= v -> resolveVarRhs binds (S.insert v seen) v'
        rhs -> rhs

hasCursorBump :: Int -> Var -> L3.Scalar -> [Bind3] -> Bool
hasCursorBump intBytes ref scalar binds =
  any matches binds
  where
    bytes = scalarWidthBytes intBytes scalar
    matches (_, _, _, Ext (L3.BumpCursorMutable ref' (LitE n))) = ref == ref' && n == fromIntegral bytes
    matches _ = False

scalarSupported :: L3.Scalar -> Bool
scalarSupported s = s `elem` [L3.IntS, L3.SymS, L3.FloatS, L3.CharS, L3.BoolS]

-- | The logical unroll stride for the first prototype.  Int/Sym are 64-bit, so
-- SSE2 handles this as two 2-lane vector operations.  Float uses one 4-lane SSE
-- operation.  A future AVX2 backend can raise this to eight 32-bit lanes or four
-- 64-bit lanes by changing this layer and the backend lowering together.
vectorStride :: Int -> L3.Scalar -> Int
vectorStride _ L3.CharS = 16
vectorStride _ L3.BoolS = 16
vectorStride _ _ = 4

vectorLanes :: Int -> L3.Scalar -> Int
vectorLanes _ L3.FloatS = 4
vectorLanes _ L3.CharS = 16
vectorLanes _ L3.BoolS = 16
vectorLanes intBytes L3.IntS = if intBytes == 4 then 4 else 2
vectorLanes _ _ = 2

vectorGroups :: Int -> L3.Scalar -> Int
vectorGroups intBytes scalar = vectorStride intBytes scalar `div` vectorLanes intBytes scalar

vectorBytes :: Int -> L3.Scalar -> Int
vectorBytes intBytes scalar = vectorLanes intBytes scalar * scalarWidthBytes intBytes scalar

scalarWidthBytes :: Int -> L3.Scalar -> Int
scalarWidthBytes intBytes L3.IntS = intBytes
scalarWidthBytes _ L3.SymS = 8
scalarWidthBytes _ L3.FloatS = 4
scalarWidthBytes _ L3.CharS = 1
scalarWidthBytes _ L3.BoolS = 1

unLets3 :: L3.Exp3 -> ([Bind3], L3.Exp3)
unLets3 (LetE b bod) =
  let (bs, tailExp) = unLets3 bod
  in (b:bs, tailExp)
unLets3 e = ([], e)

infixl 3 <|>
(<|>) :: Maybe a -> Maybe a -> Maybe a
Just x <|> _ = Just x
Nothing <|> y = y
