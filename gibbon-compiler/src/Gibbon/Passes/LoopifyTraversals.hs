-- | Conservative loopification for `OPT:CanVectorize` traversals over
-- fully-factored SoA layouts.
--
-- This pass is intentionally a structural nano-pass: it only removes
-- recursion after it can extract a simple, buffer-local plan from the
-- cursorized L3 body.  When any invariant below is not satisfied, the function
-- is left unchanged.
--
-- Candidate invariants:
--
-- * The pass is active only when `--enable-loopification` and `--store-scalar-field-counts` are enabled.
--   For SoA, loop bounds come from scalar-count footer metadata, so loopification is
--   not meaningful without that runtime metadata.  This pass deliberately
--   emits the unfused per-buffer loop form.  The compiler pipeline runs
--   selective buffer sharing next, and then a separate post-selective loop
--   fusion nano-pass fuses the remaining non-shared loops.
--
-- * The function must be annotated with `OPT:CanVectorize`, or the compiler
--   must be run with `--auto-loopification`.  In automatic mode, the same
--   structural extractor and parent-child dependency check decide whether the
--   function is actually rewritten.  The packed
--   datatype mentioned by its case expression must use a fully-factored SoA
--   layout.  Buffer 0 is the dcon/tag stream; scalar buffers are assigned by
--   walking constructor fields in `DDef` order and skipping packed recursive
--   fields.
--   Automatic mode deliberately ignores compiler-generated packed helpers such
--   as `_copy_*`, `_print_*`, `_traverse_*`, and `_unpack_*`: those functions
--   are infrastructure, not user map traversals, and rewriting them can perturb
--   consumers that rely on their precise packed-walk behavior.
--
-- * The annotation is treated as the user's semantic promise that recursive
--   calls are independent.  The pass still has a syntactic safety check:
--   if a value derived from a self-call is used by a parent scalar write,
--   tag write, case scrutinee, or conditional, loopification is rejected.
--   In other words, true parent-child dependencies must remain recursive.
--
-- * The cursor ABI is inferred from the function arguments, not from fixed
--   positions.  The accepted ABI has four cursor arrays of the expected SoA
--   length: input ends, output ends, output cursors, and input cursors.  Extra
--   non-cursor-array arguments are treated as loop-invariant scalar values and
--   may appear in scalar update expressions.
--
-- Scalar-plan invariants:
--
-- * Each constructor branch may write each scalar output buffer at most once.
--   The write must target the scalar buffer associated with that constructor
--   and field, and the written scalar type must match the field type.
--
-- * A scalar update expression must be pure and may mention only scalar reads
--   from the same constructor instance or loop-invariant scalar arguments.
--   Cross-constructor scalar dependencies are rejected because independent
--   buffer walks cannot preserve constructor control flow.
--
-- * Unmentioned scalar buffers are identity-copied.  This keeps the
--   transformation structure-preserving before the later selective-buffer
--   sharing pass decides which unchanged buffers can be shared.
--
-- * A scalar-valued conditional is supported only when both branches write the
--   same set of constructor/field buffers.  The condition must satisfy the same
--   dependency rule as normal scalar expressions.  Code generation emits this
--   as unit-valued control flow inside the loop (`if ... write ... else write
--   ...`) because `ForE` and `WhileCursor` loop bodies lower as unit tails.
--
-- Chunk/footer invariants:
--
-- * This pass emits one outer chunk loop and one inner counted `ForE` per
--   homogeneous buffer.  The first chunk's count is read from the
--   end-of-region footer; later chunk counts are read from the footer reached
--   at the preceding redirection boundary.  This matches the cyclic
--   next-chunk-count encoding in the RTS.  The later
--   `LoopifiedTraversalFusion` pass may fuse remaining scalar-buffer loops for
--   fields of the same constructor after selective sharing has removed copied
--   buffers.
--
-- * The dcon stream is copied by reading tags from the input tag buffer and
--   writing the same tags to the output.  The pass does not synthesize
--   constructor tags from assumptions about lists, trees, or constructor order.
--
-- * If a scalar update for one buffer depends on another scalar buffer, the
--   dependency gets its own cursor anchored at the original input cursor array.
--   That dependency cursor is advanced in lock-step with the consumer buffer,
--   including across chunk redirection boundaries.  It must not reuse the main
--   cursor for the dependency buffer, because that main cursor may have already
--   been consumed by the dependency buffer's own loop.
--
-- * A loopified map is also a builder for a fresh packed output value.  It must
--   therefore populate scalar-count metadata for every output buffer,
--   including the dcon stream.  Because maps preserve shape, output chunk
--   counts are identical to input chunk counts.  The pass sets the output
--   footer count once per chunk rather than bumping once per written element.
--   Without this metadata, a later loopified map over the output would read
--   stale or zero footer counts.
--
-- Current limitations:
--
-- * This pass only emits scalar loops; explicit SIMD/vector IR is a later
--   `VectorizeTraversals` concern.
--
-- * The accepted scalar language is deliberately small: variables, literals,
--   projections, primitive scalar operations, and the conditional shape
--   described above.  Unsupported effects or non-scalar fields cause the pass
--   to leave the function recursive.
module Gibbon.Passes.LoopifyTraversals
  ( loopifyTraversals
  , LoopifyCandidate(..)
  , TraversalPlan(..)
  , ScalarBufferPlan(..)
  , loopifyCandidateInfo
  , loopifyCandidateInfoWith
  , collectMentionedDataCons
  , hasParentChildDependency
  ) where

import Control.Monad (foldM)
import Data.Char (isAlphaNum)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L3.Syntax

data LoopifyCandidate = LoopifyCandidate
  { lcFunName :: Var
  , lcTyCon :: TyCon
  , lcDataCons :: [DataCon]
  }
  deriving (Eq, Ord, Show)

data TraversalPlan = TraversalPlan
  { tpABI :: LoopifyABI
  , tpScalarPlans :: [ScalarBufferPlan]
  }
  deriving (Eq, Ord, Show)

data ScalarBufferSpec = ScalarBufferSpec
  { sbsBufIx :: Int
  , sbsDCon :: DataCon
  , sbsFieldIdx :: Int
  , sbsTy :: Ty3
  }
  deriving (Eq, Ord, Show)

data ScalarBufferPlan = ScalarBufferPlan
  { sbpBufIx :: Int
  , sbpDCon :: DataCon
  , sbpFieldIdx :: Int
  , sbpTy :: Ty3
  , sbpScalar :: Scalar
  , sbpOp :: ScalarBufferOp
  }
  deriving (Eq, Ord, Show)

data ScalarBufferOp
  = ScalarCopy
  | ScalarExpr Exp3 (M.Map Var ScalarInputInfo)
  deriving (Eq, Ord, Show)

data BufferRole
  = InputBuf Int
  | OutputBuf Int
  deriving (Eq, Ord, Show)

data ScalarInputInfo = ScalarInputInfo
  { siiScalar :: Scalar
  , siiBufIx :: Int
  }
  deriving (Eq, Ord, Show)

data LoopifyABI = LoopifyABI
  { abiArrLen :: Int
  , abiInEnds :: Var
  , abiOutEnds :: Var
  , abiOutCurs :: Var
  , abiInCurs :: Var
  , abiLoopInvariantArgs :: S.Set Var
  }
  deriving (Eq, Ord, Show)

newtype LoopNameSeed = LoopNameSeed
  { loopNameSeedPrefix :: Var
  }
  deriving (Eq, Ord, Show)

freshLoopNameSeed :: Bool -> PassM LoopNameSeed
freshLoopNameSeed isMutable =
  LoopNameSeed <$> gensym (if isMutable then "loop_mut" else "loop")

loopName :: LoopNameSeed -> String -> Var
loopName LoopNameSeed{loopNameSeedPrefix} s =
  loopNameSeedPrefix `varAppend` "_" `varAppend` toVar s

loopBufferName :: LoopNameSeed -> Int -> String -> Var
loopBufferName LoopNameSeed{loopNameSeedPrefix} ix s =
  loopNameSeedPrefix
    `varAppend` "_buf"
    `varAppend` toVar (show ix)
    `varAppend` "_"
    `varAppend` toVar s

sanitizeLoopName :: String -> String
sanitizeLoopName =
  map (\c -> if isAlphaNum c then c else '_')

loopifyTraversals :: Prog3 -> PassM Prog3
loopifyTraversals prog@Prog{ddefs, fundefs} = do
  dflags <- getDynFlags
  let enabled =
        gopt Opt_StoreScalarFieldCounts dflags &&
        gopt Opt_EnableLoopification dflags
      auto = gopt Opt_AutoLoopification dflags
  fds' <-
    if enabled
    then mapM (rewriteFun False auto ddefs) (M.elems fundefs)
    else pure (M.elems fundefs)
  pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

rewriteFun :: Bool -> Bool -> DDefs Ty3 -> FunDef3 -> PassM FunDef3
rewriteFun fuseScalarLoops auto ddefs fn =
  case loopifyCandidateInfoWith auto ddefs fn of
    Nothing -> pure fn
    Just cand ->
      case extractTraversalPlan ddefs cand fn of
        Nothing -> pure fn
        Just plan -> do
          mbody <- loopifyFastPath fuseScalarLoops plan fn
          case mbody of
            Nothing -> pure fn
            Just body' -> pure $ stampCanVectorize (fn { funBody = body' })

loopifyCandidateInfo :: DDefs Ty3 -> FunDef3 -> Maybe LoopifyCandidate
loopifyCandidateInfo = loopifyCandidateInfoWith False

loopifyCandidateInfoWith :: Bool -> DDefs Ty3 -> FunDef3 -> Maybe LoopifyCandidate
loopifyCandidateInfoWith allowInferred ddefs FunDef{funName, funMeta, funBody}
  | not explicitlyAnnotated && not canInfer = Nothing
  | otherwise =
      let dcons = L.nub (collectMentionedDataCons funBody)
          tycons = L.nub (map (getTyOfDataCon ddefs) dcons)
       in case tycons of
            [tycon]
              | memLayout (lookupDDef ddefs tycon) == FullyFactored ->
                  Just LoopifyCandidate
                    { lcFunName = funName
                    , lcTyCon = tycon
                    , lcDataCons = dcons
                    }
            _ -> Nothing
  where
    explicitlyAnnotated = CanVectorize `elem` funOpt funMeta
    canInfer = allowInferred && not (isGeneratedPackedHelper funName)

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

extractTraversalPlan :: DDefs Ty3 -> LoopifyCandidate -> FunDef3 -> Maybe TraversalPlan
extractTraversalPlan ddefs LoopifyCandidate{lcFunName, lcTyCon} FunDef{funArgs, funBody, funTy = (ins, _)} = do
  if hasParentChildDependency lcFunName funBody
    then Nothing
    else pure ()
  specs <- scalarBufferSpecs ddefs lcTyCon
  case specs of
    [] -> Nothing
    _ -> pure ()
  (preBinds, _scrt, branches) <- splitTopCase funBody
  let expectedArrLen = 1 + length specs
      candidates = loopifyABICandidates expectedArrLen (collectVars funBody) funArgs ins
  listToMaybe $ mapMaybe (extractWithABI specs preBinds branches) candidates

extractWithABI
  :: [ScalarBufferSpec]
  -> [(Var, [()], Ty3, Exp3)]
  -> [(DataCon, [(Var, ())], Exp3)]
  -> LoopifyABI
  -> Maybe TraversalPlan
extractWithABI specs preBinds branches abi@LoopifyABI{abiOutCurs, abiInCurs, abiLoopInvariantArgs} = do
  let baseInputArrays = extendCursorArrayAliases (S.singleton abiInCurs) preBinds
      baseOutputArrays = extendCursorArrayAliases (S.singleton abiOutCurs) preBinds
      baseRoles = collectCursorRolesFrom M.empty baseInputArrays baseOutputArrays preBinds
  branchPlanMaps <- mapM (extractBranchPlans specs abiLoopInvariantArgs baseInputArrays baseOutputArrays baseRoles) branches
  merged <- mergeBranchPlanMaps branchPlanMaps
  if M.null merged
    then Nothing
    else pure ()
  let plans = map (\spec -> fromMaybe (identityPlan spec) (M.lookup (sbsBufIx spec) merged)) specs
  pure $ TraversalPlan { tpABI = abi, tpScalarPlans = L.sortOn sbpBufIx plans }

loopifyABICandidates :: Int -> S.Set Var -> [Var] -> [Ty3] -> [LoopifyABI]
loopifyABICandidates expectedArrLen usedVars args tys =
  let typedArgs = zip args tys
      cursorArrays =
        [ (pos, v)
        | (pos, (v, CursorArrayTy n)) <- zip [0 :: Int ..] typedArgs
        , n == expectedArrLen
        ]
      invariants =
        [ v
        | (v, ty) <- typedArgs
        , not (isCursorArrayTy ty)
        ]
      candidates =
        [ (candidateScore poss, abi)
        | inEnds@(posInEnds, _) <- cursorArrays
        , outEnds@(posOutEnds, _) <- cursorArrays
        , outCurs@(posOutCurs, _) <- cursorArrays
        , inCurs@(posInCurs, _) <- cursorArrays
        , snd outCurs `S.member` usedVars
        , snd inCurs `S.member` usedVars
        , let vars = map snd [inEnds, outEnds, outCurs, inCurs]
              poss = [posInEnds, posOutEnds, posOutCurs, posInCurs]
        , length (L.nub vars) == 4
        , let abi =
                LoopifyABI
                  { abiArrLen = expectedArrLen
                  , abiInEnds = snd inEnds
                  , abiOutEnds = snd outEnds
                  , abiOutCurs = snd outCurs
                  , abiInCurs = snd inCurs
                  , abiLoopInvariantArgs = S.fromList invariants
                  }
        ]
   in map snd (L.sortOn fst candidates)
  where
    isCursorArrayTy ty =
      case ty of
        CursorArrayTy{} -> True
        _ -> False

    candidateScore :: [Int] -> (Int, Int)
    candidateScore ps =
      ( roleOrderInversions ps
      , sum ps
      )

    roleOrderInversions :: [Int] -> Int
    roleOrderInversions ps =
      length
        [ ()
        | (i, p1) <- zip [0 :: Int ..] ps
        , (j, p2) <- zip [0 :: Int ..] ps
        , i < j
        , p1 > p2
        ]

collectVars :: Exp3 -> S.Set Var
collectVars ex =
  case ex of
    VarE v -> S.singleton v
    LitE{} -> S.empty
    CharE{} -> S.empty
    FloatE{} -> S.empty
    LitSymE{} -> S.empty
    AppE _ _ _ args -> S.unions (map collectVars args)
    PrimAppE _ args -> S.unions (map collectVars args)
    LetE (v, _, _, rhs) bod ->
      S.insert v (collectVars rhs `S.union` collectVars bod)
    IfE a b c ->
      S.unions [collectVars a, collectVars b, collectVars c]
    MkProdE ls -> S.unions (map collectVars ls)
    ProjE _ e -> collectVars e
    CaseE scrt brs ->
      collectVars scrt
        `S.union` S.unions [ S.fromList (map fst vars) `S.union` collectVars rhs
                            | (_, vars, rhs) <- brs
                            ]
    DataConE _ _ args -> S.unions (map collectVars args)
    TimeIt e _ _ -> collectVars e
    WithArenaE _ e -> collectVars e
    SpawnE _ _ args -> S.unions (map collectVars args)
    SyncE -> S.empty
    MapE (v, _, e1) e2 ->
      S.insert v (collectVars e1 `S.union` collectVars e2)
    FoldE (v1, _, e1) (v2, _, e2) e3 ->
      S.insert v1 (S.insert v2 (S.unions [collectVars e1, collectVars e2, collectVars e3]))
    Ext ext ->
      collectExtVars ext

collectExtVars :: E3Ext () Ty3 -> S.Set Var
collectExtVars ext =
  case ext of
    ReadScalar _ cur -> S.singleton cur
    WriteScalar _ cur rhs -> S.insert cur (collectVars rhs)
    ReadTag cur -> S.singleton cur
    WriteTag _ cur -> S.singleton cur
    WriteTagPacked cur rhs -> S.insert cur (collectVars rhs)
    TagCursor cur tag -> S.fromList [cur, tag]
    WriteCursorIndirection cur target end -> S.fromList [cur, target, end]
    WriteCursorSelectiveIndirection cur target end mask ->
      S.fromList [cur, target, end] `S.union` collectVars mask
    UnwrapSelectiveIndirections _ ends curs -> S.fromList [ends, curs]
    WriteTaggedCursor cur rhs -> S.insert cur (collectVars rhs)
    MemCpy src dst _ -> S.fromList [src, dst]
    ReadTaggedCursor cur -> S.singleton cur
    ReadCursor cur -> S.singleton cur
    GrowRegion cur end -> S.fromList [cur, end]
    WriteCursorMutable cur rhs -> S.insert cur (collectVars rhs)
    ReadList cur _ -> S.singleton cur
    WriteList cur rhs _ -> S.insert cur (collectVars rhs)
    ReadVector cur _ -> S.singleton cur
    WriteVector cur rhs _ -> S.insert cur (collectVars rhs)
    MakeCursorArray _ vars -> S.fromList vars
    IndexCursorArray arr _ -> S.singleton arr
    AddCursor cur rhs -> S.insert cur (collectVars rhs)
    BumpCursorMutable cur rhs -> S.insert cur (collectVars rhs)
    AddrOfCursor rhs -> collectVars rhs
    DerefMutCursor cur -> S.singleton cur
    CastPtr cur _ -> S.singleton cur
    SubPtr cur1 cur2 -> S.fromList [cur1, cur2]
    NewBuffer{} -> S.empty
    ScopedBuffer{} -> S.empty
    NewParBuffer{} -> S.empty
    ScopedParBuffer{} -> S.empty
    EndOfBuffer{} -> S.empty
    MMapFileSize cur -> S.singleton cur
    SizeOfPacked cur1 cur2 -> S.fromList [cur1, cur2]
    SizeOfScalar cur -> S.singleton cur
    BoundsCheck _ end cur mb _ ->
      S.fromList [end, cur] `S.union`
        maybe S.empty (\(end', cur') -> S.fromList [end', cur']) mb
    BoundsCheckVector checks ->
      S.unions
        [ S.fromList [endVar, curVar, endVar', curVar']
        | (_, endVar, curVar, (endVar', curVar')) <- checks
        ]
    IndirectionBarrier _ (l1, r1, l2, r2) -> S.fromList [l1, r1, l2, r2]
    BumpArenaRefCount arena end -> S.fromList [arena, end]
    NullCursor -> S.empty
    InitCursor{} -> S.empty
    RetE ls -> S.unions (map collectVars ls)
    GetCilkWorkerNum -> S.empty
    LetAvail _ bod -> collectVars bod
    AllocateTagHere cur _ -> S.singleton cur
    AllocateScalarsHere cur -> S.singleton cur
    StartTagAllocation cur -> S.singleton cur
    EndTagAllocation cur -> S.singleton cur
    StartScalarsAllocation cur -> S.singleton cur
    EndScalarsAllocation cur -> S.singleton cur
    ScalarCountBump _ curs -> S.fromList curs
    ScalarCountSet footer count -> S.fromList [footer, count]
    ScalarCountCopyAll _ dstEnds srcEnds -> S.fromList [dstEnds, srcEnds]
    ReadScalarCount cur -> S.singleton cur
    ReadScalarCountFirstFooter cur -> S.singleton cur
    ReadScalarCountNextFooter cur -> S.singleton cur
    ForE v bound bod -> S.insert v (collectVars bound `S.union` collectVars bod)
    WhileCursor cur bod -> S.insert cur (collectVars bod)
    WhileCursorEnd cur end bod -> S.insert cur (S.insert end (collectVars bod))
    VecBroadcast _ _ val -> collectVars val
    VecLoad _ _ ref -> S.singleton ref
    VecAdd _ _ a b -> collectVars a `S.union` collectVars b
    VecSub _ _ a b -> collectVars a `S.union` collectVars b
    VecMul _ _ a b -> collectVars a `S.union` collectVars b
    VecDiv _ _ a b -> collectVars a `S.union` collectVars b
    VecMod _ _ a b -> collectVars a `S.union` collectVars b
    VecEq _ _ a b -> collectVars a `S.union` collectVars b
    VecSelect _ _ m a b -> S.unions [collectVars m, collectVars a, collectVars b]
    VecStore _ _ ref val -> S.insert ref (collectVars val)
    SSPush _ a b _ -> S.fromList [a, b]
    SSPop _ a b -> S.fromList [a, b]
    Assert rhs -> collectVars rhs

identityPlan :: ScalarBufferSpec -> ScalarBufferPlan
identityPlan ScalarBufferSpec{sbsBufIx, sbsDCon, sbsFieldIdx, sbsTy} =
  ScalarBufferPlan
    { sbpBufIx = sbsBufIx
    , sbpDCon = sbsDCon
    , sbpFieldIdx = sbsFieldIdx
    , sbpTy = sbsTy
    , sbpScalar = mkScalar sbsTy
    , sbpOp = ScalarCopy
    }

scalarBufferSpecs :: DDefs Ty3 -> TyCon -> Maybe [ScalarBufferSpec]
scalarBufferSpecs ddefs tycon =
  snd <$> foldM stepCtor (1, []) userDataCons
  where
    ddef = lookupDDef ddefs tycon
    userDataCons =
      filter
        (\(dcon, _) -> not (isIndirectionTag dcon || isRedirectionTag dcon))
        (dataCons ddef)

    stepCtor :: (Int, [ScalarBufferSpec]) -> (DataCon, [(Bool, Ty3)]) -> Maybe (Int, [ScalarBufferSpec])
    stepCtor (nextIx, acc) (dcon, fields) =
      foldM (stepField dcon) (nextIx, acc) (zip [0..] (map snd fields))

    stepField :: DataCon -> (Int, [ScalarBufferSpec]) -> (Int, Ty3) -> Maybe (Int, [ScalarBufferSpec])
    stepField dcon (nextIx, acc) (fieldIx, ty)
      | isPackedTy ty = pure (nextIx, acc)
      | isScalarTy ty =
          pure
            ( nextIx + 1
            , acc ++ [ScalarBufferSpec nextIx dcon fieldIx ty]
            )
      | otherwise = Nothing

splitTopCase :: Exp3 -> Maybe ([(Var, [()], Ty3, Exp3)], Exp3, [(DataCon, [(Var, ())], Exp3)])
splitTopCase = go []
  where
    go acc ex =
      case ex of
        LetE b bod -> go (acc ++ [b]) bod
        CaseE scrt brs -> Just (acc, scrt, brs)
        _ -> Nothing

collectCursorRoles :: Var -> Var -> [(Var, [()], Ty3, Exp3)] -> M.Map Var BufferRole
collectCursorRoles inCurs outCurs binds =
  let inputArrays = extendCursorArrayAliases (S.singleton inCurs) binds
      outputArrays = extendCursorArrayAliases (S.singleton outCurs) binds
   in collectCursorRolesFrom M.empty inputArrays outputArrays binds

collectCursorRolesFrom :: M.Map Var BufferRole -> S.Set Var -> S.Set Var -> [(Var, [()], Ty3, Exp3)] -> M.Map Var BufferRole
collectCursorRolesFrom env0 inputArrays outputArrays = foldl step env0
  where
    step env (v, _, _, rhs) =
      let env' = collectNestedRoles env rhs
       in case rhsRole env' rhs of
            Just role -> M.insert v role env'
            Nothing -> env'

    rhsRole env rhs =
      case rhs of
        VarE v -> M.lookup v env
        Ext (IndexCursorArray arr ix)
          | arr `S.member` inputArrays -> Just (InputBuf ix)
          | arr `S.member` outputArrays -> Just (OutputBuf ix)
        Ext (AddrOfCursor inner) -> rhsRole env inner
        Ext (DerefMutCursor ref) -> M.lookup ref env
        Ext (AddCursor cur _) -> M.lookup cur env
        _ -> Nothing

    collectNestedRoles env ex =
      case ex of
        LetE (v, _, _, rhs1) bod ->
          let env1 = collectNestedRoles env rhs1
              env2 =
                case rhsRole env1 rhs1 of
                  Just role -> M.insert v role env1
                  Nothing -> env1
           in collectNestedRoles env2 bod
        IfE a b c ->
          let env1 = collectNestedRoles env a
              env2 = collectNestedRoles env1 b
           in collectNestedRoles env2 c
        MkProdE ls ->
          foldl collectNestedRoles env ls
        ProjE _ e ->
          collectNestedRoles env e
        PrimAppE _ args ->
          foldl collectNestedRoles env args
        AppE _ _ _ args ->
          foldl collectNestedRoles env args
        CaseE scrt brs ->
          let env1 = collectNestedRoles env scrt
           in foldl (\acc (_, _, rhs1) -> collectNestedRoles acc rhs1) env1 brs
        DataConE _ _ args ->
          foldl collectNestedRoles env args
        TimeIt e _ _ ->
          collectNestedRoles env e
        WithArenaE _ e ->
          collectNestedRoles env e
        SpawnE _ _ args ->
          foldl collectNestedRoles env args
        MapE (_, _, e1) e2 ->
          collectNestedRoles (collectNestedRoles env e1) e2
        FoldE (_, _, e1) (_, _, e2) e3 ->
          collectNestedRoles (collectNestedRoles (collectNestedRoles env e1) e2) e3
        Ext (LetAvail _ bod) ->
          collectNestedRoles env bod
        Ext (WriteScalar _ _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteTaggedCursor _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteCursorMutable _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteList _ rhs1 _) ->
          collectNestedRoles env rhs1
        Ext (WriteVector _ rhs1 _) ->
          collectNestedRoles env rhs1
        Ext (AddCursor _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (BumpCursorMutable _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (AddrOfCursor rhs1) ->
          collectNestedRoles env rhs1
        Ext (Assert rhs1) ->
          collectNestedRoles env rhs1
        _ -> env

extendCursorArrayAliases :: S.Set Var -> [(Var, [()], Ty3, Exp3)] -> S.Set Var
extendCursorArrayAliases seed binds = foldl step seed binds
  where
    step aliases (v, _, _, rhs) =
      case rhs of
        VarE src
          | src `S.member` aliases -> S.insert v aliases
        _ -> aliases

extractBranchPlans
  :: [ScalarBufferSpec]
  -> S.Set Var
  -> S.Set Var
  -> S.Set Var
  -> M.Map Var BufferRole
  -> (DataCon, [(Var, ())], Exp3)
  -> Maybe (M.Map Int ScalarBufferPlan)
extractBranchPlans specs loopInvariantArgs baseInputArrays baseOutputArrays baseRoles (branchDCon, _, rhs) = do
  let binds = collectAllLets rhs
      inputArrays = extendCursorArrayAliases baseInputArrays binds
      outputArrays = extendCursorArrayAliases baseOutputArrays binds
      roles = collectCursorRolesFrom baseRoles inputArrays outputArrays binds
      scalarInputs = collectScalarInputsWithRoles roles binds
      pureEnv = collectPureBindings scalarInputs binds
      specByBuf = M.fromList [ (sbsBufIx spec, spec) | spec <- specs ]

  extractPlansFromExpr roles scalarInputs pureEnv specByBuf rhs
  where
    -- A constructor branch is converted into a map from scalar buffer index to
    -- the operation that should run for each element in that homogeneous
    -- buffer.  For normal branches this is just the set of scalar writes found
    -- in the branch.  For an `if`, both arms must write the same target
    -- buffers; the branch-level conditional is then retained as a scalar
    -- expression and later emitted as unit-valued write control flow in the
    -- inner loop.
    extractPlansFromExpr roles scalarInputs pureEnv specByBuf ex =
      case stripLeadingLets ex of
        IfE cond thn els -> do
          let cond' = normalizePureExpr pureEnv cond
              condFvs = S.toList (gFreeVars cond')
          if not (all (\v -> M.member v scalarInputs || v `S.member` loopInvariantArgs) condFvs)
            then Nothing
            else pure ()
          let condDeps = M.restrictKeys scalarInputs (S.fromList condFvs)
          validateScalarDeps specByBuf branchDCon condDeps
          thnPlans <- extractFlatPlans roles scalarInputs pureEnv specByBuf thn
          elsPlans <- extractFlatPlans roles scalarInputs pureEnv specByBuf els
          mergeConditionalPlanMaps scalarInputs cond' condDeps thnPlans elsPlans
        _ ->
          extractFlatPlans roles scalarInputs pureEnv specByBuf ex

    extractFlatPlans roles scalarInputs pureEnv specByBuf ex =
      foldM (stepWrite roles scalarInputs pureEnv specByBuf) M.empty (collectAllLets ex)

    -- Only strip leading administrative lets.  Nested lets still participate
    -- in the scalar input/pure binding analysis above.
    stripLeadingLets ex =
      case ex of
        LetE _ bod -> stripLeadingLets bod
        _ -> ex

    -- A scalar write is accepted only when it writes the scalar buffer for the
    -- current constructor field and its RHS mentions only same-constructor
    -- scalar inputs or loop-invariant scalar arguments.  This is the central
    -- "map over a buffer" invariant: no constructor control-flow or child
    -- result is allowed to determine the value being written.
    stepWrite roles scalarInputs pureEnv specByBuf acc (_, _, _, bindRhs) =
      case bindRhs of
        Ext (WriteScalar s outCur rhs0) -> do
          outBufIx <- case M.lookup outCur roles of
                        Just (OutputBuf ix) -> Just ix
                        _ -> Nothing
          spec <- M.lookup outBufIx specByBuf
          if sbsDCon spec /= branchDCon
            then Nothing
            else pure ()
          if scalarToTy s /= sbsTy spec
            then Nothing
            else pure ()
          if M.member outBufIx acc
            then Nothing
            else pure ()
          let rhs' = normalizePureExpr pureEnv rhs0
              fvs = S.toList (gFreeVars rhs')
          if not (all (\v -> M.member v scalarInputs || v `S.member` loopInvariantArgs) fvs)
            then Nothing
            else pure ()
          let deps = M.restrictKeys scalarInputs (S.fromList fvs)
          validateScalarDeps specByBuf branchDCon deps
          pure $
            M.insert
              outBufIx
              ScalarBufferPlan
                { sbpBufIx = outBufIx
                , sbpDCon = branchDCon
                , sbpFieldIdx = sbsFieldIdx spec
                , sbpTy = sbsTy spec
                , sbpScalar = s
                , sbpOp = ScalarExpr rhs' deps
                }
              acc
        _ -> pure acc

    -- Dependencies between scalar buffers are legal only within the same data
    -- constructor.  For example, a field update for `Cell.mom` may depend on
    -- `Cell.s`, but it may not depend on a `Particle` field because the loop
    -- over the `Cell.mom` buffer has no per-element dcon control flow.
    validateScalarDeps specByBuf dcon deps =
      mapM_
        (\info -> do
            depSpec <- M.lookup (siiBufIx info) specByBuf
            if sbsDCon depSpec /= dcon
              then Nothing
              else pure ()
            if scalarToTy (siiScalar info) /= sbsTy depSpec
              then Nothing
              else pure ())
        (M.elems deps)

    -- Conditional scalar updates are accepted only when both arms have the
    -- same write shape.  This lets the later loop body do exactly one write to
    -- the buffer per input element, independent of the branch taken.
    mergeConditionalPlanMaps scalarInputs cond condDeps thnPlans elsPlans = do
      let keys = S.toList (M.keysSet thnPlans `S.union` M.keysSet elsPlans)
      pairs <-
        mapM
          (\ix -> do
              thnPlan <- M.lookup ix thnPlans
              elsPlan <- M.lookup ix elsPlans
              plan <- mergeConditionalPlan scalarInputs cond condDeps thnPlan elsPlan
              pure (ix, plan))
          keys
      pure $ M.fromList pairs

    mergeConditionalPlan scalarInputs cond condDeps thnPlan elsPlan
      | thnPlan == elsPlan = Just thnPlan
      | otherwise = do
          if samePlanTarget thnPlan elsPlan
            then pure ()
            else Nothing
          (thnExpr, thnDeps) <- planAsExpr scalarInputs thnPlan
          (elsExpr, elsDeps) <- planAsExpr scalarInputs elsPlan
          pure $
            thnPlan
              { sbpOp =
                  ScalarExpr
                    (IfE cond thnExpr elsExpr)
                    (M.unions [condDeps, thnDeps, elsDeps])
              }

    samePlanTarget a b =
      sbpBufIx a == sbpBufIx b
        && sbpDCon a == sbpDCon b
        && sbpFieldIdx a == sbpFieldIdx b
        && sbpTy a == sbpTy b
        && sbpScalar a == sbpScalar b

    planAsExpr scalarInputs plan =
      case sbpOp plan of
        ScalarExpr expr deps -> Just (expr, deps)
        ScalarCopy -> do
          (v, info) <-
            listToMaybe
              [ (v, info)
              | (v, info) <- M.toList scalarInputs
              , siiBufIx info == sbpBufIx plan
              ]
          pure (VarE v, M.singleton v info)

mergeBranchPlanMaps :: [M.Map Int ScalarBufferPlan] -> Maybe (M.Map Int ScalarBufferPlan)
mergeBranchPlanMaps =
  foldM
    (\acc mp ->
       foldM
         (\acc' (ix, plan) ->
            case M.lookup ix acc' of
              Nothing -> pure $ M.insert ix plan acc'
              Just plan'
                | plan' == plan -> pure acc'
                | otherwise -> Nothing)
         acc
         (M.toList mp))
    M.empty

loopifyFastPath :: Bool -> TraversalPlan -> FunDef3 -> PassM (Maybe Exp3)
loopifyFastPath fuseScalarLoops TraversalPlan{tpABI = LoopifyABI{abiArrLen, abiInEnds, abiOutEnds, abiOutCurs, abiInCurs}, tpScalarPlans} FunDef{funTy = (_, out)}
  | otherwise =
      if abiArrLen == 1 + length tpScalarPlans
         && out == loopifiedOutTy abiArrLen
      then Just <$> mkFastPathBody fuseScalarLoops abiArrLen abiInEnds abiOutEnds abiOutCurs abiInCurs tpScalarPlans
      else if abiArrLen == 1 + length tpScalarPlans
              && out == ProdTy []
      then Just <$> mkMutableFastPathBody fuseScalarLoops abiArrLen abiInEnds abiOutEnds abiOutCurs abiInCurs tpScalarPlans
      else pure Nothing

loopifiedOutTy :: Int -> Ty3
loopifiedOutTy arr =
  ProdTy
    [ CursorArrayTy arr
    , CursorArrayTy arr
    , CursorArrayTy arr
    , ProdTy [CursorArrayTy arr, CursorArrayTy arr]
    ]

collectLeadingLets :: Exp3 -> [(Var, [()], Ty3, Exp3)]
collectLeadingLets ex =
  case ex of
    LetE b bod -> b : collectLeadingLets bod
    _ -> []

collectAllLets :: Exp3 -> [(Var, [()], Ty3, Exp3)]
collectAllLets ex =
  case ex of
    LetE b@(_, _, _, rhs) bod ->
      b : collectAllLets rhs ++ collectAllLets bod
    IfE a b c ->
      collectAllLets a ++ collectAllLets b ++ collectAllLets c
    MkProdE ls ->
      concatMap collectAllLets ls
    ProjE _ e ->
      collectAllLets e
    PrimAppE _ args ->
      concatMap collectAllLets args
    AppE _ _ _ args ->
      concatMap collectAllLets args
    CaseE scrt brs ->
      collectAllLets scrt ++ concatMap (\(_, _, rhs) -> collectAllLets rhs) brs
    DataConE _ _ args ->
      concatMap collectAllLets args
    TimeIt e _ _ ->
      collectAllLets e
    WithArenaE _ e ->
      collectAllLets e
    SpawnE _ _ args ->
      concatMap collectAllLets args
    MapE (_, _, e1) e2 ->
      collectAllLets e1 ++ collectAllLets e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      collectAllLets e1 ++ collectAllLets e2 ++ collectAllLets e3
    Ext (ForE _ bound body) ->
      collectAllLets bound ++ collectAllLets body
    Ext (WhileCursor _ bod) ->
      collectAllLets bod
    Ext (WhileCursorEnd _ _ bod) ->
      collectAllLets bod
    Ext (WriteScalar _ _ rhs) ->
      collectAllLets rhs
    Ext (WriteTaggedCursor _ rhs) ->
      collectAllLets rhs
    Ext (WriteCursorMutable _ rhs) ->
      collectAllLets rhs
    Ext (WriteList _ rhs _) ->
      collectAllLets rhs
    Ext (WriteVector _ rhs _) ->
      collectAllLets rhs
    Ext (AddCursor _ rhs) ->
      collectAllLets rhs
    Ext (BumpCursorMutable _ rhs) ->
      collectAllLets rhs
    Ext (AddrOfCursor rhs) ->
      collectAllLets rhs
    Ext (LetAvail _ bod) ->
      collectAllLets bod
    Ext (Assert rhs) ->
      collectAllLets rhs
    _ -> []

hasParentChildDependency :: Var -> Exp3 -> Bool
hasParentChildDependency funName body =
  let childVars = childDerivedVars funName body
   in not (S.null childVars)
        && exprHasParentChildUse childVars body

childDerivedVars :: Var -> Exp3 -> S.Set Var
childDerivedVars funName body = fixedPoint S.empty
  where
    binds = collectAllLets body

    fixedPoint seen =
      let seen' = foldl step seen binds
       in if seen' == seen
            then seen
            else fixedPoint seen'

    step seen (v, _, _, rhs)
      | isSelfCall rhs = S.insert v seen
      | exprMentionsAny seen rhs = S.insert v seen
      | otherwise = seen

    isSelfCall rhs =
      case rhs of
        AppE fn _ _ _ | fn == funName -> True
        _ -> False

exprMentionsAny :: S.Set Var -> Exp3 -> Bool
exprMentionsAny vars rhs =
  not (S.null (collectVars rhs `S.intersection` vars))

exprHasParentChildUse :: S.Set Var -> Exp3 -> Bool
exprHasParentChildUse childVars ex =
  case ex of
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args ->
      any (exprMentionsAny childVars) args
    PrimAppE _ args ->
      any (exprMentionsAny childVars) args
    LetE (_, _, _, rhs) bod ->
      exprHasParentChildUse childVars rhs || exprHasParentChildUse childVars bod
    IfE cond thn els ->
      exprMentionsAny childVars cond
        || exprHasParentChildUse childVars thn
        || exprHasParentChildUse childVars els
    MkProdE args ->
      any (exprMentionsAny childVars) args
    ProjE _ rhs ->
      exprHasParentChildUse childVars rhs
    CaseE scrt brs ->
      exprMentionsAny childVars scrt
        || any (\(_, _, rhs) -> exprHasParentChildUse childVars rhs) brs
    DataConE _ _ args ->
      any (exprMentionsAny childVars) args
    TimeIt rhs _ _ ->
      exprHasParentChildUse childVars rhs
    WithArenaE _ rhs ->
      exprHasParentChildUse childVars rhs
    SpawnE _ _ args ->
      any (exprMentionsAny childVars) args
    SyncE -> False
    MapE (_, _, e1) e2 ->
      exprHasParentChildUse childVars e1 || exprHasParentChildUse childVars e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      any (exprHasParentChildUse childVars) [e1, e2, e3]
    Ext ext ->
      extHasParentChildUse childVars ext

extHasParentChildUse :: S.Set Var -> E3Ext () Ty3 -> Bool
extHasParentChildUse childVars ext =
  case ext of
    WriteScalar _ _ rhs ->
      exprMentionsAny childVars rhs
    WriteTagPacked _ rhs ->
      exprMentionsAny childVars rhs
    WriteTaggedCursor _ rhs ->
      exprMentionsAny childVars rhs
    WriteCursorMutable _ rhs ->
      exprMentionsAny childVars rhs
    WriteList _ rhs _ ->
      exprMentionsAny childVars rhs
    WriteVector _ rhs _ ->
      exprMentionsAny childVars rhs
    AddCursor _ rhs ->
      exprMentionsAny childVars rhs
    BumpCursorMutable _ rhs ->
      exprMentionsAny childVars rhs
    AddrOfCursor rhs ->
      exprHasParentChildUse childVars rhs
    LetAvail _ bod ->
      exprHasParentChildUse childVars bod
    Assert rhs ->
      exprMentionsAny childVars rhs
    ForE _ bound bod ->
      exprMentionsAny childVars bound || exprHasParentChildUse childVars bod
    WhileCursor _ bod ->
      exprHasParentChildUse childVars bod
    WhileCursorEnd _ _ bod ->
      exprHasParentChildUse childVars bod
    RetE args ->
      any (exprMentionsAny childVars) args
    _ ->
      False

mkFastPathBody :: Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkFastPathBody fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  dflags <- getDynFlags
  mkGenericFastPathBody dflags False fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans

mkMutableFastPathBody :: Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkMutableFastPathBody fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  dflags <- getDynFlags
  mkGenericFastPathBody dflags True fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans

mkGenericFastPathBody :: DynFlags -> Bool -> Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkGenericFastPathBody dflags isMutable fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  nameSeed <- freshLoopNameSeed isMutable
  let body = mkLets (prelude nameSeed) (fastBody nameSeed)
  pure body
  where
    -- The generated structure is:
    --
    --   for the dcon stream, and each constructor's scalar-buffer group:
    --     while representative_count_footer != NULL:
    --       count = scalar_count(representative_count_footer)
    --       set each output buffer's footer count to count
    --       for i in [0,count):
    --         copy/update one element in every buffer in the group
    --       if not last chunk:
    --         read each input redirection, grow each output region, and advance
    --         each footer cursor to the next chunk's count
    --
    -- This is intentionally buffer-oriented rather than recursive.  We fuse
    -- scalar buffers by constructor, not by field, because fields belonging to
    -- the same constructor have the same per-chunk element count.  Fully
    -- factored SoA layout keeps redirection boundaries aligned across buffers:
    -- when any buffer grows, all peer buffers get corresponding redirections.
    -- The dcon stream remains separate because its footer count is the total
    -- number of constructor tags in the chunk, not the count for a single
    -- constructor.  The generated loops rely on the RTS invariant that footer
    -- counts describe the next chunk in O(1): the final/end footer stores the
    -- first chunk count, and each redirection boundary footer stores the
    -- following chunk count.
    sortedPlans = L.sortOn sbpBufIx plans
    planMap = M.fromList [ (sbpBufIx p, p) | p <- sortedPlans ]
    bufferIndices = [0 .. arrLen - 1]
    scalarGroups
      | fuseScalarLoops =
          L.sortOn (minimum . map sbpBufIx) $
            map (L.sortOn sbpBufIx) $
              M.elems $
                M.fromListWith (++)
                  [ (sbpDCon plan, [plan])
                  | plan <- sortedPlans
                  ]
      | otherwise =
          map (:[]) sortedPlans
    loopGroups = Left 0 : map Right scalarGroups

    groupBufferIndices group =
      case group of
        Left ix -> [ix]
        Right groupPlans -> map sbpBufIx groupPlans

    groupRepIx group =
      case groupBufferIndices group of
        ix:_ -> ix
        [] -> error "loopify: empty loop group"

    nullFooter seed = loopName seed "null_footer"
    overwriteReg seed = loopName seed "overwrite_reg"
    inFinalArr seed = loopName seed "in_final_arr"
    outFinalArr seed = loopName seed "out_final_arr"
    packedPair seed = loopName seed "packed_pair"

    inputEndVar seed ix = loopBufferName seed ix "input_end"
    firstFooterVar seed ix = loopBufferName seed ix "first_footer"
    countFooterCurVar seed ix = loopBufferName seed ix "count_footer_cur"
    countFooterLocVar seed ix = loopBufferName seed ix "count_footer_loc"
    nextFooterCurVar seed ix = loopBufferName seed ix "next_footer_cur"
    nextFooterLocVar seed ix = loopBufferName seed ix "next_footer_loc"
    inLocVar seed ix = loopBufferName seed ix "in_loc"
    outLocVar seed ix = loopBufferName seed ix "out_loc"
    outEndLocVar seed ix = loopBufferName seed ix "out_end_loc"
    loopResVar seed ix = loopBufferName seed ix "loop"
    scalarLoopResVar seed ix dcon =
      loopBufferName seed ix ("dcon_" ++ sanitizeLoopName dcon ++ "_loop")
    finalInVar seed ix = loopBufferName seed ix "in_final"
    finalOutVar seed ix = loopBufferName seed ix "out_final"
    finalOutEndVar seed ix = loopBufferName seed ix "out_end_final"

    depStartVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_start")
    depLocVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_loc")

    depReadCurVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_read_cur")
    depReadPairVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_read_pair")
    depReadValVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_read_val")
    depBumpVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_bump")
    depBoundaryCurVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_boundary_cur")
    depBoundaryPairVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_boundary_pair")
    depBoundaryAfterVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_boundary_after")
    depRedirPairVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_redir_pair")
    depNextStartVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_next_start")
    depSetInVar seed ix depIx = loopBufferName seed ix ("dep" ++ show depIx ++ "_set_in")

    prelude pfx =
      [ (nullFooter pfx, [], CursorTy, Ext NullCursor) ]
      ++ concatMap (mkBufferPrelude pfx) bufferIndices
      ++ concatMap (mkDependencyPrelude pfx) dependencyPairs

    dependencyPairs =
      [ (sbpBufIx plan, info)
      | plan <- sortedPlans
      , info <- planDependencyInfos plan
      , siiBufIx info /= sbpBufIx plan
      ]

    -- Each buffer loop owns its mutable input/output cursors and the footer
    -- cursors used for chunk bounds.  Cross-buffer dependency cursors are
    -- separate mutable cursors initialized from the original input cursor
    -- array; they are not aliases of another buffer loop's main cursor.
    mkBufferPrelude pfx ix =
      [ (inputEndVar pfx ix, [], CursorTy, indexCursorExp inEnds ix)
      , (firstFooterVar pfx ix, [], CursorTy, Ext $ ReadScalarCountFirstFooter (inputEndVar pfx ix))
      , (countFooterCurVar pfx ix, [], CursorTy, VarE (inputEndVar pfx ix))
      , (countFooterLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (VarE (countFooterCurVar pfx ix)))
      , (nextFooterCurVar pfx ix, [], CursorTy, VarE (firstFooterVar pfx ix))
      , (nextFooterLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (VarE (nextFooterCurVar pfx ix)))
      , (inLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp inCurs ix))
      , (outLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outCurs ix))
      , (outEndLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outEnds ix))
      ]

    mkDependencyPrelude pfx (ix, info) =
      let depIx = siiBufIx info
       in [ (depStartVar pfx ix depIx, [], CursorTy, indexCursorExp inCurs depIx)
          , (depLocVar pfx ix depIx, [], MutCursorTy, Ext $ AddrOfCursor (VarE (depStartVar pfx ix depIx)))
          ]

    fastBody pfx =
      if isMutable
        then mkLets (map (mkLoopGroup pfx) loopGroups) (MkProdE [])
        else
          mkLets
            ( map (mkLoopGroup pfx) loopGroups
                ++ concatMap (mkBufferFinalLets pfx) bufferIndices
                ++ [ (overwriteReg pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalOutEndVar pfx) bufferIndices))
                   , (inFinalArr pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalInVar pfx) bufferIndices))
                   , (outFinalArr pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalOutVar pfx) bufferIndices))
                   , (packedPair pfx, [], ProdTy [CursorArrayTy arrLen, CursorArrayTy arrLen], MkProdE [VarE outCurs, VarE (outFinalArr pfx)])
                   ]
            )
            (MkProdE [VarE inEnds, VarE (overwriteReg pfx), VarE (inFinalArr pfx), VarE (packedPair pfx)])

    mkLoopGroup pfx group =
      let repIx = groupRepIx group
          resVar =
            case group of
              Left{} -> loopResVar pfx repIx
              Right (plan:_) -> scalarLoopResVar pfx repIx (sbpDCon plan)
              Right [] -> loopResVar pfx repIx
       in (resVar, [], ProdTy [], Ext $ WhileCursor (countFooterLocVar pfx repIx) (mkGroupChunkBody pfx group))

    mkBufferFinalLets pfx ix =
      [ (finalInVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
      , (finalOutVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
      , (finalOutEndVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (outEndLocVar pfx ix))
      ]

    mkGroupChunkBody pfx group =
      let repIx = groupRepIx group
          currentCountFooter = loopBufferName pfx repIx "current_count_footer"
          chunkCount = loopBufferName pfx repIx "chunk_count"
          currentNextFooter = loopBufferName pfx repIx "current_next_footer"
          isNullNextFooter = loopBufferName pfx repIx "is_null_next_footer"
          isEndNextFooter = loopBufferName pfx repIx "is_end_next_footer"
          isLastChunk = loopBufferName pfx repIx "is_last_chunk"
          innerLoopRes = loopBufferName pfx repIx "inner_loop_res"
          chunkBranch = loopBufferName pfx repIx "chunk_branch"
       in mkLets
            ( [ (currentCountFooter, [], CursorTy, Ext $ DerefMutCursor (countFooterLocVar pfx repIx))
              , (chunkCount, [], IntTy, Ext $ ReadScalarCount currentCountFooter)
              , (currentNextFooter, [], CursorTy, Ext $ DerefMutCursor (nextFooterLocVar pfx repIx))
              , (isNullNextFooter, [], BoolTy, PrimAppE EqIntP [VarE currentNextFooter, VarE (nullFooter pfx)])
              , (isEndNextFooter, [], BoolTy, PrimAppE EqIntP [VarE currentNextFooter, VarE (inputEndVar pfx repIx)])
              , (isLastChunk, [], BoolTy, PrimAppE OrP [VarE isNullNextFooter, VarE isEndNextFooter])
              ]
              ++ concatMap (mkSetChunkCountLets pfx chunkCount) (groupBufferIndices group)
              ++ [ (innerLoopRes, [], ProdTy [], Ext $ ForE (loopBufferName pfx repIx "i") (VarE chunkCount) (mkGroupInnerLoopBody pfx group))
                 , (chunkBranch, [], ProdTy [], IfE (VarE isLastChunk) (mkGroupLastChunkBody pfx group) (mkGroupContinueChunkBody pfx group currentNextFooter))
              ]
            )
            (MkProdE [])

    mkSetChunkCountLets pfx chunkCount ix =
      let currentOutEnd = loopBufferName pfx ix "current_out_end"
          setChunkCount = loopBufferName pfx ix "set_chunk_count"
       in [ (currentOutEnd, [], CursorTy, Ext $ DerefMutCursor (outEndLocVar pfx ix))
          , (setChunkCount, [], ProdTy [], Ext $ ScalarCountSet currentOutEnd chunkCount)
          ]

    mkGroupInnerLoopBody pfx group =
      case group of
        Left ix -> mkDConInnerLoop pfx ix
        Right groupPlans ->
          mkLets
            [ (loopBufferName pfx (sbpBufIx plan) "inner_body", [], ProdTy [], mkScalarInnerLoop pfx (sbpBufIx plan) plan)
            | plan <- groupPlans
            ]
            (MkProdE [])

    -- The tag stream is copied from input to output.  We deliberately avoid
    -- hardcoding constructor tags here: tree-like and multi-constructor ADTs
    -- may have arbitrary tag order in the packed input.
    mkDConInnerLoop pfx ix =
      let readCur = loopBufferName pfx ix "read_cur"
          readPair = loopBufferName pfx ix "read_pair"
          readTag = loopBufferName pfx ix "read_tag"
          writeCur = loopBufferName pfx ix "write_cur"
          writeTag = loopBufferName pfx ix "write_tag"
          bumpIn = loopBufferName pfx ix "bump_in"
          bumpOut = loopBufferName pfx ix "bump_out"
       in mkLets
            [ (readCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
            , (readPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag readCur)
            , (readTag, [], IntTy, ProjE 0 (VarE readPair))
            , (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
            , (writeTag, [], CursorTy, Ext $ WriteTagPacked writeCur (VarE readTag))
            , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (LitE 1))
            , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (LitE 1))
            ]
            (MkProdE [])

    -- Scalar buffers either copy the input value or apply the extracted pure
    -- scalar expression.  Conditional scalar expressions are emitted as
    -- unit-valued write branches so that lowering can keep `ForE` bodies as
    -- unit tails.  Output footer metadata is set once per chunk in
    -- `mkBufferChunkBody`; shape-preserving maps do not need per-element
    -- metadata bumps.
    mkScalarInnerLoop pfx ix plan@ScalarBufferPlan{sbpTy, sbpScalar, sbpOp} =
      let readCur = loopBufferName pfx ix "read_cur"
          readPair = loopBufferName pfx ix "read_pair"
          readVal = loopBufferName pfx ix "read_val"
          fieldVal = loopBufferName pfx ix "field_val"
          fieldThenVal = loopBufferName pfx ix "field_then_val"
          fieldElseVal = loopBufferName pfx ix "field_else_val"
          writeCur = loopBufferName pfx ix "write_cur"
          writeVal = loopBufferName pfx ix "write_val"
          writeThenVal = loopBufferName pfx ix "write_then_val"
          writeElseVal = loopBufferName pfx ix "write_else_val"
          conditionalWrite = loopBufferName pfx ix "conditional_write"
          bumpIn = loopBufferName pfx ix "bump_in"
          bumpOut = loopBufferName pfx ix "bump_out"
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc sbpTy) (sizeOfTyD dflags sbpTy)
          rawFieldExpr = instantiateScalarOp pfx ix readVal sbpOp
          (fieldExprLets, fieldExpr) = anfScalarExpr pfx ix rawFieldExpr
          commonLets =
            [ (readCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
            , (readPair, [], ProdTy [sbpTy, CursorTy], Ext $ ReadScalar sbpScalar readCur)
            , (readVal, [], sbpTy, ProjE 0 (VarE readPair))
            ]
            ++ concatMap (mkDependencyRead pfx ix) (planDependencies plan)
            ++ fieldExprLets
          writeLets =
            case fieldExpr of
              IfE cond thn els ->
                [ (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
                , ( conditionalWrite
                  , []
                  , ProdTy []
                  , IfE cond
                      (mkScalarWriteBranch fieldThenVal writeThenVal writeCur thn)
                      (mkScalarWriteBranch fieldElseVal writeElseVal writeCur els)
                  )
                , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (LitE scalarBytes))
                , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (LitE scalarBytes))
                ]
              _ ->
                [ (fieldVal, [], sbpTy, fieldExpr)
                , (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
                , (writeVal, [], CursorTy, Ext $ WriteScalar sbpScalar writeCur (VarE fieldVal))
                , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (LitE scalarBytes))
                , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (LitE scalarBytes))
                ]
       in mkLets
            (commonLets ++ writeLets)
            (MkProdE [])
      where
        mkScalarWriteBranch fieldVar writeVar writeCur expr =
          mkLets
            [ (fieldVar, [], sbpTy, expr)
            , (writeVar, [], CursorTy, Ext $ WriteScalar sbpScalar writeCur (VarE fieldVar))
            ]
            (MkProdE [])

    -- Cross-buffer dependencies are read with their own cursor.  This fixed
    -- the `scaleEnergy` case where one field's update depended on another
    -- field buffer that had already been walked by its own loop.
    mkDependencyRead pfx ix (_, info)
      | depIx == ix = []
      | otherwise =
          let depTy = scalarToTy (siiScalar info)
              depBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc depTy) (sizeOfTyD dflags depTy)
           in [ (depReadCurVar pfx ix depIx, [], CursorTy, Ext $ DerefMutCursor (depLocVar pfx ix depIx))
              , (depReadPairVar pfx ix depIx, [], ProdTy [depTy, CursorTy], Ext $ ReadScalar (siiScalar info) (depReadCurVar pfx ix depIx))
              , (depReadValVar pfx ix depIx, [], depTy, ProjE 0 (VarE (depReadPairVar pfx ix depIx)))
              , (depBumpVar pfx ix depIx, [], ProdTy [], Ext $ BumpCursorMutable (depLocVar pfx ix depIx) (LitE depBytes))
              ]
      where
        depIx = siiBufIx info

    instantiateScalarOp pfx ix readVal op =
      case op of
        ScalarCopy -> VarE readVal
        ScalarExpr expr deps ->
          substMany
            [ (src, replacementFor info)
            | (src, info) <- M.toList deps
            ]
            expr
      where
        replacementFor info
          | siiBufIx info == ix = VarE readVal
          | otherwise = VarE (depReadValVar pfx ix (siiBufIx info))

    anfScalarExpr :: LoopNameSeed -> Int -> Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3)
    anfScalarExpr pfx ix expr =
      let (binds, expr', _) = go 0 expr
       in (binds, expr')
      where
        tmpVar :: Int -> Var
        tmpVar n = loopBufferName pfx ix ("anf" ++ show n)

        go :: Int -> Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3, Int)
        go n ex =
          case ex of
            VarE{} -> ([], ex, n)
            LitE{} -> ([], ex, n)
            CharE{} -> ([], ex, n)
            FloatE{} -> ([], ex, n)
            LitSymE{} -> ([], ex, n)
            PrimAppE p args ->
              let (argBinds, args', n') = goArgs n args
                  tmp = tmpVar n'
                  ty = primRetTy p
               in (argBinds ++ [(tmp, [], ty, PrimAppE p args')], VarE tmp, n' + 1)
            IfE a b c ->
              let (ab, a', n1) = go n a
                  (bb, b', n2) = go n1 b
                  (cb, c', n3) = go n2 c
               in (ab ++ bb ++ cb, IfE a' b' c', n3)
            ProjE i e ->
              let (bs, e', n') = go n e
               in (bs, ProjE i e', n')
            _ -> ([], ex, n)

        goArgs :: Int -> [Exp3] -> ([(Var, [()], Ty3, Exp3)], [Exp3], Int)
        goArgs n [] = ([], [], n)
        goArgs n (arg:rest) =
          let (bs1, arg', n1) = go n arg
              (bs2, rest', n2) = goArgs n1 rest
           in (bs1 ++ bs2, arg' : rest', n2)

    planDependencies ScalarBufferPlan{sbpOp} =
      case sbpOp of
        ScalarCopy -> []
        ScalarExpr _ deps -> L.sortOn (siiBufIx . snd) (M.toList deps)

    planDependencyInfos plan =
      M.elems $
        M.fromList
          [ (siiBufIx info, info)
          | (_, info) <- planDependencies plan
          ]

    mkGroupLastChunkBody pfx group =
      let updateCountFooter ix = loopBufferName pfx ix "update_count_footer"
       in mkLets
            [ (updateCountFooter ix, [], ProdTy [], Ext $ WriteCursorMutable (countFooterLocVar pfx ix) (VarE (nullFooter pfx)))
            | ix <- groupBufferIndices group
            ]
            (MkProdE [])

    mkGroupContinueChunkBody pfx group repCurrentNextFooter =
      let repIx = groupRepIx group
       in mkLets
            (concatMap (mkContinueOneBuffer pfx repIx repCurrentNextFooter) (groupBufferIndices group))
            (MkProdE [])

    mkContinueOneBuffer pfx repIx repCurrentNextFooter ix =
      let currentNextFooter =
            if ix == repIx
            then repCurrentNextFooter
            else loopBufferName pfx ix "current_next_footer"
          readCurrentNextFooter =
            if ix == repIx
            then []
            else [(currentNextFooter, [], CursorTy, Ext $ DerefMutCursor (nextFooterLocVar pfx ix))]
       in readCurrentNextFooter ++ mkContinueOneBufferLets pfx ix currentNextFooter

    mkContinueOneBufferLets pfx ix currentNextFooter =
      let boundaryCur = loopBufferName pfx ix "boundary_cur"
          boundaryPair = loopBufferName pfx ix "boundary_pair"
          boundaryAfter = loopBufferName pfx ix "boundary_after"
          redirPair = loopBufferName pfx ix "redir_pair"
          nextStart = loopBufferName pfx ix "next_start"
          growOut = loopBufferName pfx ix "grow_out"
          setIn = loopBufferName pfx ix "set_in"
          nextNextFooter = loopBufferName pfx ix "next_next_footer"
          updateCountFooter = loopBufferName pfx ix "update_count_footer"
          updateNextFooter = loopBufferName pfx ix "update_next_footer"
       in [ (boundaryCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
          , (boundaryPair, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag boundaryCur)
          , (boundaryAfter, [], CursorTy, ProjE 1 (VarE boundaryPair))
          , (redirPair, [], ProdTy [CursorTy, CursorTy, IntTy], Ext $ ReadTaggedCursor boundaryAfter)
          , (nextStart, [], CursorTy, ProjE 0 (VarE redirPair))
          , (growOut, [], ProdTy [], Ext $ GrowRegion (outLocVar pfx ix) (outEndLocVar pfx ix))
          , (setIn, [], ProdTy [], Ext $ WriteCursorMutable (inLocVar pfx ix) (VarE nextStart))
          ]
          ++ mkDependencyContinueLets pfx ix
          ++
          [ (nextNextFooter, [], CursorTy, Ext $ ReadScalarCountNextFooter currentNextFooter)
          , (updateCountFooter, [], ProdTy [], Ext $ WriteCursorMutable (countFooterLocVar pfx ix) (VarE currentNextFooter))
          , (updateNextFooter, [], ProdTy [], Ext $ WriteCursorMutable (nextFooterLocVar pfx ix) (VarE nextNextFooter))
          ]

    -- Dependency cursors must follow the same chunk transitions as their
    -- consumer loop.  At a redirection boundary, read the dependent buffer's
    -- redirection tag and reset that dependency cursor to the next chunk
    -- start.  This is independent of the dependency buffer's own main loop.
    mkDependencyContinueLets pfx ix =
      case M.lookup ix planMap of
        Nothing -> []
        Just plan -> concatMap (mkDependencyContinue pfx ix) (planDependencyInfos plan)

    mkDependencyContinue pfx ix info
      | depIx == ix = []
      | otherwise =
          [ (depBoundaryCurVar pfx ix depIx, [], CursorTy, Ext $ DerefMutCursor (depLocVar pfx ix depIx))
          , (depBoundaryPairVar pfx ix depIx, [], ProdTy [IntTy, CursorTy], Ext $ ReadTag (depBoundaryCurVar pfx ix depIx))
          , (depBoundaryAfterVar pfx ix depIx, [], CursorTy, ProjE 1 (VarE (depBoundaryPairVar pfx ix depIx)))
          , (depRedirPairVar pfx ix depIx, [], ProdTy [CursorTy, CursorTy, IntTy], Ext $ ReadTaggedCursor (depBoundaryAfterVar pfx ix depIx))
          , (depNextStartVar pfx ix depIx, [], CursorTy, ProjE 0 (VarE (depRedirPairVar pfx ix depIx)))
          , (depSetInVar pfx ix depIx, [], ProdTy [], Ext $ WriteCursorMutable (depLocVar pfx ix depIx) (VarE (depNextStartVar pfx ix depIx)))
          ]
      where
        depIx = siiBufIx info

    indexCursorExp arr ix = Ext $ IndexCursorArray arr ix

    substMany :: [(Var, Exp3)] -> Exp3 -> Exp3
    substMany replacements ex =
      foldl (\acc (old, new) -> substE (VarE old) new acc) ex replacements

collectScalarInputsWithRoles :: M.Map Var BufferRole -> [(Var, [()], Ty3, Exp3)] -> M.Map Var ScalarInputInfo
collectScalarInputsWithRoles roles binds = goTuple M.empty M.empty binds
  where
    goTuple _ acc [] = acc
    goTuple tupleMap acc ((v, _, _, rhs):rest) =
      case rhs of
        Ext (ReadScalar s cur) ->
          case M.lookup cur roles of
            Just (InputBuf ix) ->
              let tupleMap' = M.insert v (ScalarInputInfo s ix) tupleMap
               in goTuple tupleMap' acc rest
            _ -> goTuple tupleMap acc rest
        ProjE 0 (VarE tup) ->
          case M.lookup tup tupleMap of
            Just info -> goTuple tupleMap (M.insert v info acc) rest
            Nothing -> goTuple tupleMap acc rest
        _ -> goTuple tupleMap acc rest

collectPureBindings :: M.Map Var ScalarInputInfo -> [(Var, [()], Ty3, Exp3)] -> M.Map Var Exp3
collectPureBindings scalarInputs = go M.empty
  where
    go env [] = env
    go env ((v, _, _, rhs):rest)
      | v `M.member` scalarInputs = go env rest
      | otherwise =
          case normalizePureExpr env rhs of
            rhs'
              | isSupportedPureExpr rhs' ->
                  go (M.insert v rhs' env) rest
            _ -> go env rest

normalizePureExpr :: M.Map Var Exp3 -> Exp3 -> Exp3
normalizePureExpr env ex =
  case ex of
    VarE v -> fromMaybe (VarE v) (M.lookup v env)
    LitE{} -> ex
    CharE{} -> ex
    FloatE{} -> ex
    LitSymE{} -> ex
    PrimAppE p args -> PrimAppE p (map (normalizePureExpr env) args)
    IfE a b c -> IfE (normalizePureExpr env a) (normalizePureExpr env b) (normalizePureExpr env c)
    ProjE i e -> ProjE i (normalizePureExpr env e)
    _ -> ex

isSupportedPureExpr :: Exp3 -> Bool
isSupportedPureExpr ex =
  case ex of
    VarE{} -> True
    LitE{} -> True
    CharE{} -> True
    FloatE{} -> True
    LitSymE{} -> True
    PrimAppE _ args -> all isSupportedPureExpr args
    IfE a b c -> all isSupportedPureExpr [a, b, c]
    ProjE _ e -> isSupportedPureExpr e
    _ -> False

collectMentionedDataCons :: Exp3 -> [DataCon]
collectMentionedDataCons ex =
  case ex of
    VarE{} -> []
    LitE{} -> []
    CharE{} -> []
    FloatE{} -> []
    LitSymE{} -> []
    AppE _ _ _ args -> concatMap collectMentionedDataCons args
    PrimAppE _ args -> concatMap collectMentionedDataCons args
    LetE (_, _, _, rhs) bod ->
      collectMentionedDataCons rhs ++ collectMentionedDataCons bod
    IfE a b c ->
      collectMentionedDataCons a
        ++ collectMentionedDataCons b
        ++ collectMentionedDataCons c
    MkProdE ls -> concatMap collectMentionedDataCons ls
    ProjE _ e -> collectMentionedDataCons e
    CaseE scrt brs ->
      collectMentionedDataCons scrt
        ++ concatMap
          (\(dcon, _, rhs) -> dcon : collectMentionedDataCons rhs)
          brs
    DataConE _ dcon args -> dcon : concatMap collectMentionedDataCons args
    TimeIt e _ _ -> collectMentionedDataCons e
    WithArenaE _ e -> collectMentionedDataCons e
    SpawnE _ _ args -> concatMap collectMentionedDataCons args
    SyncE -> []
    MapE (_, _, e1) e2 ->
      collectMentionedDataCons e1 ++ collectMentionedDataCons e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      collectMentionedDataCons e1
        ++ collectMentionedDataCons e2
        ++ collectMentionedDataCons e3
    Ext ext ->
      case ext of
        ReadScalar{} -> []
        WriteScalar _ _ rhs -> collectMentionedDataCons rhs
        ReadTag{} -> []
        WriteTag dcon _ -> [dcon]
        WriteTagPacked _ rhs -> collectMentionedDataCons rhs
        TagCursor{} -> []
        WriteCursorIndirection{} -> []
        WriteCursorSelectiveIndirection _ _ _ mask -> collectMentionedDataCons mask
        UnwrapSelectiveIndirections{} -> []
        WriteTaggedCursor _ rhs -> collectMentionedDataCons rhs
        MemCpy{} -> []
        ReadTaggedCursor{} -> []
        ReadCursor{} -> []
        GrowRegion{} -> []
        WriteCursorMutable _ rhs -> collectMentionedDataCons rhs
        ReadList{} -> []
        WriteList _ rhs _ -> collectMentionedDataCons rhs
        ReadVector{} -> []
        WriteVector _ rhs _ -> collectMentionedDataCons rhs
        MakeCursorArray{} -> []
        IndexCursorArray{} -> []
        AddCursor _ rhs -> collectMentionedDataCons rhs
        BumpCursorMutable _ rhs -> collectMentionedDataCons rhs
        AddrOfCursor rhs -> collectMentionedDataCons rhs
        DerefMutCursor{} -> []
        CastPtr{} -> []
        SubPtr{} -> []
        NewBuffer{} -> []
        ScopedBuffer{} -> []
        NewParBuffer{} -> []
        ScopedParBuffer{} -> []
        EndOfBuffer{} -> []
        MMapFileSize{} -> []
        SizeOfPacked{} -> []
        SizeOfScalar{} -> []
        BoundsCheck{} -> []
        BoundsCheckVector{} -> []
        IndirectionBarrier{} -> []
        BumpArenaRefCount{} -> []
        NullCursor -> []
        InitCursor{} -> []
        RetE ls -> concatMap collectMentionedDataCons ls
        GetCilkWorkerNum -> []
        LetAvail _ bod -> collectMentionedDataCons bod
        AllocateTagHere{} -> []
        AllocateScalarsHere{} -> []
        StartTagAllocation{} -> []
        EndTagAllocation{} -> []
        StartScalarsAllocation{} -> []
        EndScalarsAllocation{} -> []
        ScalarCountBump dcon _ -> [dcon]
        ScalarCountSet{} -> []
        ScalarCountCopyAll{} -> []
        ReadScalarCount{} -> []
        ReadScalarCountFirstFooter{} -> []
        ReadScalarCountNextFooter{} -> []
        ForE _ bound bod ->
          collectMentionedDataCons bound ++ collectMentionedDataCons bod
        WhileCursor _ bod -> collectMentionedDataCons bod
        WhileCursorEnd _ _ bod -> collectMentionedDataCons bod
        VecBroadcast _ _ val -> collectMentionedDataCons val
        VecLoad{} -> []
        VecAdd _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecSub _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecMul _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecDiv _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecMod _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecEq _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecSelect _ _ m a b -> collectMentionedDataCons m ++ collectMentionedDataCons a ++ collectMentionedDataCons b
        VecStore _ _ _ val -> collectMentionedDataCons val
        SSPush{} -> []
        SSPop{} -> []
        Assert rhs -> collectMentionedDataCons rhs
