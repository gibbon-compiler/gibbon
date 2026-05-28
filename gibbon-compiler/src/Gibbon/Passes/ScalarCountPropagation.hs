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
  ) where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import qualified Gibbon.L3.Syntax as L3

data CursorPairShape = CursorPairShape
  { cpsLen :: Int
  , cpsEndArgIx :: Int
  , cpsCurArgIx :: Int
  }
  deriving (Eq, Ord, Show)

data ProducerShape = ProducerShape
  { psInput :: CursorPairShape
  , psOutput :: CursorPairShape
  }
  deriving (Eq, Ord, Show)

propagateScalarCounts :: L3.Prog3 -> PassM L3.Prog3
propagateScalarCounts prog@Prog{fundefs, mainExp} = do
  dflags <- getDynFlags
  let enabled = gopt Opt_StoreScalarFieldCounts dflags
      producerShapes =
        if enabled
        then M.mapMaybe producerShape fundefs
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

    rewriteExt ext =
      case ext of
        L3.ForE idx bound bod -> L3.ForE idx <$> go bound <*> go bod
        L3.WhileCursor cur bod -> L3.WhileCursor cur <$> go bod
        L3.WhileCursorEnd cur end bod -> L3.WhileCursorEnd cur end <$> go bod
        L3.WriteScalar s cur rhs -> L3.WriteScalar s cur <$> go rhs
        L3.WriteTagPacked cur rhs -> L3.WriteTagPacked cur <$> go rhs
        L3.WriteTaggedCursor cur rhs -> L3.WriteTaggedCursor cur <$> go rhs
        L3.WriteCursorMutable cur rhs -> L3.WriteCursorMutable cur <$> go rhs
        L3.WriteList cur rhs ty -> (\rhs' -> L3.WriteList cur rhs' ty) <$> go rhs
        L3.WriteVector cur rhs ty -> (\rhs' -> L3.WriteVector cur rhs' ty) <$> go rhs
        L3.AddCursor cur rhs -> L3.AddCursor cur <$> go rhs
        L3.BumpCursorMutable cur rhs -> L3.BumpCursorMutable cur <$> go rhs
        L3.AddrOfCursor rhs -> L3.AddrOfCursor <$> go rhs
        L3.LetAvail vars bod -> L3.LetAvail vars <$> go bod
        L3.Assert rhs -> L3.Assert <$> go rhs
        L3.WriteCursorSelectiveIndirection cur target end mask ->
          L3.WriteCursorSelectiveIndirection cur target end <$> go mask
        _ -> pure ext

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

producerShape :: L3.FunDef3 -> Maybe ProducerShape
producerShape fn
  | bodyWritesScalarCounts (funBody fn) = Nothing
  | otherwise =
      case (soaInputCursorShapes (funArgs fn) (fst (funTy fn)),
            soaOutputCursorShape (funArgs fn) (fst (funTy fn))) of
        ([inputShape], Just outputShape)
          | cpsLen inputShape == cpsLen outputShape ->
              Just $ ProducerShape inputShape outputShape
        _ -> Nothing

soaInputCursorShapes :: [Var] -> [L3.Ty3] -> [CursorPairShape]
soaInputCursorShapes args tys =
  case cursorArrays of
    [(endIx, _, n1), _, _, (curIx, _, n2)]
      | n1 == n2 && n1 > 1 -> [CursorPairShape n1 endIx curIx]
    _ -> []
  where
    cursorArrays =
      [ (ix, v, n)
      | (ix, (v, L3.CursorArrayTy n)) <- zip [0..] (zip args tys)
      ]

soaOutputCursorShape :: [Var] -> [L3.Ty3] -> Maybe CursorPairShape
soaOutputCursorShape args tys =
  case cursorArrays of
    [_ , (outEndIx, _, n2), (outCurIx, _, n3), _]
      | n2 == n3 && n2 > 1 -> Just (CursorPairShape n2 outEndIx outCurIx)
    _ -> Nothing
  where
    cursorArrays =
      [ (ix, v, n)
      | (ix, (v, L3.CursorArrayTy n)) <- zip [0..] (zip args tys)
      ]

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

extWritesScalarCounts :: L3.E3Ext () L3.Ty3 -> Bool
extWritesScalarCounts ext =
  case ext of
    L3.ScalarCountBump{} -> True
    L3.ScalarCountSet{} -> True
    L3.ScalarCountCopyAll _ _ _ -> True
    L3.ForE _ bound bod -> bodyWritesScalarCounts bound || bodyWritesScalarCounts bod
    L3.WhileCursor _ bod -> bodyWritesScalarCounts bod
    L3.WhileCursorEnd _ _ bod -> bodyWritesScalarCounts bod
    L3.WriteScalar _ _ rhs -> bodyWritesScalarCounts rhs
    L3.WriteTagPacked _ rhs -> bodyWritesScalarCounts rhs
    L3.WriteTaggedCursor _ rhs -> bodyWritesScalarCounts rhs
    L3.WriteCursorMutable _ rhs -> bodyWritesScalarCounts rhs
    L3.WriteList _ rhs _ -> bodyWritesScalarCounts rhs
    L3.WriteVector _ rhs _ -> bodyWritesScalarCounts rhs
    L3.AddCursor _ rhs -> bodyWritesScalarCounts rhs
    L3.BumpCursorMutable _ rhs -> bodyWritesScalarCounts rhs
    L3.AddrOfCursor rhs -> bodyWritesScalarCounts rhs
    L3.LetAvail _ bod -> bodyWritesScalarCounts bod
    L3.Assert rhs -> bodyWritesScalarCounts rhs
    L3.WriteCursorSelectiveIndirection _ _ _ mask -> bodyWritesScalarCounts mask
    _ -> False
