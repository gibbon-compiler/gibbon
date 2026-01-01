module Gibbon.Passes.OptimizeL3 (removeReDefs) where

import qualified Data.Map as M
import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax


removeReDefs :: Prog3 -> PassM Prog3
removeReDefs Prog {ddefs, fundefs, mainExp} = do
  main' <- case mainExp of
    Just (m, t) -> do
      m' <- removeReDefsExp (Env2 M.empty funEnv) m
      return $ Just (m', t)
    Nothing -> return Nothing
  fds' <- mapM removeReDefsFn fundefs
  return $ Prog ddefs fds' main'
  where
    funEnv = M.map funTy fundefs

    removeReDefsFn :: FunDef3 -> PassM FunDef3
    removeReDefsFn f@FunDef {funTy, funArgs, funBody} = do
      let in_tys = inTys funTy
      let env2 = Env2 (M.fromList $ zip funArgs in_tys) funEnv
      funBody' <- removeReDefsExp env2 funBody
      return $ f {funBody = funBody'}

removeReDefsExp :: Env2 Var Ty3 -> Exp3 -> PassM Exp3
removeReDefsExp env ex =
  case ex of
    LetE (v, locs, ty, rhs) bod -> do
      case mblookupVEnv v env of 
              Nothing -> do   
                          let env' = extendVEnv v ty env
                          rhs' <- removeReDefsExp env' rhs
                          bod' <- removeReDefsExp env' bod
                          pure $ (LetE (v, locs, ty, rhs')) bod'
              _ -> do
                if v == "_"
                then do
                   let env' = extendVEnv v ty env
                   rhs' <- removeReDefsExp env' rhs
                   bod' <- removeReDefsExp env' bod
                   pure $ (LetE (v, locs, ty, rhs')) bod'
                else do 
                  bod' <- removeReDefsExp env bod 
                  pure bod' 
    MkProdE es -> do
      MkProdE <$> mapM go es

    ProjE i e -> ProjE i <$> go e
    VarE v -> do
      return $ VarE v
    LitE {} -> pure ex
    CharE {} -> pure ex
    FloatE {} -> pure ex
    LitSymE {} -> pure ex
    AppE f cty locs args -> AppE f cty locs <$> mapM go args
    PrimAppE pr args -> PrimAppE pr <$> mapM go args
    IfE a b c -> do
      a' <- go a
      b' <- go b
      c' <- go c
      pure $ IfE a' b' c'
    CaseE scrt ls -> do
      scrt' <- go scrt
      ls' <-
        mapM
          ( \(dcon, vlocs, rhs) -> do
              rhs' <- go rhs
              pure $ (dcon, vlocs, rhs')
          )
          ls
      pure $ CaseE scrt' ls'
    DataConE loc dcon args -> DataConE loc dcon <$> mapM go args
    TimeIt e ty b -> do
      e' <- go e
      pure $ TimeIt e' ty b
    WithArenaE v e -> do
      e' <- go e
      pure $ WithArenaE v e'
    SpawnE v locs args -> SpawnE v locs <$> mapM go args
    SyncE -> pure ex
    Ext (RetE ls) -> do
      ls' <- mapM go ls
      pure $ Ext (RetE ls')
    Ext (LetAvail vs bod) -> do
      bod' <- go bod
      pure $ Ext (LetAvail vs bod')
    Ext (ReadScalar s v) -> do
      pure $ Ext (ReadScalar s v)
    Ext (WriteScalar s v e) -> do
      e' <- go e
      pure $ Ext (WriteScalar s v e')
    Ext (ReadTag v) -> do
      pure (Ext $ ReadTag v)
    Ext (WriteTag dcon v) -> do
      pure (Ext $ WriteTag dcon v)
    Ext (TagCursor a b) -> do
      pure (Ext $ TagCursor a b)
    Ext (WriteTaggedCursor v e) -> do
      e' <- go e
      pure (Ext $ WriteTaggedCursor v e')
    Ext (MemCpy{}) -> return ex    
    Ext (ReadTaggedCursor v) -> do
      pure (Ext $ ReadTaggedCursor v)
    Ext (ReadCursor v) -> do
      pure (Ext $ ReadCursor v)
    Ext (WriteCursor v e) -> do
      e' <- go e
      pure (Ext $ WriteCursor v e')
    Ext (ReadList v ty) -> do
      pure (Ext $ ReadList v ty)
    Ext (WriteList v e ty) -> do
      e' <- go e
      pure (Ext $ WriteList v e' ty)
    Ext (ReadVector v ty) -> do
      pure (Ext $ ReadVector v ty)
    Ext (WriteVector v e ty) -> do
      e' <- go e
      pure (Ext $ WriteVector v e' ty)
    Ext (AddCursor v e) -> do
      e' <- go e
      pure (Ext $ AddCursor v e')
    Ext (BumpCursorMutable v e) -> do
      e' <- go e
      pure (Ext $ BumpCursorMutable v e')
    Ext (DerefMutCursor v) -> do 
      pure (Ext $ DerefMutCursor v)
    Ext (SubPtr a b) -> do
      pure (Ext $ SubPtr a b)
    Ext (NewBuffer _ _) -> return ex
    Ext (ScopedBuffer _) -> return ex
    Ext (NewParBuffer _) -> return ex
    Ext (ScopedParBuffer _) -> return ex
    Ext (EndOfBuffer _ _) -> return ex
    Ext (MMapFileSize v) -> do
      pure $ Ext (MMapFileSize v)
    Ext (SizeOfPacked a b) -> do
      pure (Ext $ SizeOfPacked a b)
    Ext (SizeOfScalar v) -> do
      pure $ Ext (SizeOfScalar v)
    Ext (BoundsCheck i a b c d) -> do
      pure $ Ext (BoundsCheck i a b c d)
    Ext (BoundsCheckVector{}) -> pure ex
    Ext (IndirectionBarrier _ (_, _, _, _)) -> pure ex
    Ext (BumpArenaRefCount _ _) -> pure ex
    Ext NullCursor -> pure ex
    Ext InitCursor{} -> pure ex
    Ext GetCilkWorkerNum -> pure ex
    Ext (AllocateTagHere v tycon) -> do
      pure $ (Ext $ AllocateTagHere v tycon)
    Ext (AllocateScalarsHere v) -> do
      pure $ (Ext $ AllocateScalarsHere v)
    Ext (StartTagAllocation v) -> do
      pure $ (Ext $ StartTagAllocation v)
    Ext (EndTagAllocation v) -> do
      pure $ (Ext $ EndTagAllocation v)
    Ext (StartScalarsAllocation v) -> do
      pure $ (Ext $ StartScalarsAllocation v)
    Ext (EndScalarsAllocation v) -> do
      pure $ (Ext $ EndScalarsAllocation v)
    Ext (SSPush _ _ _ _) -> pure ex
    Ext (SSPop _ _ _) -> pure ex
    Ext (Assert e) -> do
      e' <- go e
      pure $ Ext $ Assert e'
    Ext (CastPtr{}) -> pure ex
    Ext (MakeCursorArray{}) -> pure ex
    Ext (IndexCursorArray{}) -> pure ex
    Ext (AddrOfCursor bod) -> do 
                                bod' <- go bod
                                return $ Ext (AddrOfCursor bod')
    MapE {} -> error "addCastsExp: MapE TODO"
    FoldE {} -> error "addCastsExp: FoldE TODO"
  where
    go = removeReDefsExp env