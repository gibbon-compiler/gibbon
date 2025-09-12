module Gibbon.Passes.AddCastInstructions (addCasts) where

import Data.Foldable (foldrM)
import qualified Data.List as L
import qualified Data.Map as M
import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax

-- A map mapping a variable to the casted variable
type CastMapInfo = M.Map Var Var

addCasts :: Prog3 -> PassM Prog3
addCasts Prog {ddefs, fundefs, mainExp} = do
  main' <- case mainExp of
    Just (m, t) -> do
      m' <- addCastsExp Nothing M.empty (Env2 M.empty funEnv) m
      return $ Just (m', t)
    Nothing -> return Nothing
  fds' <- mapM addCastsFunction fundefs
  return $ Prog ddefs fds' main'
  where
    funEnv = M.map funTy fundefs

    addCastsFunction :: FunDef3 -> PassM FunDef3
    addCastsFunction f@FunDef {funTy, funArgs, funBody} = do
      let in_tys = inTys funTy
      let env2 = Env2 (M.fromList $ zip funArgs in_tys) funEnv
      funBody' <- addCastsExp (Just f) M.empty env2 funBody
      return $ f {funBody = funBody'}

addCastsExp :: Maybe FunDef3 -> CastMapInfo -> Env2 Var Ty3 -> Exp3 -> PassM Exp3
addCastsExp fundef cenv env ex =
  case ex of
    LetE (v, locs, ty, rhs@(Ext (IndexCursorArray _ _))) bod -> do
      let new_env = extendVEnv v ty env
      (let_expr, cenv', env') <- case ty of
        CursorTy -> return $ ([LetE (v, locs, ty, rhs)], cenv, new_env)
        CursorArrayTy _ -> do
          casted_var <- gensym "cast"
          let ncenv = M.insert v casted_var cenv
          let cursory_ty3 :: Ty3 = CursorTy
          let nenv = extendVEnv casted_var cursory_ty3 new_env
          let cast_ins = Ext $ CastPtr casted_var ty
          -- let new_inst = [LetE (v, locs, ty, rhs)] ++ [LetE (casted_var, [], CursorTy, cast_ins)]
          let new_inst = [LetE (casted_var, locs, CursorTy, rhs)] ++ [LetE (v, [], ty, cast_ins)]
          pure $ (new_inst, ncenv, nenv)
        _ -> error "addCastsExp: Casting expressions others than cursors hot handled!\n"
      bod' <- addCastsExp fundef cenv' env' bod
      let ex' = foldr (\expr acc -> expr acc) bod' let_expr
      pure $ ex'
      
    LetE (v, locs, ty, rhs@(Ext (AddrOfCursor (Ext (IndexCursorArray _ _)))) ) bod -> do
      let new_env = extendVEnv v ty env
      (let_expr, cenv', env') <- case ty of
        MutCursorTy -> return $ ([LetE (v, locs, ty, rhs)], cenv, new_env) 
        CursorTy -> error "Did not expect lhs of address of expression to be a cursor."
        CursorArrayTy _ -> error "Cannot take address of a CursorArray!\n"
        _ -> error "addCastsExp: Casting expressions others than cursors hot handled!\n"
      bod' <- addCastsExp fundef cenv' env' bod
      let ex' = foldr (\expr acc -> expr acc) bod' let_expr
      pure $ ex'

    LetE (v, locs, ty, (Ext (MakeCursorArray len vars))) bod -> do
      let new_env = extendVEnv v ty env
      (new_insts, cenv', env', vars') <-
        foldrM
          ( \var (insts, fcenv, fenv, nvars) -> do
              let ty_of_var = lookupVEnv var fenv
              case ty_of_var of
                CursorTy -> pure (insts, fcenv, fenv, nvars ++ [var])
                CursorArrayTy _ -> do
                  casted_var <- gensym "cast"
                  let nfcenv = M.insert var casted_var fcenv
                  let cursory_ty3 :: Ty3 = CursorTy
                  let nfenv = extendVEnv casted_var cursory_ty3 fenv
                  let cast_ins = Ext $ CastPtr var cursory_ty3
                  let cast_inst = [LetE (casted_var, [], CursorTy, cast_ins)]
                  pure (insts ++ cast_inst, nfcenv, nfenv, nvars ++ [casted_var])
                _ -> error "Unexpected type!"
          )
          ([], cenv, new_env, [])
          vars
      bod' <- addCastsExp fundef cenv' env' bod
      let ex' = foldr (\expr acc -> expr acc) (LetE (v, locs, ty, (Ext (MakeCursorArray len (L.reverse vars')))) bod') new_insts
      pure $ ex'
    LetE (v, locs, ty, (MkProdE es)) bod -> do
      let new_env = extendVEnv v ty env
      let tys_of_es = case ty of
            ProdTy tys -> tys
            _ -> error $ "addCastsExp: Expected a product type, got " ++ show ty
      (new_insts, cenv', env', vars') <-
        foldrM
          ( \(expr, exp_ty) (insts, fcenv, fenv, fexps) -> do
              case expr of
                VarE var -> do
                  let ty_of_var = lookupVEnv var fenv
                  case ty_of_var of
                    CursorTy -> pure (insts, fcenv, fenv, fexps ++ [VarE var])
                    CursorArrayTy len -> case exp_ty of
                      CursorTy -> do
                        casted_var <- gensym "cast"
                        let nfcenv = M.insert var casted_var fcenv
                        let cursor_ty3 :: Ty3 = CursorTy
                        let nfenv = extendVEnv casted_var cursor_ty3 fenv
                        let cast_ins = Ext $ CastPtr var cursor_ty3
                        let cast_inst = [LetE (casted_var, [], CursorTy, cast_ins)]
                        pure (insts ++ cast_inst, nfcenv, nfenv, fexps ++ [VarE casted_var])
                      CursorArrayTy len' ->
                        if (len /= len')
                          then do
                            casted_var <- gensym "cast"
                            let nfcenv = M.insert var casted_var fcenv
                            let cursor_ty3 :: Ty3 = CursorArrayTy len'
                            let nfenv = extendVEnv casted_var cursor_ty3 fenv
                            let cast_ins = Ext $ CastPtr var cursor_ty3
                            let cast_inst = [LetE (casted_var, [], CursorArrayTy len', cast_ins)]
                            pure (insts ++ cast_inst, nfcenv, nfenv, fexps ++ [VarE casted_var])
                          else
                            pure (insts, fcenv, fenv, fexps ++ [VarE var])
                      _ -> error $ "addCastsExp: Expected a variable, got " ++ show exp_ty
                    _ -> pure (insts, fcenv, fenv, fexps ++ [VarE var]) -- error $ "addCastsExp: Expected a variable, got " ++ show ty_of_var
                _ -> pure (insts, fcenv, fenv, fexps ++ [expr]) -- error "TODO: addCastsExp: not implemented yet!!"
          )
          ([], cenv, new_env, [])
          (zip es tys_of_es)
      bod' <- addCastsExp fundef cenv' env' bod
      let ex' = foldr (\ex acc -> ex acc) (LetE (v, locs, ty, ((MkProdE (L.reverse vars')))) bod') new_insts
      pure $ ex'

    -- LetE (v, locs, ty, rhs@(Ext (AppE f _locs args))) bod -> do
    --     let new_env = extendVEnv v ty env
    --     (new_insts, cenv', env', args')

    LetE (v, locs, _, rhs@(Ext (AddCursor _ _))) bod -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      let env' = extendVEnv v (CursorTy) env
      rhs' <- addCastsExp fundef cenv env' rhs
      bod' <- addCastsExp fundef cenv env' bod
      pure $ (LetE (nv, locs, CursorTy, rhs')) bod'
    -- let nv = case (M.lookup v' cenv) of
    --                     Just v'' -> v''
    --                     Nothing -> v'
    -- let nv_ty = lookupVEnv nv env
    -- e' <- go e
    -- bod' <- addCastsExp fundef cenv env' bod
    -- pure $ (LetE (nv, locs, ty, rhs')) bod'

    -- let ty_v' = lookupVEnv v' env
    -- case (ty == ty_v') of
    --    True -> do
    --            e' <- go e
    --            let env' = extendVEnv v ty env
    --            bod' <- addCastsExp fundef cenv env' bod
    --            pure $ (LetE (v, locs, ty, Ext (AddCursor v' e'))) bod'
    --    False -> do
    --             let nv = case (M.lookup v cenv) of
    --                            Just v'' -> v''
    --                            Nothing -> v
    --             let env' = extendVEnv v ty env
    --             rhs' <- addCastsExp fundef cenv env' rhs
    --             bod' <- addCastsExp fundef cenv env' bod
    --             pure $ (LetE (nv, locs, ty, rhs')) bod'

    LetE (v, locs, ty, rhs) bod -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      let env' = extendVEnv v ty env
      rhs' <- addCastsExp fundef cenv env' rhs
      bod' <- addCastsExp fundef cenv env' bod
      pure $ (LetE (nv, locs, ty, rhs')) bod'
    MkProdE es -> do
      let def = case fundef of
            Just def' -> Just $ funTy def'
            Nothing -> Nothing
      case def of
        Just (_, outTy') -> do
          (new_insts, _, _, vars') <- handleProdTy outTy' ex
          let ex' =
                foldr
                  ( \expr acc -> case expr of
                      LetE (v, locs, ty, rhs) _ -> LetE (v, locs, ty, rhs) acc
                      _ -> error "Did not expect a non-LetE in MkProdE"
                  )
                  (MkProdE (L.reverse vars'))
                  new_insts
          pure $ ex'
        Nothing -> MkProdE <$> mapM go es
    -- MkProdE <$> mapM go es
    ProjE i e -> ProjE i <$> go e
    VarE v -> do
      return $ VarE v
    --    case (M.lookup v cenv) of
    --             Just v' -> pure $ VarE v'
    --             Nothing -> pure $ VarE v
    LitE {} -> pure ex
    CharE {} -> pure ex
    FloatE {} -> pure ex
    LitSymE {} -> pure ex
    AppE f locs args -> AppE f locs <$> mapM go args
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
      let nv = v
      --  let nv = case (M.lookup v cenv) of
      --         Just v' -> v'
      --         Nothing -> v
      pure $ Ext (ReadScalar s nv)
    Ext (WriteScalar s v e) -> do
      let nv = v
      --  let nv = case (M.lookup v cenv) of
      --         Just v' -> v'
      --         Nothing -> v
      e' <- go e
      pure $ Ext (WriteScalar s nv e')
    Ext (ReadTag v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ ReadTag nv)
    Ext (WriteTag dcon v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ WriteTag dcon nv)
    Ext (TagCursor a b) -> do
      let na = case (M.lookup a cenv) of
            Just v' -> v'
            Nothing -> a
      let nb = case (M.lookup b cenv) of
            Just v' -> v'
            Nothing -> b
      pure (Ext $ TagCursor na nb)
    Ext (WriteTaggedCursor v e) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      e' <- go e
      pure (Ext $ WriteTaggedCursor nv e')
    Ext (ReadTaggedCursor v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ ReadTaggedCursor nv)
    Ext (ReadCursor v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ ReadCursor nv)
    Ext (WriteCursor v e) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      e' <- go e
      pure (Ext $ WriteCursor nv e')
    Ext (ReadList v ty) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ ReadList nv ty)
    Ext (WriteList v e ty) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      e' <- go e
      pure (Ext $ WriteList nv e' ty)
    Ext (ReadVector v ty) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure (Ext $ ReadVector nv ty)
    Ext (WriteVector v e ty) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      e' <- go e
      pure (Ext $ WriteVector nv e' ty)
    Ext (AddCursor v e) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      e' <- go e
      pure (Ext $ AddCursor nv e')
    Ext (DerefMutCursor v) -> do 
      let nv = case (M.lookup v cenv) of
            Just v' -> v' 
            Nothing -> v
      pure (Ext $ DerefMutCursor nv)
    Ext (SubPtr a b) -> do
      let na = case (M.lookup a cenv) of
            Just v' -> v'
            Nothing -> a
      let nb = case (M.lookup b cenv) of
            Just v' -> v'
            Nothing -> b
      pure (Ext $ SubPtr na nb)
    Ext (NewBuffer _) -> return ex
    Ext (ScopedBuffer _) -> return ex
    Ext (NewParBuffer _) -> return ex
    Ext (ScopedParBuffer _) -> return ex
    Ext (EndOfBuffer _) -> return ex
    Ext (MMapFileSize v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ Ext (MMapFileSize nv)
    Ext (SizeOfPacked a b) -> do
      let na = case (M.lookup a cenv) of
            Just v' -> v'
            Nothing -> a
      let nb = case (M.lookup b cenv) of
            Just v' -> v'
            Nothing -> b
      pure (Ext $ SizeOfPacked na nb)
    Ext (SizeOfScalar v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ Ext (SizeOfScalar nv)
    Ext (BoundsCheck i a b) -> do
      let na = case (M.lookup a cenv) of
            Just v' -> v'
            Nothing -> a
      let nb = case (M.lookup b cenv) of
            Just v' -> v'
            Nothing -> b
      pure $ Ext (BoundsCheck i na nb)
    Ext (BoundsCheckVector bounds) -> do
      bounds' <-
        mapM
          ( \(i, a, b, (a', b')) -> do
              let na = case (M.lookup a cenv) of
                    Just v' -> v'
                    Nothing -> a
              let nb = case (M.lookup b cenv) of
                    Just v' -> v'
                    Nothing -> b
              let na' = case (M.lookup a' cenv) of
                        Just v' -> v'
                        Nothing -> a'
              let nb' = case (M.lookup b' cenv) of
                        Just v' -> v'
                        Nothing -> b'
              return $ (i, na, nb, (na', nb'))
          )
          bounds
      pure $ Ext (BoundsCheckVector bounds')
    Ext (IndirectionBarrier _ (_, _, _, _)) -> pure ex
    Ext (BumpArenaRefCount _ _) -> pure ex
    Ext NullCursor -> pure ex
    Ext GetCilkWorkerNum -> pure ex
    Ext (AllocateTagHere v tycon) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ AllocateTagHere nv tycon)
    Ext (AllocateScalarsHere v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ AllocateScalarsHere nv)
    Ext (StartTagAllocation v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ StartTagAllocation nv)
    Ext (EndTagAllocation v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ EndTagAllocation nv)
    Ext (StartScalarsAllocation v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ StartScalarsAllocation nv)
    Ext (EndScalarsAllocation v) -> do
      let nv = case (M.lookup v cenv) of
            Just v' -> v'
            Nothing -> v
      pure $ (Ext $ EndScalarsAllocation nv)
    Ext (SSPush _ _ _ _) -> pure ex
    Ext (SSPop _ _ _) -> pure ex
    Ext (Assert e) -> do
      e' <- go e
      pure $ Ext $ Assert e'
    Ext {} -> error $ "addCastsExp : Unexpected instruction " ++ show ex
    MapE {} -> error "addCastsExp: MapE TODO"
    FoldE {} -> error "addCastsExp: FoldE TODO"
  where
    go = addCastsExp fundef cenv env

    handleProdTy :: Ty3 -> Exp3 -> PassM ([Exp3], CastMapInfo, Env2 Var Ty3, [Exp3])
    handleProdTy ty expr = do
      case expr of
        MkProdE es ->
          case ty of
            ProdTy tys -> do
              let zipped = zip es tys
              (new_insts, cenv', env', vars') <-
                foldrM
                  ( \(expr', exp_ty) (insts, fcenv, fenv, fexps) -> do
                      case expr' of
                        VarE var -> do
                          let ty_of_var = lookupVEnv var fenv
                          case ty_of_var of
                            CursorTy -> pure (insts, fcenv, fenv, fexps ++ [VarE var])
                            CursorArrayTy len -> case exp_ty of
                              CursorTy -> do
                                casted_var <- gensym "cast"
                                let nfcenv = M.insert var casted_var fcenv
                                let cursor_ty3 :: Ty3 = CursorTy
                                let nfenv = extendVEnv casted_var cursor_ty3 fenv
                                let cast_ins = Ext $ CastPtr var cursor_ty3
                                let cast_inst = [LetE (casted_var, [], CursorTy, cast_ins) (VarE casted_var)]
                                pure (insts ++ cast_inst, nfcenv, nfenv, fexps ++ [VarE casted_var])
                              CursorArrayTy len' ->
                                if (len /= len')
                                  then do
                                    casted_var <- gensym "cast"
                                    let nfcenv = M.insert var casted_var fcenv
                                    let cursor_ty3 :: Ty3 = CursorArrayTy len'
                                    let nfenv = extendVEnv casted_var cursor_ty3 fenv
                                    let cast_ins = Ext $ CastPtr var cursor_ty3
                                    let cast_inst = [LetE (casted_var, [], CursorArrayTy len', cast_ins) (VarE casted_var)]
                                    pure (insts ++ cast_inst, nfcenv, nfenv, fexps ++ [VarE casted_var])
                                  else
                                    pure (insts, fcenv, fenv, fexps ++ [VarE var])
                              _ -> error $ "addCastsExp: Expected a variable, got " ++ show exp_ty
                            _ -> pure (insts, fcenv, fenv, fexps ++ [VarE var]) -- error $ "addCastsExp: Expected a variable, got " ++ show ty_of_var
                        MkProdE _ -> do
                          res <- handleProdTy exp_ty expr
                          pure res
                        _ -> error "TODO: addCastsExp: not implemented yet!!"
                  )
                  ([], cenv, env, [])
                  zipped
              pure $ (new_insts, cenv', env', vars')
            _ -> error $ "addCastsExp: Expected a product type, got " ++ show ty
        VarE v -> error $ "addCastsExp: Expected a product type, got VarE " ++ show v
        _ -> error $ "addCastsExp: Expected a product type, got " ++ show ty
