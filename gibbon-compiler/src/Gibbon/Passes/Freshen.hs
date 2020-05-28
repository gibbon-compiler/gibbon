{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}

-- | Unique names.

module Gibbon.Passes.Freshen (freshNames, freshExp, freshExp1) where

import           Control.Exception
import           Data.Foldable ( foldrM )
import           Prelude hiding (exp)
import           Data.List
import qualified Data.Map as M

import           Gibbon.Common
import           Gibbon.L0.Syntax
import qualified Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

type VarEnv     = M.Map Var Var
type TyVarEnv t = M.Map TyVar t

freshNames :: Prog0 -> PassM Prog0
freshNames (Prog defs funs main) =
    do main' <- case main of
                  Nothing -> return Nothing
                  Just (m,ty) -> do m' <- freshExp M.empty M.empty m
                                    return $ Just (m',ty)
       defs' <- traverse freshDDef defs
       funs' <- M.mapKeys cleanFunName <$> traverse freshFun funs
       return $ Prog defs' funs' main'

freshDDef :: DDef Ty0 -> PassM (DDef Ty0)
freshDDef DDef{tyName,tyArgs,dataCons} = do
  rigid_tyvars <- mapM (\(UserTv v) -> BoundTv <$> gensym v) tyArgs
  let env :: TyVarEnv Ty0
      env = M.fromList $ zip tyArgs (map TyVar rigid_tyvars)
  dataCons' <- mapM (\(dcon,vs) -> (dcon,) <$> mapM (go (sdoc (dcon,vs)) rigid_tyvars env) vs) dataCons
  pure (DDef tyName rigid_tyvars dataCons')
  where
    go :: String -> [TyVar] -> TyVarEnv Ty0 -> (t, Ty0) -> PassM (t, Ty0)
    go msg bound env (b, ty) = do
      (_, ty') <- freshTy env ty
      let free_tvs = tyVarsInTy ty' \\ bound
      if free_tvs == []
      then pure (b, ty')
      else error $ "freshDDef: Unbound type variables " ++ sdoc free_tvs
                   ++ " in the constructor:\n" ++ msg

freshFun :: FunDef Exp0 -> PassM (FunDef Exp0)
freshFun (FunDef nam nargs funty bod) =
    do nargs' <- mapM gensym nargs
       let msubst = (M.fromList $ zip nargs nargs')
       (tvenv, funty') <- freshTyScheme funty
       funty'' <- freshDictTyScheme msubst funty'
       bod' <- freshExp msubst tvenv bod
       let nam' = cleanFunName nam
       pure $ FunDef nam' nargs' funty'' bod'

--
freshTyScheme :: TyScheme -> PassM (TyVarEnv Ty0, TyScheme)
freshTyScheme (ForAll tvs ty) = do
  rigid_tyvars <- mapM (\(UserTv v) -> BoundTv <$> gensym v) tvs
  let env = M.fromList $ zip tvs (map TyVar rigid_tyvars)
  (env', ty') <- freshTy env ty
  pure (env', ForAll rigid_tyvars ty')

freshTy :: TyVarEnv Ty0 -> Ty0 -> PassM (TyVarEnv Ty0, Ty0)
freshTy env ty =
  case ty of
     IntTy    -> pure (env, ty)
     FloatTy  -> pure (env, ty)
     SymTy0   -> pure (env, ty)
     BoolTy   -> pure (env, ty)
     ArenaTy  -> pure (env, ty)
     SymSetTy -> pure (env, ty)
     SymHashTy -> pure (env, ty)
     TyVar tv -> case M.lookup tv env of
                   Nothing  -> do tv' <- newTyVar
                                  pure (env, TyVar tv')
                   Just tv' -> pure (env, tv')
     MetaTv{} -> pure (env, ty)
     ProdTy tys    -> do (env', tys') <- freshTys env tys
                         pure (env', ProdTy tys')
     SymDictTy v t   -> do (env', t') <- freshTy env t
                           pure (env', SymDictTy v t')
     ArrowTy tys t -> do (env', tys') <- freshTys env tys
                         (env'', [t'])  <- freshTys env' [t]
                         pure (env'', ArrowTy tys' t')
     PackedTy tycon tys -> do (env', tys') <- freshTys env tys
                              pure (env', PackedTy tycon tys')
     VectorTy el_t -> do (env', el_t') <- freshTy env el_t
                         pure (env', VectorTy el_t')
     IntHashTy -> pure (env, ty)

freshTys :: TyVarEnv (TyOf Exp0) -> [Ty0] -> PassM (TyVarEnv (TyOf Exp0), [Ty0])
freshTys env tys =
  foldrM
    (\t (env', acc) -> do
          (env'', t') <- freshTy env' t
          pure (env' <> env'', t' : acc))
    (env, [])
    tys

freshDictTy :: Monad m => M.Map Var Var -> Ty0 -> m Ty0
freshDictTy m ty =
    case ty of
     IntTy    -> pure ty
     FloatTy  -> pure ty
     SymTy0   -> pure ty
     BoolTy   -> pure ty
     ArenaTy  -> pure ty
     TyVar _tv -> pure ty
     MetaTv{}  -> pure ty
     ProdTy tys ->
         do tys' <- mapM (freshDictTy m) tys
            pure (ProdTy tys')
     SymDictTy (Just v) t   ->
         do t' <- freshDictTy m t
            case M.lookup v m of
              Just v' -> pure $ SymDictTy (Just v') t'
              Nothing -> pure ty
     SymDictTy Nothing t ->
         do t' <- freshDictTy m t
            pure $ SymDictTy Nothing t'
     ArrowTy tys t ->
         do tys' <- mapM (freshDictTy m) tys
            t' <- freshDictTy m t
            pure $ ArrowTy tys' t'
     PackedTy tycon tys ->
         do tys' <- mapM (freshDictTy m) tys
            pure $ PackedTy tycon tys'
     VectorTy el_t ->
         do el_t' <- freshDictTy m el_t
            pure $ VectorTy el_t'
     SymSetTy  -> error "freshDictTy: SymSetTy not handled."
     SymHashTy -> error "freshDictTy: SymHashTy not handled."
     IntHashTy -> error "freshDictTy: IntHashTy not handled."

freshDictTyScheme :: Monad m =>
                     M.Map Var Var -> TyScheme -> m TyScheme
freshDictTyScheme m (ForAll tvs ty) =
    do ty' <- freshDictTy m ty
       pure $ ForAll tvs ty'

freshExp :: VarEnv -> TyVarEnv Ty0 -> Exp0 -> PassM Exp0
freshExp venv tvenv exp =
  case exp of
    LitE i    -> return $ LitE i
    FloatE i  -> return $ FloatE i
    LitSymE v -> return $ LitSymE v

    VarE v ->
      case M.lookup v venv of
        Nothing -> return $ VarE (cleanFunName v)
        Just v' -> return $ VarE (cleanFunName v')

    AppE v locs ls -> assert ([] == locs) $ do
      ls' <- mapM go ls
      case M.lookup v venv of
        Nothing -> return $ AppE (cleanFunName v) [] ls'
        Just v' -> return $ AppE (cleanFunName v') [] ls'

    PrimAppE p es -> do
      es' <- mapM go es
      return $ PrimAppE p es'

    LetE (v,_locs,ty, e1) e2 -> do
      let user_tvs  = filter isUserTv $ tyVarsInTy ty
      rigid_tyvars <- mapM (\(UserTv w) -> BoundTv <$> gensym w) user_tvs
      let env = M.fromList $ zip user_tvs (map TyVar rigid_tyvars)
          tvenv' = env <> tvenv

      (_tvenv'', ty') <- freshTy tvenv' ty
      e1' <- freshExp venv tvenv' e1
      v'  <- gensym (cleanFunName v)
      e2' <- freshExp (M.insert v v' venv) tvenv e2
      ty'' <- case ty' of
                SymDictTy (Just w) ty2 -> case M.lookup w venv of
                                            Nothing -> return ty'
                                            Just w' -> return $ SymDictTy (Just w') ty2
                _ -> return ty'
      return $ LetE (v',[],ty'',e1') e2'

    IfE e1 e2 e3 -> do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ IfE e1' e2' e3'

    ProjE i e -> do
      e' <- go e
      return $ ProjE i e'

    MkProdE es -> do
      es' <- mapM go es
      return $ MkProdE es'

    CaseE e mp -> do
      e' <- go e
      mp' <- mapM (\(c,prs,ae) -> do
                     let (args,locs) = unzip prs
                     args' <- mapM gensym args
                     let venv' = M.fromList (zip args args') `M.union` venv
                     ae' <- freshExp venv' tvenv ae
                     return (c, zip args' locs, ae')) mp
      return $ CaseE e' mp'

    DataConE loc c es -> do
      es' <- mapM go es
      return $ DataConE loc c es'

    TimeIt e t b -> do
      e' <- go e
      return $ TimeIt e' t b

    WithArenaE v e -> do
      v' <- gensym v
      e' <- freshExp (M.insert v v' venv) tvenv e
      return $ WithArenaE v' e'

    SpawnE v locs ls -> assert ([] == locs) $ do
      ls' <- mapM go ls
      case M.lookup v venv of
        Nothing -> return $ SpawnE (cleanFunName v) [] ls'
        Just v' -> return $ SpawnE (cleanFunName v') [] ls'

    SyncE -> pure SyncE

    MapE (v,t,b) e -> do
      b' <- go b
      e' <- go e
      return $ MapE (v,t,b') e'

    FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ FoldE (v1,t1,e1') (v2,t2,e2') e3'

    -- Ext ext -> Ext <$> gFreshenExp venv tvenv ext

    Ext ext ->
      case ext of
        LambdaE args bod -> do
          (venv', vs, ts) <- foldrM
                               (\(v,t) (acc1, acc2, acc3) -> do
                                     v' <- gensym v
                                     let acc1' = M.insert v v' acc1
                                     (_tvenv', t') <- freshTy tvenv t
                                     pure (acc1', v':acc2, t': acc3))
                               (venv,[],[]) args
          Ext <$> (LambdaE (zip vs ts) <$> (freshExp venv' tvenv bod))
        FunRefE tyapps f ->
          case M.lookup f venv of
            Nothing -> pure $ Ext $ FunRefE tyapps (cleanFunName f)
            Just f' -> pure $ Ext $ FunRefE tyapps (cleanFunName f')
        PolyAppE{} -> error "freshExp: TODO, PolyAppE."

        BenchE fn tyapps args b -> do
          args' <- mapM go args
          pure $ Ext (BenchE (cleanFunName fn) tyapps args' b)

        ParE0 ls -> Ext <$> ParE0 <$> mapM go ls
        L p e    -> Ext <$> (L p) <$> go e

  where go = freshExp venv tvenv


-- copy-paste.
freshExp1 :: VarEnv -> L1.Exp1 -> PassM L1.Exp1
freshExp1 vs exp =
  case exp of
    LitE i    -> return $ LitE i
    FloatE i  -> return $ FloatE i
    LitSymE v -> return $ LitSymE v

    VarE v ->
      case M.lookup v vs of
        Nothing -> return $ VarE v
        Just v' -> return $ VarE v'

    AppE v locs ls -> assert ([] == locs) $ do
      ls' <- mapM (freshExp1 vs) ls
      case M.lookup v vs of
        Nothing -> return $ AppE (cleanFunName v) [] ls'
        Just v' -> return $ AppE (cleanFunName v') [] ls'

    PrimAppE p es -> do
      es' <- mapM (freshExp1 vs) es
      return $ PrimAppE p es'

    LetE (v,locs,t, e1) e2 -> assert ([]==locs) $ do
     e1' <- freshExp1 vs e1
     v'  <- gensym v
     e2' <- freshExp1 (M.insert v v' vs) e2
     return $ LetE (v',[],t,e1') e2'

    IfE e1 e2 e3 -> do
      e1' <- freshExp1 vs e1
      e2' <- freshExp1 vs e2
      e3' <- freshExp1 vs e3
      return $ IfE e1' e2' e3'

    ProjE i e -> do
      e' <- freshExp1 vs e
      return $ ProjE i e'

    MkProdE es -> do
      es' <- mapM (freshExp1 vs) es
      return $ MkProdE es'

    CaseE e mp -> do
      e' <- freshExp1 vs e
      -- Here we freshen locations:
      mp' <- mapM (\(c,prs,ae) ->
                   let (args,_) = unzip prs in
                   do
                     args' <- mapM gensym args
                     let vs' = (M.fromList $ zip args args') `M.union` vs
                     ae' <- freshExp1 vs' ae
                     return (c, map (,()) args', ae')) mp
      return $ CaseE e' mp'

    DataConE () c es -> do
      es' <- mapM (freshExp1 vs) es
      return $ DataConE () c es'

    TimeIt e t b -> do
      e' <- freshExp1 vs e
      return $ TimeIt e' t b

    SpawnE v locs ls -> assert ([] == locs) $ do
      ls' <- mapM (freshExp1 vs) ls
      case M.lookup v vs of
        Nothing -> return $ SpawnE (cleanFunName v) [] ls'
        Just v' -> return $ SpawnE (cleanFunName v') [] ls'

    SyncE -> pure SyncE

    MapE (v,t,b) e -> do
      b' <- freshExp1 vs b
      e' <- freshExp1 vs e
      return $ MapE (v,t,b') e'

    FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
      e1' <- freshExp1 vs e1
      e2' <- freshExp1 vs e2
      e3' <- freshExp1 vs e3
      return $ FoldE (v1,t1,e1') (v2,t2,e2') e3'

    WithArenaE{} -> error "freshExp1: WithArenaE not handled."

    Ext (L1.BenchE fn tyapps args b) -> do
      args' <- mapM (freshExp1 vs) args
      pure $ Ext (L1.BenchE (cleanFunName fn) tyapps args' b)

    Ext (L1.AddFixed{}) -> error "freshExp1: AddFixed not handled."
