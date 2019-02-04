-- When the pipeline is ready, this will take the place of 'Gibbon.Passes.Freshen'.
module Gibbon.L0.Freshen
  ( freshNames ) where

import           Control.Exception
import           Data.Foldable ( foldrM )
import           Data.Loc
import           Prelude hiding (exp)
import           Data.List
import qualified Data.Map as M

import           Gibbon.Common
import           Gibbon.L0.Syntax

--------------------------------------------------------------------------------

type VarEnv   = M.Map Var Var
type TyVarEnv = M.Map TyVar Ty0


-- TODO: ScopedTypeVariables.
freshNames :: Prog0 -> PassM Prog0
freshNames (Prog defs funs main) =
    do main' <- case main of
                  Nothing -> return Nothing
                  Just (m,ty) -> do m' <- freshExp M.empty M.empty m
                                    return $ Just (m',ty)
       defs' <- traverse freshDDef defs
       funs' <- traverse freshFun funs
       return $ Prog defs' funs' main'

freshDDef :: DDef Ty0 -> PassM (DDef Ty0)
freshDDef DDef{tyName,tyArgs,dataCons} = do
  rigid_tyvars <- mapM (\(UserTv v) -> BoundTv <$> gensym v) tyArgs
  let env = M.fromList $ zip tyArgs (map TyVar rigid_tyvars)
  dataCons' <- mapM (\(dcon,vs) -> (dcon,) <$> mapM (go (sdoc (dcon,vs)) rigid_tyvars env) vs) dataCons
  pure (DDef tyName rigid_tyvars dataCons')
  where
    go :: String -> [TyVar] -> TyVarEnv -> (t, Ty0) -> PassM (t, Ty0)
    go msg bound env (b, ty) = do
      (_, ty') <- freshTy env ty
      let free_tvs = tyVarsInTy ty' \\ bound
      if free_tvs == []
      then pure (b, ty')
      else error $ "freshDDef: Unbound type variables " ++ sdoc free_tvs
                   ++ " in the constructor:\n" ++ msg

freshFun :: FunDef (L Exp0) -> PassM (FunDef (L Exp0))
freshFun (FunDef nam narg funty bod) =
    do narg' <- gensym narg
       (tvenv, funty') <- freshTyScheme funty
       bod' <- freshExp (M.singleton narg narg') tvenv bod
       let nam' = cleanFunName nam
       pure $ FunDef nam' narg' funty' bod'

--
freshTyScheme :: TyScheme -> PassM (TyVarEnv, TyScheme)
freshTyScheme (ForAll tvs ty) = do
  rigid_tyvars <- mapM (\(UserTv v) -> BoundTv <$> gensym v) tvs
  let env = M.fromList $ zip tvs (map TyVar rigid_tyvars)
  (env', ty') <- freshTy env ty
  pure (env', ForAll rigid_tyvars ty')

freshTy :: TyVarEnv -> Ty0 -> PassM (TyVarEnv, Ty0)
freshTy env ty =
  case ty of
     IntTy  -> pure (env, ty)
     SymTy0 -> pure (env, ty)
     BoolTy -> pure (env, ty)
     TyVar tv -> case M.lookup tv env of
                   Nothing  -> do tv' <- newTyVar
                                  pure (env, TyVar tv')
                   Just tv' -> pure (env, tv')
     MetaTv{} -> pure (env, ty)
     ProdTy tys    -> do (env', tys') <- freshTys env tys
                         pure (env', ProdTy tys')
     SymDictTy t   -> do (env', t') <- freshTy env t
                         pure (env', SymDictTy t')
     ArrowTy t1 t2 -> do (env', [t1', t2']) <- freshTys env [t1,t2]
                         pure (env', ArrowTy t1' t2')
     PackedTy tycon tys -> do (env', tys') <- freshTys env tys
                              pure (env', PackedTy tycon tys')
     ListTy t -> do (env', t') <- freshTy env t
                    pure (env', ListTy t')

freshTys :: TyVarEnv -> [Ty0] -> PassM (TyVarEnv, [Ty0])
freshTys env tys =
  foldrM
    (\t (env', acc) -> do
          (env'', t') <- freshTy env' t
          pure (env' <> env'', t' : acc))
    (env, [])
    tys

freshExp :: VarEnv -> TyVarEnv -> L Exp0 -> PassM (L Exp0)
freshExp venv tvenv (L sloc exp) = fmap (L sloc) $
  case exp of
    LitE i    -> return $ LitE i
    LitSymE v -> return $ LitSymE v

    VarE v ->
      case M.lookup v venv of
        Nothing -> return $ VarE v
        Just v' -> return $ VarE v'

    AppE v ls e -> assert ([] == ls) $ do
      e' <- go e
      -- If this is a call site of a let bound lambda, we need to update it.
      case M.lookup v venv of
        Nothing -> return $ AppE (cleanFunName v) [] e'
        Just v' -> return $ AppE v' [] e'

    PrimAppE p es -> do
      es' <- mapM go es
      return $ PrimAppE p es'

    LetE (v,_locs,ty, e1) e2 -> do
      -- No ScopedTypeVariables.
      (_tvenv', ty') <- freshTy tvenv ty
      e1' <- freshExp venv tvenv e1
      v'  <- gensym v
      e2' <- freshExp (M.insert v v' venv) tvenv e2
      return $ LetE (v',[],ty',e1') e2'

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

    ParE a b -> do
      ParE <$> go a <*> go b

    MapE (v,t,b) e -> do
      b' <- go b
      e' <- go e
      return $ MapE (v,t,b') e'

    FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ FoldE (v1,t1,e1') (v2,t2,e2') e3'

    Ext ext ->
      case ext of
        LambdaE (v,ty) bod -> do
          v' <- gensym v
          let venv' = M.insert v v' venv
          (_tvenv', ty') <- freshTy tvenv ty
          Ext <$> (LambdaE (v',ty') <$> (freshExp venv' tvenv bod))
        PolyAppE{} -> error "freshExp: TODO, PolyAppE."

  where go = freshExp venv tvenv
