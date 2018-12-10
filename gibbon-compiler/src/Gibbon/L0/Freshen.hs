-- When the pipeline is ready, this will take the place of 'Gibbon.Passes.Freshen'.
module Gibbon.L0.Freshen
  ( freshNames ) where

import           Control.Exception
import           Data.Loc
import           Prelude hiding (exp)
import           Data.List
import qualified Data.Map as M

import           Gibbon.Common
import           Gibbon.L0.Syntax

--------------------------------------------------------------------------------

type VarEnv   = M.Map Var Var
type TyVarEnv = M.Map TyVar TyVar


{-|

Freshen term and type variables, and check if tyvars are used properly.
Support lexically scoped type variables, so that we can give type annotations
to all let bound terms. Consider this (slightly contrived) program:

    ($) :: (a -> b) -> a -> b
    ($) f x = let g :: (a -> b)
                  g = f
              in g x

is renamed to:

   ($) :: (a0 -> b1) -> a0 -> b1
   ($) f2 x3 = let g4 :: (a0 -> b1)
                   g4 = f2
               in g4 x3

See "L0.Typecheck" for more details.

-}
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
  tyArgs' <- mapM gensym tyArgs
  let env = M.fromList (zip tyArgs tyArgs')
      dataCons' = map (\(dcon,vs) -> (dcon, map (go env) vs)) dataCons
  pure (DDef tyName tyArgs' dataCons')
  where
    go env (b, ty) = (b, freshTy env ty)

freshFun :: FunDef (L Exp0) -> PassM (FunDef (L Exp0))
freshFun (FunDef nam narg funty bod) =
    do narg' <- gensym narg
       (tyenv, funty') <- freshTyScheme funty
       bod' <- freshExp (M.singleton narg narg') tyenv bod
       let nam' = cleanFunName nam
       pure $ FunDef nam' narg' funty' bod'

freshTyScheme :: TyScheme -> PassM (TyVarEnv, TyScheme)
freshTyScheme (ForAll tvs ty) = do
  tvs' <- mapM gensym tvs
  let env = M.fromList (zip tvs tvs')
      ty' = freshTy env ty
  pure (env, ForAll tvs' ty')

freshTy :: TyVarEnv -> Ty0 -> Ty0
freshTy env ty =
  case ty of
     IntTy  -> IntTy
     BoolTy -> BoolTy
     TyVar tv -> case M.lookup tv env of
                   Nothing  -> error $ "freshTy: Unbound type variable " ++ show tv
                   Just tv' -> TyVar tv'
     ProdTy tys    -> ProdTy $ map go tys
     SymDictTy t   -> SymDictTy $ go t
     ArrowTy t1 t2 -> ArrowTy (go t1) (go t2)
     PackedTy tycon t -> PackedTy tycon $ map go t
     ListTy t -> ListTy (go t)
  where go = freshTy env

freshExp :: VarEnv -> TyVarEnv -> L Exp0 -> PassM (L Exp0)
freshExp venv tyenv (L sloc exp) = fmap (L sloc) $
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

    LetE (v,ls,ty, e1) e2 -> assert ([]==ls) $ do
      -- Freshen type variables free in 'ty' wrt 'tyenv',
      -- a.k.a. ScopedTypeVariables.
      let free_tyvars = tyVarsInType ty \\ M.keys tyenv
      tyenv' <- M.fromList <$> mapM (\x -> (x, ) <$> gensym x) free_tyvars
      let ty' = freshTy (tyenv <> tyenv') ty

      v'  <- gensym v
      -- N.B. If rhs is a lambda, we need to freshen it with a tyenv which
      -- binds all its free type variables.
      e1' <- freshExp venv tyenv' e1
      e2' <- freshExp (M.insert v v' venv) tyenv e2
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
                     let (args,_) = unzip prs
                     args' <- mapM gensym args
                     let venv' = M.fromList (zip args args') `M.union` venv
                     ae' <- freshExp venv' tyenv ae
                     return (c, map (,()) args', ae')) mp
      return $ CaseE e' mp'

    DataConE () c es -> do
      es' <- mapM go es
      return $ DataConE () c es'

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
              ty'   = freshTy tyenv ty
          Ext <$> (LambdaE (v',ty') <$> (freshExp venv' tyenv bod))
        PolyAppE{} -> error "freshExp: TODO, PolyAppE."

  where go = freshExp venv tyenv
