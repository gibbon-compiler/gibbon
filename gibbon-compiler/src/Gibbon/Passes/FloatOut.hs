{-# LANGUAGE EmptyCase #-}

module Gibbon.Passes.FloatOut
  (floatOut) where

import Control.Monad.State
import Data.Loc
import qualified Data.Map as M
import qualified Data.Set as S

import Gibbon.Common
import Gibbon.Language
import Gibbon.L1.Syntax
import Gibbon.L2.Syntax  (stripTyLocs)

{-|

The Gibbon backend uses Cilk to execute parts of the tuple combinator
in parallel. The Cilk C API only allows us to spawn functions,
not expressions. The idea here is to float out sub-expressions into top-level
functions which can then be 'cilk_spawn'd.

-}
floatOut :: Prog1 -> PassM Prog1
floatOut (Prog ddefs fundefs main) = do
  let env2 = Env2 M.empty (initFunEnv fundefs)
      m = do
        main' <- case main of
                    Nothing -> return Nothing
                    Just (e,ty) -> Just <$> (,ty) <$> floatOutExp ddefs env2 e
        fds <- mapM (floatOutFn ddefs env2) $ M.elems fundefs
        let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds
        return (Prog ddefs fundefs' main')
  (prg,fundefs1) <- runFloatOutM fundefs m
  return prg { fundefs = fundefs1}

type FloatOutM a = StateT FunDefs1 PassM a

runFloatOutM :: FunDefs1 -> FloatOutM a -> PassM (a, FunDefs1)
runFloatOutM fdefs a = runStateT a fdefs

floatOutFn :: DDefs Ty1 -> Env2 Ty1 -> FunDef1 -> FloatOutM FunDef1
floatOutFn ddefs env2 f@FunDef{funArgs,funTy,funBody} = do
  let env2' = extendsVEnv (M.fromList $ zip funArgs (inTys funTy)) env2
  bod' <- floatOutExp ddefs env2' funBody
  return $ f { funBody = bod' }

floatOutExp :: DDefs Ty1 -> Env2 Ty1 -> L Exp1 -> FloatOutM (L Exp1)
floatOutExp ddefs env2 (L p ex) = (L p) <$>
  case ex of
    ParE a b -> do
     (bnds1, a') <- dopar a
     (bnds2, b') <- dopar b
     return $ unLoc $ mkLets (bnds1 ++ bnds2) (l$ ParE a' b')

    -- standard recursion here
    VarE{} -> return ex
    LitE{} -> return ex
    LitSymE{}  -> return ex
    AppE{}     -> return ex
    PrimAppE{} -> return ex
    LetE (v,locs,ty,rhs) bod -> do
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        floatOutExp ddefs (extendVEnv v ty env2) bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    ProjE i e  -> ProjE i <$> go e
    CaseE scrt brs -> CaseE scrt <$> mapM docase brs
    DataConE loc dcon ls -> DataConE loc dcon <$> mapM go ls
    TimeIt e ty b -> do
      e' <- go e
      return (TimeIt e' ty b)
    WithArenaE v e -> WithArenaE v <$> go e
    Ext ext -> case ext of {}
    MapE{}  -> error "floatOutExp: TODO MapE"
    FoldE{} -> error "floatOutExp: TODO MapE"
  where
    go = floatOutExp ddefs env2

    docase (dcon,vlocs,rhs) = do
      let vars  = map fst vlocs
          tys   = map stripTyLocs (lookupDataCon ddefs dcon)
          env21 = extendsVEnv (M.fromList (zip vars tys)) env2
      (dcon,vlocs,) <$> floatOutExp ddefs env21 rhs


    dopar :: L Exp1 -> FloatOutM ([(Var,[()],Ty1,L Exp1)], L Exp1)
    dopar (L p1 e) = do
      case e of
        AppE{} -> return ([], L p1 e)
        _ -> do
          let free_vars = S.toList (gFreeVars e)
              intys = map (\v -> lookupVEnv v env2) free_vars
              retty = gRecoverType ddefs env2 (L p e)
          var <- lift $ gensym "float_out_arg"
          funarg <- lift $ gensym "arg"
          funname <- lift $ gensym "float_out_fn"
          let fn = FunDef { funName = funname
                          -- TODO:CSK Check this
                          , funArgs = [funarg]
                          , funTy   = ([ProdTy intys], retty)
                          , funBody = mkLets [ (v,[],ty,mkProj idx (l$ VarE funarg))
                                             | ((v,ty), idx) <- (zip (zip free_vars intys) [0..])]
                                      (L p e)
                          }
          fdefs <- get
          put (M.insert funname fn fdefs)
          return ([(var,[],ProdTy intys,l$ MkProdE [ (l$ VarE v) | v <- free_vars])],
                  L p1 $ AppE funname [] [l$ VarE var])
