module Gibbon.Passes.AddTraversals
  (addTraversals) where

import Data.Set as S
import Data.Map as M
import Data.List as L
import Data.Loc

import Gibbon.Common
import Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

-- |
addTraversals :: S.Set Var -> Prog1 -> PassM Prog1
addTraversals unsafeFns prg@Prog{ddefs,fundefs,mainExp} =
  dbgTrace 5 ("AddTraversals: Fixing functions:" ++ sdoc (S.toList unsafeFns)) <$> do
    funs <- mapM (\(nm,f) -> (nm,) <$> addTraversalsFn unsafeFns ddefs f) (M.toList fundefs)
    mainExp' <-
      case mainExp of
        Just (ex,ty) -> Just <$> (,ty) <$> addTraversalsExp ddefs ex
        Nothing -> return Nothing
    return prg { ddefs = ddefs
               , fundefs = M.fromList funs
               , mainExp = mainExp'
               }


-- Process body and reset traversal effects.
addTraversalsFn :: S.Set Var -> DDefs Ty1 -> L1.FunDef1 -> PassM L1.FunDef1
addTraversalsFn unsafeFns ddefs f@FunDef{funName, funBody} =
  if funName `S.member` unsafeFns
  then do
    bod' <- addTraversalsExp ddefs funBody
    return $ f {funBody = bod'}
  else return f

-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty1-> L Exp1 -> PassM (L Exp1)
addTraversalsExp ddefs (L p ex) = L p <$>
  case ex of
    CaseE scrt brs -> CaseE scrt <$> mapM docase brs

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> go bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    DataConE{} -> return ex
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    Ext _ -> return ex
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addTraversalsExp ddefs
    docase (dcon,vlocs,rhs) = do
      let tys = lookupDataCon ddefs dcon
          (vars,_) = unzip vlocs
          -- First (n-1) packed elements
          packedOnly = L.filter (\(_,ty) -> isPackedTy ty) (zip vars tys)
      case packedOnly of
        [] -> (dcon,vlocs,) <$> go rhs
        _ -> do
          let ls = init packedOnly
          travbinds <- mapM (\(v,ty) -> do
                               let PackedTy dc _ = ty
                                   copyfn = mkCopyFunName dc
                               v' <- gensym v
                               return (v',[], ty, l$ AppE copyfn [] (l$ VarE v)))
                       ls
          (dcon,vlocs,) <$> mkLets travbinds <$> go rhs
