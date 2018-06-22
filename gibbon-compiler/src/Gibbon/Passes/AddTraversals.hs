module Gibbon.Passes.AddTraversals
  (addTraversals) where

import Control.Monad (forM)
import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Loc

import Gibbon.Passes.InferEffects (inferExp)
import Gibbon.Common
import Gibbon.L1.Syntax as L1
import Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

{- Note [Adding dummy traversals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-}

addTraversals :: Prog2 -> PassM Prog2
addTraversals prg@Prog{ddefs,fundefs,mainExp} = do
  funs <- mapM (addTraversalsFn ddefs fundefs) fundefs
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addTraversalsExp ddefs fundefs M.empty ex
      Nothing -> return Nothing
  return prg { ddefs = ddefs
             , fundefs = funs
             , mainExp = mainExp'
             }

addTraversalsFn :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef2
addTraversalsFn ddefs fundefs f@FunDef{funArg, funTy, funBody} =
  if traversesAllInputs
  then return f
  else do
    bod' <- addTraversalsExp ddefs fundefs (M.singleton funArg (arrIn funTy)) funBody
    return $ f {funBody = bod'}
  where
    traversesAllInputs = length (L2.inLocVars funTy) == length (S.toList $ L2.arrEffs funTy)


-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty2 -> FunDefs2 -> TyEnv Ty2 -> L Exp2 -> PassM (L Exp2)
addTraversalsExp ddefs fundefs tyenv (L p ex) = L p <$>
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
    Ext ext ->
      case ext of
        LetRegionE reg bod -> Ext <$> LetRegionE reg <$> go bod
        LetLocE loc locexp bod -> Ext <$> LetLocE loc locexp <$> go bod
        _ -> return ex
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addTraversalsExp ddefs fundefs tyenv

    -- If this case expression cannot unpack all the pattern matched variables:
    -- (1) Everything after the first packed element should be unused in the RHS
    -- (2) Otherwise, we must traverse the first (n-1) packed elements
    docase (dcon,vlocs,rhs) = do
      let (vars, _locs) = unzip vlocs
          tys    = lookupDataCon ddefs dcon
          v_tys  = zip vars tys
          fenv   = M.map funTy fundefs
          (eff,_)= inferExp ddefs fenv (M.union tyenv (M.fromList v_tys)) rhs
          effToLoc (Traverse loc_var) = loc_var
          packedOnly = L.filter (\(_,t) -> hasPacked t) v_tys

          -- Collect all non-static items that were not traversed
          -- (related: InferEffects)
          notTraversed =
            case packedOnly of
              [] -> []
              ls -> let patVMap = M.fromList vlocs
                        packedlocs = L.map (\(a,_) -> Traverse (patVMap # a)) ls
                    -- Using Data.Set changes the order of packedlocs, and we would
                    -- like to preserve it.
                    in L.map effToLoc $ packedlocs L.\\ (S.toList eff)

      case L.findIndex isPackedTy tys of
        Nothing -> (dcon, vlocs,) <$> go rhs
        Just i  -> case notTraversed of
                     -- All the packed elements were traversed
                     [] -> (dcon, vlocs,) <$> go rhs
                     _ls -> do
                       -- Why (i+1): findIndex is 0-based, and drop is not
                       let should_be_unused = S.fromList $ L.drop (i+1) vars
                       -- If the problematic elements are unused, we don't need
                       -- to add traversals
                       if not (L2.occurs should_be_unused rhs)
                       then (dcon,vlocs,) <$> go rhs
                       -- Otherwise, traverse.
                       else do
                         let loc_map = M.fromList $ L.map (\(a,b) -> (b,a)) vlocs
                         trav_binds <-
                           forM notTraversed $ \p_loc -> do
                              v <- gensym "trav"
                              let p_var = loc_map # p_loc
                                  ty = (M.fromList v_tys) # p_var
                                  fn_name = mkTravFunName (tyToDataCon ty)
                              return $ (v,[],IntTy, l$ AppE fn_name [p_loc] (l$ VarE p_var))
                         (dcon,vlocs,) <$> mkLets trav_binds <$> go rhs
