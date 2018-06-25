module Gibbon.Passes.AddTraversals
  (addTraversals, needsTraversal) where

import Control.Monad (forM, when)
import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Loc

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Passes.InferEffects (inferExp)
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
      Just (ex,ty) -> Just <$> (,ty) <$> addTraversalsExp ddefs fundefs M.empty "mainExp" ex
      Nothing -> return Nothing
  return prg { ddefs = ddefs
             , fundefs = funs
             , mainExp = mainExp'
             }

addTraversalsFn :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef2
addTraversalsFn ddefs fundefs f@FunDef{funName, funArg, funTy, funBody} =
  if traversesAllInputs
  then return f
  else do
    bod' <- addTraversalsExp ddefs fundefs (M.singleton funArg (arrIn funTy)) (fromVar funName) funBody
    return $ f {funBody = bod'}
  where
    traversesAllInputs = length (L2.inLocVars funTy) == length (S.toList $ L2.arrEffs funTy)

-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty2 -> FunDefs2 -> TyEnv Ty2 -> String -> L Exp2 -> PassM (L Exp2)
addTraversalsExp ddefs fundefs tyenv context (L p ex) = L p <$>
  case ex of
    CaseE scrt brs -> CaseE scrt <$> mapM docase brs

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*>
        addTraversalsExp ddefs fundefs (M.insert v ty tyenv) context bod
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
    go = addTraversalsExp ddefs fundefs tyenv context

    docase (dcon,vlocs,rhs) = do
      let (vars,_locs) = unzip vlocs
          tys    = lookupDataCon ddefs dcon
          tyenv1 = M.union tyenv $ M.fromList (zip vars tys)
          needs_traversal = needsTraversal ddefs fundefs tyenv (dcon,vlocs,rhs)
      case needs_traversal of
        Nothing -> (dcon, vlocs,) <$> go rhs
        Just ls -> do
          dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags

          -- TODO: Move to needsTraversal.
          -- POLICY: We only traverse the first (n-1) packed elements.
          -- However if (n==1), we traverse that element. Need to audit this.
          let trav = if length ls == 1
                     then ls
                     else init ls

          when dump_op $
            dbgTrace 2 ("Adding traversals: " ++ sdoc context) (return ())
          -- Generate traversals: assuming that InferLocs has already generated
          -- the traversal functions, we merely use it here.
          trav_binds <-
            forM trav $ \(p_var, p_loc) -> do
               v <- gensym "trav"
               let ty = tyenv1 # p_var
                   fn_name = mkTravFunName (tyToDataCon ty)
               return $ (v,[],IntTy, l$ AppE fn_name [p_loc] (l$ VarE p_var))
          (dcon,vlocs,) <$> mkLets trav_binds <$>
            addTraversalsExp ddefs fundefs tyenv1 context rhs


-- | Collect all non-static items that need to be traversed (uses InferEffects).
--
-- If we cannot unpack all the pattern matched variables:
-- (1) Everything after the first packed element should be unused in the RHS
-- (2) Otherwise, we must traverse the first (n-1) packed elements
needsTraversal :: DDefs Ty2 -> FunDefs2 -> TyEnv Ty2 -> (DataCon, [(Var, LocVar)], L Exp2) -> Maybe [(Var, LocVar)]
needsTraversal ddefs fundefs tyenv (dcon,vlocs,rhs) =
  let (vars, _locs) = unzip vlocs
      tys     = lookupDataCon ddefs dcon
      tyenv1  = M.fromList (zip vars tys)
      funenv  = M.map funTy fundefs
      (eff,_) = inferExp ddefs funenv (M.union tyenv tyenv1) rhs
      -- Note: Do not change this to use M.filter. It changes the order sometimes.
      packedOnly = L.filter (\(_,b) -> hasPacked b) (zip vars tys)

      effToLoc (Traverse loc_var) = loc_var

      not_traversed = case packedOnly of
                        [] -> []
                        ls -> let locenv = M.fromList vlocs
                                  packedlocs = L.map (\(a,_) -> Traverse (locenv # a)) ls
                                  -- Get the locations of all non-static things which the RHS does not traverse.
                                  -- Note: Using Data.Set changes the order of packedlocs, and we would
                                  -- like to preserve it.
                              in L.map effToLoc $ packedlocs L.\\ (S.toList eff)

   in case L.findIndex isPackedTy tys of
        Nothing -> Nothing
        Just i  -> case not_traversed of
                     [] -> Nothing
                     _ls -> do
                       let -- Why (i+1): findIndex is 0-based, and drop is not
                           should_be_unused = S.fromList $ L.drop (i+1) vars

                           -- LocVar -> Var
                           loc_var_mp = M.fromList $ L.map (\(a,b) -> (b,a)) vlocs

                       -- If the problematic elements are unused, we don't need to add traversals
                       if not (L2.occurs should_be_unused rhs)
                       then Nothing
                       else Just $ L.map (\a -> (loc_var_mp # a, a)) not_traversed
