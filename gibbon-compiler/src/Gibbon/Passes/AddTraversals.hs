module Gibbon.Passes.AddTraversals
  (addTraversals, needsTraversalCase) where

import Control.Monad ( forM, when )
import qualified Data.List as L
import Data.Map as M
import Data.Set as S

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Passes.InferEffects ( inferExp )
import Gibbon.L1.Syntax hiding (StartOfPkdCursor)
import Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

{- Note [Adding dummy traversals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

..TODO..

-}

type Deps = M.Map LocVar LocVar

-- Maps a location to a region
type RegEnv = M.Map LocVar Var

addTraversals :: Prog2 -> PassM Prog2
addTraversals prg@Prog{ddefs,fundefs,mainExp} = do
  funs <- mapM (addTraversalsFn ddefs fundefs) fundefs
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addTraversalsExp ddefs fundefs emptyEnv2 M.empty "mainExp" ex
      Nothing -> return Nothing
  return prg { ddefs = ddefs
             , fundefs = funs
             , mainExp = mainExp'
             }

addTraversalsFn :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef2
addTraversalsFn ddefs fundefs f@FunDef{funName, funArgs, funTy, funBody} = do
    let inlocs = inLocVars funTy
        eff = arrEffs funTy
    if S.null ((S.fromList inlocs) `S.difference` (S.map (\(Traverse v) -> v) eff)) && not (hasParallelism funTy)
      then return f
      else do
        let funenv = initFunEnv fundefs
            tyenv = M.fromList $ fragileZip funArgs (inTys funTy)
            env2 = Env2 tyenv funenv
            renv = M.fromList $ L.map (\lrm -> (lrmLoc lrm, regionToVar (lrmReg lrm)))
                                      (locVars funTy)
        bod' <- addTraversalsExp ddefs fundefs env2 renv (fromVar funName) funBody
        return $ f {funBody = bod'}

-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty2 -> FunDefs2 -> Env2 Var Ty2 -> RegEnv -> String -> Exp2 -> PassM Exp2
addTraversalsExp ddefs fundefs env2 renv context ex =
  case ex of
    CaseE scrt@(VarE sv) brs -> do
        let PackedTy _tycon tyloc = lookupVEnv sv env2
            reg = renv # tyloc
        CaseE scrt <$> mapM (docase reg) brs

    CaseE scrt _ -> error $ "addTraversalsExp: Scrutinee is not flat " ++ sdoc scrt

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    CharE{}   -> return ex
    FloatE{}  -> return ex
    LitSymE{} -> return ex
    AppE f locs args -> AppE f locs <$> mapM go args
    PrimAppE f args  -> PrimAppE f <$> mapM go args
    WithArenaE v e -> WithArenaE v <$> addTraversalsExp ddefs fundefs (extendVEnv v ArenaTy env2) renv context e
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*>
        addTraversalsExp ddefs fundefs (extendVEnv v ty env2) renv context bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    DataConE{} -> return ex
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{} -> pure ex -- error "addTraversalsExp: Cannot compile SpawnE"
    SyncE    -> pure ex -- error "addTraversalsExp: Cannot compile SyncE"
    Ext ext ->
      case ext of
        LetRegionE reg sz ty bod -> Ext . LetRegionE reg sz ty <$> go bod
        LetParRegionE reg sz ty bod -> Ext . LetParRegionE reg sz ty <$> go bod
        L2.StartOfPkdCursor cur -> pure $ Ext $ L2.StartOfPkdCursor cur
        LetLocE loc FreeLE  bod ->
          Ext <$> LetLocE loc FreeLE <$>
            addTraversalsExp ddefs fundefs env2 renv context bod
        LetLocE loc locexp  bod ->
          let reg = case locexp of
                      StartOfRegionLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc   -> renv # lc
                      AfterVariableLE _ lc _ -> renv # lc
                      FromEndLE lc           -> renv # lc -- TODO: This needs to be fixed
          in Ext <$> LetLocE loc locexp <$>
               addTraversalsExp ddefs fundefs env2 (M.insert loc reg renv) context bod
        _ -> return ex
    MapE{}  -> error "addTraversalsExp: TODO MapE"
    FoldE{} -> error "addTraversalsExp: TODO FoldE"

  where
    go = addTraversalsExp ddefs fundefs env2 renv context

    docase reg (dcon,vlocs,rhs) = do
      let (vars,locs) = unzip vlocs
          env21 = extendPatternMatchEnv dcon ddefs vars locs env2
          renv1 = L.foldr (\lc acc -> M.insert lc reg acc) renv locs
          needs_traversal = needsTraversalCase ddefs fundefs env21 (dcon,vlocs,rhs)
      case needs_traversal of
        Nothing -> pure (dcon, vlocs, rhs)
        Just ls -> do
          dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags

          when dump_op $
            dbgTrace 2 ("Adding traversals: " ++ sdoc context) (return ())
          -- Generate traversals: assuming that InferLocs has already generated
          -- the traversal functions, we only use it here.
          trav_binds <- genTravBinds (L.map (\(p_var, _p_loc) -> (VarE p_var, lookupVEnv p_var env21)) ls)
          (dcon,vlocs,) <$> mkLets trav_binds <$>
            addTraversalsExp ddefs fundefs env21 renv1 context rhs


-- | Collect all non-static items that need to be traversed (uses InferEffects).
--
-- If we cannot unpack all the pattern matched variables:
-- (1) Everything after the first packed element should be unused in the RHS
-- (2) Otherwise, we must traverse the first (n-1) packed elements
needsTraversalCase :: DDefs Ty2 -> FunDefs2 -> Env2 Var Ty2 -> (DataCon, [(Var, LocVar)], Exp2) -> Maybe [(Var, LocVar)]
needsTraversalCase ddefs fundefs env2 (dcon,vlocs,rhs) =
  if isAbsRANDataCon dcon || isRelRANDataCon dcon then Nothing else
  let (vars, _locs) = unzip vlocs
      tys     = lookupDataCon ddefs dcon
      tyenv   = M.fromList (zip vars tys)
      funenv  = M.map funTy fundefs
      dps     = makeDps (reverse $ L.map snd vlocs)
      (eff,_) = inferExp ddefs funenv (M.union tyenv (vEnv env2)) dps rhs
      -- Note: Do not use Data.Map.filter. It changes the order sometimes.
      packedOnly = L.filter (\(_,b) -> hasPacked b) (zip vars tys)

      makeDps [] = M.empty
      makeDps [_] = M.empty
      makeDps (v:v':vs) = M.insert v v' (makeDps vs)

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

                           -- POLICY: We only traverse the first (n-1) packed elements.
                           -- However if (n==1), we traverse that element. Need to audit this.
                           ls = L.map (\a -> (loc_var_mp # a, a)) not_traversed
                           trav = if length ls == 1
                                  -- [2020.05.01]: CSK, I haven't thought about this change too much. Maybe we need to revisit this.
                                  then []
                                  else init ls

                       -- If the problematic elements are unused, we don't need to add traversals
                       if not (occurs should_be_unused rhs)
                       then Nothing
                       else Just trav

genTravBinds :: [(Exp2, Ty2)] -> PassM [(Var, [LocVar], Ty2, Exp2)]
genTravBinds ls = concat <$>
  (forM ls $ \(e,ty) ->
      case ty of
        PackedTy tycon loc1 -> do
          w <- gensym "trav"
          let fn_name = mkTravFunName tycon
          return [(w,[],ProdTy [], AppE fn_name [loc1] [e])]
        -- TODO: Write a testcase for this path.
        ProdTy tys -> do
          -- So that we don't have to make assumptions about the 'e' being a VarE
          tmp <- gensym "tmp_trav"
          proj_binds <-
            genTravBinds (L.foldl (\acc (ty1,idx) ->
                                   if isPackedTy ty1
                                   then (mkProj idx (VarE tmp), ty1) : acc
                                   else acc)
                                  []
                                  (zip tys [0..]))
          return $ [(tmp,[],ty,e)] ++ proj_binds
        _ -> return [])
