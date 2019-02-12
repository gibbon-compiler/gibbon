module Gibbon.Passes.AddTraversals
  (addTraversals, needsTraversal) where

import Control.Monad ( forM, when )
import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Loc

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Passes.InferEffects ( inferExp )
import Gibbon.L1.Syntax
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

{- Note [Adding dummy traversals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

..TODO..

-}

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
addTraversalsFn ddefs fundefs f@FunDef{funName, funArg, funTy, funBody} = do
    let funenv = initFunEnv fundefs
        tyenv = M.singleton funArg (inTy funTy)
        env2 = Env2 tyenv funenv
        renv = M.fromList $ L.map (\lrm -> (lrmLoc lrm, regionToVar (lrmReg lrm)))
                                  (locVars funTy)
    bod' <- addTraversalsExp ddefs fundefs env2 renv (fromVar funName) funBody
    return $ f {funBody = bod'}

-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty2 -> FunDefs2 -> Env2 Ty2 -> RegEnv -> String -> L Exp2 -> PassM (L Exp2)
addTraversalsExp ddefs fundefs env2 renv context (L p ex) = L p <$>
  case ex of
    CaseE scrt@(L _ (VarE sv)) brs -> do
        let PackedTy _tycon tyloc = lookupVEnv sv env2
            reg = renv # tyloc
        CaseE scrt <$> mapM (docase reg) brs

    CaseE scrt _ -> error $ "addTraversalsExp: Scrutinee is not flat " ++ sdoc scrt

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args

{-
Also see (2) of Note [When does a type 'needsRAN'] in Gibbon.Passes.AddRAN.

The program has a tuple (a,b) and needs access to both 'a' and 'b' simultaneously.
When 'a' and 'b' both live in the same region, most likely we'll only have access
to one of them. There are 2 assumptions that we make about such tuples:

(1) 'a' and 'b' live right next to each other in a region.
    (CSK: This is arbitrary and needs proper review.)

(2) 'a' occurs before 'b'. This is complete garbage and we need to find out
    which value actually occurs first, and have to traverse that.

..TODO.. This looks like a band-aid and parallel tuples need to be handled
         properly in the pass.
-}
    LetE (v,locs,ty, rhs@(L _ (ParE a b))) bod -> do
      let appArgTy :: L Exp2 -> (L Exp2, Ty2)
          appArgTy (L _ (AppE _ _ arg)) = (arg, gRecoverType ddefs env2 arg)
          appArgTy oth = error $ "appArgTy: Cannot handle " ++ sdoc oth

          (arg1, argty1) = appArgTy a
          (_arg2, argty2) = appArgTy b
          locs1 = locsInTy argty1
          locs2 = locsInTy argty2

          regs1 = S.fromList (L.map (renv #) locs1)
          regs2 = S.fromList (L.map (renv #) locs2)
          -- The regions used in BOTH parts of the tuple combinator --
          -- all values residing in these regions would need RAN's.
          common_regs = S.intersection regs1 regs2

      if S.null common_regs
      then LetE <$> (v,locs,ty,) <$> go rhs <*>
             addTraversalsExp ddefs fundefs (extendVEnv v ty env2) renv context bod
      else do
        -- Only traversing arg1. See ASSUMPTION above.
        trav_binds <- genTravBinds [(arg1,argty1)]
        rhs' <- go rhs
        bod' <- addTraversalsExp ddefs fundefs (extendVEnv v ty env2) renv context bod
        return $ unLoc (mkLets (trav_binds ++ [(v,locs,ty,rhs')]) bod')
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
    ParE a b -> ParE <$> go a <*> go b
    Ext ext ->
      case ext of
        LetRegionE reg bod -> Ext <$> LetRegionE reg <$> go bod
        LetLocE loc locexp bod ->
          let reg = case locexp of
                      StartOfLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc -> renv # lc
                      AfterVariableLE _ lc -> renv # lc
                      FromEndLE lc         -> renv # lc -- TODO: This needs to be fixed
          in Ext <$> LetLocE loc locexp <$>
               addTraversalsExp ddefs fundefs env2 (M.insert loc reg renv) context bod
        _ -> return ex
    MapE{}  -> error "addTraversalsExp: TODO MapE"
    FoldE{} -> error "addTraversalsExp: TODO FoldE"

  where
    go = addTraversalsExp ddefs fundefs env2 renv context

    docase reg (dcon,vlocs,rhs) = do
      let (vars,locs) = unzip vlocs
          tys   = substLocs' locs (lookupDataCon ddefs dcon)
          env21 = extendsVEnv (M.fromList (zip vars tys)) env2
          renv1 = L.foldr (\lc acc -> M.insert lc reg acc) renv locs
          needs_traversal = needsTraversal ddefs fundefs env21 (dcon,vlocs,rhs)
      case needs_traversal of
        Nothing -> (dcon, vlocs,) <$> addTraversalsExp ddefs fundefs env21 renv1 context rhs
        Just ls -> do
          dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags

          when dump_op $
            dbgTrace 2 ("Adding traversals: " ++ sdoc context) (return ())
          -- Generate traversals: assuming that InferLocs has already generated
          -- the traversal functions, we only use it here.
          trav_binds <- genTravBinds (L.map (\(p_var, _p_loc) -> (l$ VarE p_var, lookupVEnv p_var env21)) ls)
          (dcon,vlocs,) <$> mkLets trav_binds <$>
            addTraversalsExp ddefs fundefs env21 renv1 context rhs


-- | Collect all non-static items that need to be traversed (uses InferEffects).
--
-- If we cannot unpack all the pattern matched variables:
-- (1) Everything after the first packed element should be unused in the RHS
-- (2) Otherwise, we must traverse the first (n-1) packed elements
needsTraversal :: DDefs Ty2 -> FunDefs2 -> Env2 Ty2 -> (DataCon, [(Var, LocVar)], L Exp2) -> Maybe [(Var, LocVar)]
needsTraversal ddefs fundefs env2 (dcon,vlocs,rhs) =
  let (vars, _locs) = unzip vlocs
      tys     = lookupDataCon ddefs dcon
      tyenv   = M.fromList (zip vars tys)
      funenv  = M.map funTy fundefs
      (eff,_) = inferExp ddefs funenv (M.union tyenv (vEnv env2)) rhs
      -- Note: Do not use Data.Map.filter. It changes the order sometimes.
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

                           -- POLICY: We only traverse the first (n-1) packed elements.
                           -- However if (n==1), we traverse that element. Need to audit this.
                           ls = L.map (\a -> (loc_var_mp # a, a)) not_traversed
                           trav = if length ls == 1
                                  then ls
                                  else init ls

                       -- If the problematic elements are unused, we don't need to add traversals
                       if not (occurs should_be_unused rhs)
                       then Nothing
                       else Just trav

genTravBinds :: [(L Exp2, Ty2)] -> PassM [(Var, [LocVar], Ty2, L Exp2)]
genTravBinds ls = concat <$>
  (forM ls $ \(e,ty) ->
      case ty of
        PackedTy tycon loc1 -> do
          w <- gensym "trav"
          let fn_name = mkTravFunName tycon
          return [(w,[],IntTy, l$ AppE fn_name [loc1] e)]
        -- TODO: Write a testcase for this path.
        ProdTy tys -> do
          -- So that we don't have to make assumptions about the 'e' being a VarE
          tmp <- gensym "tmp_trav"
          proj_binds <-
            genTravBinds (L.foldl (\acc (ty1,idx) ->
                                   if isPackedTy ty1
                                   then (mkProj idx (l$ VarE tmp), ty1) : acc
                                   else acc)
                                  []
                                  (zip tys [0..]))
          return $ [(tmp,[],ty,e)] ++ proj_binds
        _ -> return [])
