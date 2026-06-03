{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | Replace calls to copy functions with tagged indirection nodes
module Gibbon.Passes.RemoveCopies where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

-- Maps a location to a region
type LocEnv = M.Map LocVar RegVar

removeCopies :: Prog2 -> PassM Prog2
removeCopies Prog{ddefs,fundefs,mainExp} = do
  dflags <- getDynFlags
  let keepCopiesForMutableGC = gopt Opt_UseMutableCursors dflags && not (gopt Opt_DisableGC dflags)
  ddefs' <- mapM (\ddf@DDef{dataCons} -> do
                    dcon <- fromVar <$> gensym (toVar indirectionTag)
                    -- RemoveCopies might run more than once (b/c repairProgram), so
                    -- we ensure that we add the Indirection constructor only once.
                    let datacons = filter (not . isIndirectionTag . fst) dataCons
                    let ty_of_indirection = getCursorTypeForDataCon ddefs ddf  
                    return ddf {dataCons = datacons ++ [(dcon, [(False, ty_of_indirection)])]} )
            ddefs
  -- Don't process copy* functions
  fds' <- mapM (\fn -> if isCopyFunName (funName fn)
                       then return fn
                       else removeCopiesFn keepCopiesForMutableGC ddefs' fundefs fn)
               (M.elems fundefs)
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  removeCopiesExp keepCopiesForMutableGC ddefs' fundefs M.empty env2 mn
  return $ Prog ddefs' fundefs' mainExp'

removeCopiesFn :: Bool -> DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef2
removeCopiesFn keepCopiesForMutableGC ddefs fundefs f@FunDef{funArgs,funTy,funBody} = do
  let initLocEnv = M.fromList $ map (\(LRM lc r _) -> case r of 
                                                          _ -> (lc, regionToVar r)
                                    ) (locVars funTy)
      initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
  bod' <- removeCopiesExp keepCopiesForMutableGC ddefs fundefs initLocEnv env2 funBody
  return $ f {funBody = bod'}

-- ASSUMPTION: copy functions would always be called on a single argument.
removeCopiesExp :: Bool -> DDefs Ty2 -> FunDefs2 -> LocEnv -> Env2 Var Ty2 -> Exp2 -> PassM Exp2
removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv env2 ex =
  case ex of
    AppE f _cty [_,_] [_] | isCopyFunName f && keepCopiesForMutableGC ->
      pure ex

    LetE (v,locs,ty, rhs@(AppE f _cty [_,_] [_])) bod | isCopyFunName f && keepCopiesForMutableGC ->
      LetE (v,locs,ty, rhs) <$>
        removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv (extendVEnv v ty env2) bod

    -- This AppE copies data from 'lin' to 'lout'. When this becomes an
    -- indirection node, 'lout' is the _pointer_, and 'lin' the _pointee_.
    AppE f _cty [lin,lout] [arg] | isCopyFunName f -> do
      indirection <- gensym "indirection"
      let (PackedTy tycon _) = gRecoverType ddefs env2 ex
          -- the indirection datacon for this type
          indrDcon = filter isIndirectionTag $ getConOrdering ddefs tycon
      case indrDcon of
        [] -> error $ "removeCopies: No indirection constructor found for: " ++ sdoc tycon
        [dcon] -> do
          let reg_lout = case (lenv # lout) of 
                                  SingleR v -> fromRegVarToLocVar $ (SingleR v)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          let reg_lin = case (lenv # lin) of 
                                  SingleR v -> fromRegVarToLocVar $ (SingleR v)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          return $
            mkLets ([(indirection,[],PackedTy tycon lout,
                      Ext $ IndirectionE tycon dcon (lout , reg_lout) (lin, reg_lin) arg)])
            (VarE indirection)
        oth -> error $ "removeCopies: Multiple indirection constructors: " ++ sdoc oth

    LetE (v,locs,ty@(PackedTy tycon _), (AppE f _cty [lin,lout] [arg])) bod | isCopyFunName f -> do
      -- Get the indirection datacon for this type
      let indrDcon = filter isIndirectionTag $ getConOrdering ddefs tycon
      case indrDcon of
        [] -> error $ "removeCopies: No indirection constructor found for: " ++ sdoc tycon
        [dcon] -> do
          let reg_lout = case (lenv # lout) of 
                                  SingleR vr -> fromRegVarToLocVar $ (SingleR vr)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          let reg_lin = case (lenv # lin) of 
                                  SingleR vr -> fromRegVarToLocVar $ (SingleR vr)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          LetE (v,locs,ty, Ext $ IndirectionE tycon dcon (lout , reg_lout) (lin, reg_lin) arg) <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv (extendVEnv v ty env2) bod
        oth -> error $ "removeCopies: Multiple indirection constructors: " ++ sdoc oth

    Ext ext ->
      case ext of
        -- Update lenv with a binding for loc
        LetLocE loc FreeLE bod -> do
          Ext <$> LetLocE loc FreeLE <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv env2 bod
        StartOfPkdCursor cur -> pure $ Ext $ StartOfPkdCursor cur
        TagCursor a b -> pure $ Ext $ TagCursor a b
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                      StartOfRegionLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc   -> lenv # lc
                      AfterVariableLE _ lc _ -> lenv # lc
                      FromEndLE lc           -> lenv # lc -- TODO: This needs to be fixed
                      GetDataConLocSoA lc -> 
                        let rlc = lenv # lc
                         in getDataConRegFromRegVar rlc
                      GetFieldLocSoA (dcon, idx) lc -> 
                        let rlc = lenv # lc
                         in getFieldRegFromRegVar (dcon, idx) rlc 
                      AssignLE lc -> lenv # lc
                      GenSoALoc dconLoc fieldLocs -> 
                         let dconReg = lenv # dconLoc
                             fldRegs = map (\((dcon, idx), fl) -> let rl = lenv # fl
                                                                   in ((dcon, idx), rl)
                                           ) fieldLocs
                           in SoARv dconReg fldRegs
          Ext <$> LetLocE loc rhs <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs (M.insert loc reg lenv) env2 bod
       -- Straightforward recursion
        RetE{} -> return ex
        AddFixed{} -> return ex
        LetRegionE r sz endmut ty bod -> Ext <$> LetRegionE r sz endmut ty <$> go bod
        LetParRegionE r sz ty bod -> Ext <$> LetParRegionE r sz ty <$> go bod
        FromEndE{}       -> return ex
        BoundsCheck{}    -> return ex
        IndirectionE{}   -> return ex
        GetCilkWorkerNum -> return ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
        AllocateTagHere{} -> return ex
        AllocateScalarsHere{} -> return ex
        SSPush{} -> return ex
        SSPop{} -> return ex

    -- Straightforward recursion
    VarE{}     -> return ex
    LitE{}     -> return ex
    CharE{}    -> return ex
    FloatE{}   -> return ex
    LitSymE{}  -> return ex
    AppE{}     -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    LetE (v,locs,ty, rhs) bod ->
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv (extendVEnv v ty env2) bod
    CaseE scrt mp -> do
      let (VarE v) = scrt
          PackedTy _ tyloc = lookupVEnv v env2
          reg = lenv M.! tyloc
      CaseE scrt <$> mapM (docase reg lenv env2) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    WithArenaE v e -> do
      e' <- go e
      return $ WithArenaE v e'
    SpawnE{}-> pure ex
    SyncE   -> pure ex
    MapE{}  -> error $ "go: TODO MapE"
    FoldE{} -> error $ "go: TODO FoldE"
  where
    go = removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv env2
    docase reg lenv1 env21 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          lenv1' = foldr (\lc acc -> M.insert lc reg acc) lenv1 locs
          env21' = extendPatternMatchEnv dcon ddefs vars locs env21
      (dcon,vlocs,) <$> (removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv1' env21' bod)
