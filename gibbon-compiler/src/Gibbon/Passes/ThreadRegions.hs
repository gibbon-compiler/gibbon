module Gibbon.Passes.ThreadRegions where

import Data.Loc
import Data.List as L
import qualified Data.Map as M

import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

-- Maps a location to a region
type RegEnv = M.Map LocVar Var

threadRegions :: L2.Prog2 -> PassM L2.Prog2
threadRegions Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (threadRegionsFn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  threadRegionsExp ddefs fundefs True M.empty env2 mn
  return $ Prog ddefs fundefs' mainExp'

threadRegionsFn :: DDefs Ty2 -> FunDefs2 -> L2.FunDef2 -> PassM L2.FunDef2
threadRegionsFn ddefs fundefs f@FunDef{funArg,funTy,funBody} = do
  let initRegEnv = M.fromList $ map (\(LRM lc r _) -> (lc, regionToVar r)) (locVars funTy)
      initTyEnv  = M.singleton funArg (arrIn funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
  bod' <- threadRegionsExp ddefs fundefs False initRegEnv env2 funBody
  return $ f {funBody = bod'}

threadRegionsExp :: DDefs Ty2 -> FunDefs2 -> Bool -> RegEnv -> Env2 Ty2 -> L L2.Exp2
              -> PassM (L L2.Exp2)
threadRegionsExp ddefs fundefs isMain renv env2 (L p ex) = L p <$>
  case ex of
    AppE f applocs arg -> do
      let ty = gRecoverType ddefs env2 ex
          argty = gRecoverType ddefs env2 arg
          argtylocs = locsInTy argty
          argregs = foldr (\x acc -> case M.lookup x renv of
                                       Just r -> r:acc
                                       Nothing -> acc)
                    [] argtylocs
      case ty of
        _ | hasPacked ty -> do
          let fnty = funTy $ fundefs # f
              arrOutMp = M.fromList $ zip (allLocVars fnty) applocs
              -- TODO: Fix this in gRecoverType
              outT'  = substLoc arrOutMp ty
              tylocs = locsInTy outT'
              regs   = map (renv #) tylocs
          let newapplocs = nub $ (map toEndV argregs) ++ (map toEndV regs)  ++ applocs
          return $ AppE f newapplocs arg
        _ -> do
          let newapplocs = nub $ (map toEndV argregs) ++ applocs
          return $ AppE f newapplocs arg

    LetE (v,locs,ty, (L _ (AppE f applocs arg))) bod -> do
      let argty = gRecoverType ddefs env2 arg
          argtylocs = locsInTy argty
          argregs = foldr (\x acc -> case M.lookup x renv of
                                       Just r -> r:acc
                                       Nothing -> acc)
                    [] argtylocs
          -- Map EndOf locations to input regions
          renv' = M.union renv (M.fromList $ zip locs argregs)

      case ty of
        _ | hasPacked ty -> do
          let tylocs = locsInTy ty
              regs   = map (renv #) tylocs
          regs' <- mapM gensym regs
          -- Update all locations to point to the fresh region
          let renv'' = foldr (\(lc,r,r') acc ->
                               M.insert lc r' $
                               M.map (\tyl -> if tyl == r then r' else tyl) acc)
                      renv'
                      (L.zip3 tylocs regs regs')
              newlocs    = (map toEndV regs') ++ locs
              newapplocs = nub $ (map toEndV argregs) ++ (map toEndV regs)  ++ applocs
          LetE (v, newlocs, ty, l$ AppE f newapplocs arg) <$>
            threadRegionsExp ddefs fundefs isMain renv'' (extendVEnv v ty env2) bod

        _ -> do
          let newapplocs = nub $ (map toEndV argregs) ++ applocs
          LetE (v,locs,ty, l$ AppE f newapplocs arg) <$>
            threadRegionsExp ddefs fundefs isMain renv' (extendVEnv v ty env2) bod

    LetE (v,locs,ty, rhs) bod ->
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ty env2) bod

    Ext ext ->
      case ext of
        -- Update renv with a binding for loc
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                      StartOfLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc -> renv # lc
                      AfterVariableLE _ lc -> renv # lc
                      FromEndLE lc         -> renv # lc -- TODO: This needs to be fixed
          Ext <$> LetLocE loc rhs <$>
            threadRegionsExp ddefs fundefs isMain (M.insert loc reg renv) env2 bod

        -- Implements (2)
        RetE locs v -> do
          let ty = lookupVEnv v env2
          if not isMain && hasPacked ty
          then do
            let tylocs  = locsInTy ty
                regs    = map (renv #) tylocs
                newlocs = map toEndV regs
            return $ Ext $ RetE (newlocs ++ locs) v
          else return $ Ext ext

        LetRegionE r bod -> Ext <$> LetRegionE r <$> go bod
        FromEndE{}    -> return ex
        BoundsCheck sz _bound cur -> do
          return $ Ext $ BoundsCheck sz (toEndV (renv # cur)) cur
        IndirectionE{} -> return ex

    -- Straightforward recursion

    VarE{}     -> return ex
    LitE{}     -> return ex
    LitSymE{}  -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    CaseE scrt mp -> do
      let L _ (VarE v) = scrt
          PackedTy _ tyloc = lookupVEnv v env2
          reg = renv M.! tyloc
      CaseE scrt <$> mapM (docase reg renv env2) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    ParE a b -> ParE <$> go a <*> go b
    MapE{}  -> error $ "go: TODO MapE"
    FoldE{} -> error $ "go: TODO FoldE"

  where
    go = threadRegionsExp ddefs fundefs isMain renv env2

    docase reg renv1 env21 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          renv1' = foldr (\lc acc -> M.insert lc reg acc) renv1 locs
          tys = lookupDataCon ddefs dcon
          tys' = substLocs' locs tys
          env2' = extendsVEnv (M.fromList $ zip vars tys') env21
      (dcon,vlocs,) <$> (threadRegionsExp ddefs fundefs isMain renv1' env2' bod)
