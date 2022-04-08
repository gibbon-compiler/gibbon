module Gibbon.Passes.ThreadRegions where

import qualified Data.List as L
import Data.Maybe ( fromJust )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable ( foldrM )

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

{-

Threading regions
~~~~~~~~~~~~~~~~~

Functions need end-of-regions cursors for various purposes. The output region
cursors are used for bounds checking (See [Infinite regions] in BoundsCheck).
The input region cursors are useful for garbage collection -- if there's an
indirection from R1 to R2 (input), we need to bump R2's refcount and therefore
need R2's cursor. This pass updates all call-sites to also pass region cursors.
They are prepended to the locations that AppE forms accept.
N.B. for output regions, we actually use end-of-chunk cursors, not
end-of-region cursors.

    AppE add1 [lin, lout] arg

becomes

    AppE add1 [regin, regout, lin, lout] arg


Moreover, functions must also return region cursors, at least for the output
regions. Consider this example:

    ...
    let (x, lout1) = AppE add1 [regin1, regout, lin1, lout] a1 in
    let (y, lout2) = AppE add1 [regin2, regout, lin2, lout1] a2 in
    ...

This is not correct. Because of bounds checking, the first call to add1 might
start using a new output chunk. And we shouldn't use regout in the second call
to add1 -- 'regout' is already full! So we have to thread these output regions,
just like we do the output locations.

    ...
    let (x, lout1, regout1) = AppE add1 [regin1, regout, lin1, lout] a1 in
    let (y, lout2, regout2) = AppE add1 [regin2, regout1, lin2, lout1] a2 in
    ...


-}


-- Maps a location to a region
type RegEnv = M.Map LocVar Var

-- Maps the LHS of a constructor to the region of it's last field. Because of
-- parallelism the last field of constructor may not be in the same region as
-- it's tag. The region of the last field represents the "finished writing
-- output here region", so that's the region that should be threaded.
type LastFieldRegEnv = M.Map Var Var

threadRegions :: L2.Prog2 -> PassM L2.Prog2
threadRegions Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (threadRegionsFn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  threadRegionsExp ddefs fundefs True M.empty env2 M.empty M.empty M.empty mn
  return $ Prog ddefs fundefs' mainExp'

threadRegionsFn :: DDefs Ty2 -> FunDefs2 -> L2.FunDef2 -> PassM L2.FunDef2
threadRegionsFn ddefs fundefs f@FunDef{funName,funArgs,funTy,funBody} = do
  let initRegEnv = M.fromList $ map (\(LRM lc r _) -> (lc, regionToVar r)) (locVars funTy)
      initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
      fn = (\ty acc -> case ty of
                         PackedTy tycon loc -> M.insert loc tycon acc
                         ProdTy tys -> foldr fn acc tys
                         _ -> acc)
      rlocs_env = foldr fn M.empty (arrIns funTy)
      wlocs_env = fn (arrOut funTy) M.empty
  bod' <- threadRegionsExp ddefs fundefs False initRegEnv env2 M.empty rlocs_env wlocs_env funBody
  -- Boundschecking
  dflags <- getDynFlags
  let bod'' = if gopt Opt_BigInfiniteRegions dflags
              then bod'
              -- This function is always given a BigInfinite region.
              else if isCopySansPtrsFunName funName
              then bod'
              else
                let packed_outs = getPackedTys (arrOut funTy)
                    locs_tycons = foldr
                                    (\ty acc ->
                                         case ty of
                                           PackedTy t loc ->  M.insert loc t acc
                                           _ -> acc)
                                    M.empty
                                    packed_outs
                in foldr
                     (\(LRM loc reg mode) acc ->
                        if mode == Output
                        then let rv = toEndV $ regionToVar reg
                                 bc = boundsCheck ddefs (locs_tycons M.! loc)
                             in -- dbgTraceIt ("boundscheck" ++ sdoc ((locs_tycons M.! loc), bc)) $
                                LetE ("_",[],IntTy, Ext$ BoundsCheck bc rv loc) acc
                        else acc)
                     bod'
                     (locVars funTy)
  return $ f {funBody = bod''}

threadRegionsExp :: DDefs Ty2 -> FunDefs2 -> Bool -> RegEnv -> Env2 Ty2
                 -> LastFieldRegEnv -> M.Map Var TyCon -> M.Map Var TyCon -> L2.Exp2
                 -> PassM L2.Exp2
threadRegionsExp ddefs fundefs isMain renv env2 lfenv rlocs_env wlocs_env ex =
  case ex of
    AppE f applocs args -> do
      let ty = gRecoverType ddefs env2 ex
          argtys = map (gRecoverType ddefs env2) args
          argtylocs = concatMap locsInTy argtys
          in_regs = foldr (\x acc -> case M.lookup x renv of
                                       Just r -> r:acc
                                       Nothing -> acc)
                    [] argtylocs
      -- If this function returns a Packed type, it'll have input and output
      -- locations and therefore, input and output regions.
      if hasPacked ty
      then do
        let out_tylocs = locsInTy ty
            out_regs   = map (renv #) out_tylocs
        let newapplocs = (map toEndV in_regs) ++ (map toEndV out_regs)  ++ applocs
        return $ AppE f newapplocs args
      -- Otherwise, only input regions.
      else do
        let newapplocs = (map toEndV in_regs) ++ applocs
        return $ AppE f newapplocs args

    LetE (v,locs,ty, (AppE f applocs args)) bod -> do
      let -- argtys = map (gRecoverType ddefs env2) args
          -- argtylocs = concatMap locsInTy argtys
          argtylocs = concatMap
                        (\arg ->
                             let argty = gRecoverType ddefs env2 arg in
                             case arg of
                               VarE w ->
                                 case argty of
                                   CursorTy -> [w]
                                   _ -> locsInTy argty
                               _ -> locsInTy argty)
                        args
          in_regs = foldr (\x acc -> case M.lookup x renv of
                                       Just r -> r:acc
                                       Nothing -> acc)
                    [] argtylocs
          -- Map EndOf locations to input regions
          renv' = M.union renv (M.fromList $ zip locs in_regs)

      -- Similar to the AppE case above, this one would have input and
      -- output regions.
      if (hasPacked ty)
      then do
        let tylocs = locsInTy ty
            out_regs   = map (renv #) tylocs
        out_regs' <- mapM (\r -> gensym r) out_regs
        -- Update all locations to point to the fresh region
        let renv'' = foldr (\(lc,r,r') acc ->
                             M.insert lc r' $
                             M.map (\tyl -> if tyl == r then r' else tyl) acc)
                    renv'
                    (L.zip3 tylocs out_regs out_regs')
            newretlocs = (map toEndV out_regs') ++ locs
            newapplocs = (map toEndV in_regs) ++ (map toEndV out_regs)  ++ applocs
        let env2' = extendVEnv v ty env2
            rlocs_env' = case ty of
                           PackedTy tycon loc -> M.insert loc tycon rlocs_env
                           _ -> error "threadRegionExp: "
            wlocs_env' = foldr (\loc acc -> M.delete loc acc) wlocs_env (locsInTy ty)
        bod' <- threadRegionsExp ddefs fundefs isMain renv'' env2' lfenv rlocs_env' wlocs_env' bod
        let -- free = S.fromList $ freeLocVars bod
            free = ss_free_locs (S.fromList (v : locsInTy ty ++ locs)) env2' bod
            free_rlocs = free `S.intersection` (M.keysSet rlocs_env')
            free_wlocs = free `S.intersection` (M.keysSet wlocs_env')
        (rpush,wpush,rpop,wpop) <- ss_ops free_rlocs free_wlocs
        let binds = rpush ++ wpush ++ [(v, newretlocs, ty, AppE f newapplocs args)] ++ wpop ++ rpop
        (pure $ mkLets binds bod')

      -- Only input regions.
      else do
          let env2' = extendVEnv v ty env2
          bod' <- threadRegionsExp ddefs fundefs isMain renv' env2' lfenv rlocs_env wlocs_env bod
          let newapplocs = (map toEndV in_regs) ++ applocs
          let -- free = S.fromList $ freeLocVars bod
              free = ss_free_locs (S.fromList (v : locsInTy ty ++ locs)) env2' bod
              free_rlocs = free `S.intersection` (M.keysSet rlocs_env)
              free_wlocs = free `S.intersection` (M.keysSet wlocs_env)
          (rpush,wpush,rpop,wpop) <- ss_ops free_rlocs free_wlocs
          let binds = rpush ++ wpush ++ [(v, locs, ty, AppE f newapplocs args)] ++ wpop ++ rpop
          (pure $ mkLets binds bod')

    LetE (v,locs,ty, (SpawnE f applocs args)) bod -> do
      let e' = LetE (v,locs,ty, (AppE f applocs args)) bod
      e'' <- threadRegionsExp ddefs fundefs isMain renv env2 lfenv rlocs_env wlocs_env e'
      pure $ changeAppToSpawn f args e''

    -- AUDITME: this causes all all DataConE's to return an additional cursor.
    LetE (v,locs,ty@(PackedTy _ loc), rhs@(DataConE _ _ args)) bod -> do
      let reg_of_tag = renv M.! loc
          lfenv' = case args of
                     [] -> lfenv
                     _  ->
                       let last_ty = gRecoverType ddefs env2 (last args) in
                       case last_ty of
                          PackedTy _ last_loc -> do
                            let reg_of_last_arg = renv M.! last_loc
                            if reg_of_tag /= reg_of_last_arg
                            then M.insert v reg_of_last_arg lfenv
                            else lfenv
                          _ -> lfenv
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ty env2) lfenv' rlocs_env wlocs_env bod

    -- Sometimes, this expression can have RetE forms. We should collect and update
    -- the locs here appropriately.
    LetE (v,locs,ty, rhs@(TimeIt{})) bod -> do
       rhs' <- go rhs
       let retlocs = findRetLocs rhs'
           newretlocs = retlocs ++ locs
       LetE (v, newretlocs,ty, rhs') <$>
         threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ty env2) lfenv rlocs_env wlocs_env bod

    LetE (v,locs,ty,rhs@(Ext (AllocateTagHere x x_tycon))) bod -> do
      let -- x_tycon = (wlocs_env # x)
          rlocs_env' = M.insert x x_tycon rlocs_env
          wlocs_env' = M.delete x wlocs_env
      (LetE (v,locs,ty,rhs)) <$>
        threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ty env2) lfenv rlocs_env' wlocs_env' bod

    LetE (v,locs,ty, rhs) bod ->
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ty env2) lfenv rlocs_env wlocs_env bod

    WithArenaE v e ->
      WithArenaE v <$> threadRegionsExp ddefs fundefs isMain renv (extendVEnv v ArenaTy env2) lfenv rlocs_env wlocs_env e

    Ext ext ->
      case ext of
        AddFixed{} -> return ex
        LetLocE loc FreeLE bod ->
          Ext <$> LetLocE loc FreeLE <$>
            threadRegionsExp ddefs fundefs isMain renv env2 lfenv rlocs_env wlocs_env bod

        -- Update renv with a binding for loc
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                      StartOfLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc   -> renv # lc
                      AfterVariableLE _ lc _ -> renv # lc
                      FromEndLE lc           -> renv # lc
              wlocs_env' = M.insert loc hole_tycon wlocs_env
          Ext <$> LetLocE loc rhs <$>
            threadRegionsExp ddefs fundefs isMain (M.insert loc reg renv) env2 lfenv rlocs_env wlocs_env' bod

        RetE locs v -> do
          let ty = lookupVEnv v env2
          if not isMain && isPackedTy ty
          then
            case M.lookup v lfenv of
              Nothing -> do
                let tylocs  = locsInTy ty
                    regs    = map (renv #) tylocs
                    newlocs_env = map toEndV regs
                return $ Ext $ RetE (newlocs_env ++ locs) v
              Just r  -> return $ Ext $ RetE (toEndV r : locs) v
          else if hasPacked ty
          then do
            let tylocs  = locsInTy ty
                regs    = map (renv #) tylocs
                newlocs_env = map toEndV regs
            return $ Ext $ RetE (newlocs_env ++ locs) v
          else return $ Ext ext

        LetRegionE r sz ty bod -> do
          let -- free = S.fromList $ freeLocVars bod
              free = ss_free_locs (S.singleton (regionToVar r)) env2 bod
              free_rlocs = free `S.intersection` (M.keysSet rlocs_env)
              free_wlocs = free `S.intersection` (M.keysSet wlocs_env)
          (rpush,wpush,rpop,wpop) <- ss_ops free_rlocs free_wlocs
          bod' <- go bod
          let pre = mkLets (rpush ++ wpush)
              post = mkLets (wpop ++ rpop) bod'
          pure $ pre (Ext $ LetRegionE r sz ty post)
        LetParRegionE r sz ty bod -> Ext <$> LetParRegionE r sz ty <$> go bod
        FromEndE{}    -> return ex
        BoundsCheck sz _bound cur -> do
          return $ Ext $ BoundsCheck sz (toEndV (renv # cur)) cur
        IndirectionE{}   -> return ex
        GetCilkWorkerNum -> return ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
        AllocateTagHere{} -> pure ex
        AllocateScalarsHere{} -> pure ex
        SSPush{} -> pure ex
        SSPop{} -> pure ex

    -- Straightforward recursion

    VarE{}     -> return ex
    LitE{}     -> return ex
    FloatE{}   -> return ex
    LitSymE{}  -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    CaseE scrt mp -> do
      let (VarE v) = scrt
          PackedTy _ tyloc = lookupVEnv v env2
          reg = renv M.! tyloc
      CaseE scrt <$> mapM (docase reg renv env2 lfenv rlocs_env wlocs_env) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{} -> error "threadRegionsExp: Unbound SpawnE"
    SyncE    -> pure ex
    MapE{}  -> error $ "threadRegionsExp: TODO MapE"
    FoldE{} -> error $ "threadRegionsExp: TODO FoldE"

  where
    go = threadRegionsExp ddefs fundefs isMain renv env2 lfenv rlocs_env wlocs_env

    docase reg renv1 env21 lfenv1 rlocs_env1 wlocs_env1 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          renv0  = if isIndirectionTag dcon || isRedirectionTag dcon
                   then foldr (\lc acc -> M.insert lc reg acc) renv1 vars
                   else renv1
          renv1' = foldr (\lc acc -> M.insert lc reg acc) renv0 locs
          env21' = extendPatternMatchEnv dcon ddefs vars locs env21
          rlocs_env1' = foldr (\(loc,ty) acc ->
                                case ty of
                                  PackedTy tycon _ -> M.insert loc tycon acc
                                  _ -> acc)
                              rlocs_env1
                              (fragileZip locs (lookupDataCon ddefs dcon))
      (dcon,vlocs,) <$> (threadRegionsExp ddefs fundefs isMain renv1' env21' lfenv1 rlocs_env1' wlocs_env1 bod)

    ss_free_locs bound env20 ex0 =
                     S.map (\w -> case M.lookup w (vEnv env20) of
                                       -- assumption: it's a location
                                       Nothing -> w
                                       Just (PackedTy _ loc) -> loc
                                       Just wty -> error $ "threadRegionsExp: unexpected type " ++ show (w,wty))
                           (allFreeVars_sans_datacon_args ex0 `S.difference`
                            (bound `S.union`
                             M.keysSet (M.filter (not . isPackedTy) (vEnv env20)) `S.union`
                             M.keysSet (fEnv env20)))

    hole_tycon = "HOLE"

    ss_ops free_rlocs free_wlocs = do
          rpush <- (foldrM (\x acc -> do
                             push <- gensym "ss_push"
                             let tycon = rlocs_env # x
                             if tycon == hole_tycon
                             then pure acc
                             else pure ((push,[],ProdTy [], Ext $ SSPush Read x (toEndV (renv # x)) tycon) : acc))
                           []
                           free_rlocs) :: PassM [(Var, [LocVar], Ty2, PreExp E2Ext LocVar Ty2)]
          wpush <- (foldrM (\x acc -> do
                             push <- gensym "ss_push"
                             let tycon = wlocs_env # x
                             if tycon == hole_tycon
                             then pure acc
                             else pure ((push,[],ProdTy [], Ext $ SSPush Write x (toEndV (renv # x)) tycon) : acc))
                           []
                           free_wlocs) :: PassM [(Var, [LocVar], Ty2, PreExp E2Ext LocVar Ty2)]
          let rpop = map (\(x,locs,ty,Ext (SSPush a b c _)) -> (x,locs,ty,Ext (SSPop a b c))) (reverse rpush)
              wpop = map (\(x,locs,ty,Ext (SSPush a b c _)) -> (x,locs,ty,Ext (SSPop a b c))) (reverse wpush)
          pure (rpush,wpush,rpop,wpop)


-- Inspect an AST and return locations in a RetE form.
findRetLocs :: Exp2 -> [LocVar]
findRetLocs e0 = go e0 []
  where
    go :: Exp2 -> [LocVar] -> [LocVar]
    go ex acc =
      case ex of
        VarE{}    -> acc
        LitE{}    -> acc
        FloatE{}  -> acc
        LitSymE{} -> acc
        AppE _ _ args   -> foldr go acc args
        PrimAppE _ args -> foldr go acc args
        LetE (_,_,_,rhs) bod -> do
          foldr go acc [rhs,bod]
        IfE a b c  -> foldr go acc [a,b,c]
        MkProdE xs -> foldr go acc xs
        ProjE _ e  -> go e acc
        DataConE _ _ args -> foldr go acc args
        CaseE _ mp ->
          foldr (\(_,_,c) acc2 -> go c acc2) acc mp
        TimeIt e _ty _b  -> go e acc
        WithArenaE _v e -> go e acc
        SpawnE{} -> acc
        SyncE{}  -> acc
        Ext ext ->
          case ext of
            LetRegionE _ _ _ bod  -> go bod acc
            LetParRegionE _ _ _ bod  -> go bod acc
            LetLocE _ _ bod   -> go bod acc
            RetE locs _       -> locs ++ acc
            FromEndE{}        -> acc
            BoundsCheck{}     -> acc
            IndirectionE{}    -> acc
            AddFixed{}        -> acc
            GetCilkWorkerNum  -> acc
            LetAvail _ bod    -> go bod acc
            AllocateTagHere{} -> acc
            AllocateScalarsHere{} -> acc
            SSPush{} -> acc
            SSPop{} -> acc
        MapE{}  -> error "findRetLocs: TODO MapE"
        FoldE{}  -> error "findRetLocs: TODO FoldE"

----------------------------------------

-- Maximal sum of sizes of scalars before the first packed thing in the
-- constructors of this type. The assumption is that whatever writes
-- that packed value will do a bounds check again. Note that only AppE's
-- do boundschecking, DataConE's dont. We should fix this.
boundsCheck :: DDefs2 -> TyCon -> Int
boundsCheck ddefs tycon =
  let dcons = getConOrdering ddefs tycon
      spaceReqd tys = foldl (\(bytes, seen_packed) ty ->
                               if seen_packed
                               then ( bytes, seen_packed )
                               else if hasPacked ty
                               then ( bytes, True )
                               else ( bytes + (fromJust $ sizeOfTy ty), False ))
                        (0, False)
                        tys
      tyss = map (lookupDataCon ddefs) dcons
      vals = map (fst . spaceReqd) tyss
      -- Add a byte for the tag.
      num_bytes = (1 + maximum vals)
  -- Reserve additional space for a redirection node or a forwarding pointer.
  in num_bytes + 32

----------------------------------------

-- gFreeVars ++ locations ++ region variables - (args to datacons)
allFreeVars_sans_datacon_args :: Exp2 -> S.Set Var
allFreeVars_sans_datacon_args ex =
  case ex of
    AppE _ locs args -> S.fromList locs `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    PrimAppE _ args -> (S.unions (map allFreeVars_sans_datacon_args args))
    LetE (v,locs,_,rhs) bod -> (S.fromList locs `S.union` (allFreeVars_sans_datacon_args rhs) `S.union` (allFreeVars_sans_datacon_args bod))
                               `S.difference` S.singleton v
    IfE a b c -> allFreeVars_sans_datacon_args a `S.union` allFreeVars_sans_datacon_args b `S.union` allFreeVars_sans_datacon_args c
    MkProdE args -> (S.unions (map allFreeVars_sans_datacon_args args))
    ProjE _ bod -> allFreeVars_sans_datacon_args bod
    CaseE scrt brs -> (allFreeVars_sans_datacon_args scrt) `S.union` (S.unions (map (\(_,vlocs,c) -> allFreeVars_sans_datacon_args c `S.difference`
                                                                                   S.fromList (map fst vlocs) `S.difference`
                                                                                   S.fromList (map snd vlocs))
                                                                  brs))
    DataConE loc _ _args -> S.singleton loc
    TimeIt e _ _ -> allFreeVars_sans_datacon_args e
    WithArenaE _ e -> allFreeVars_sans_datacon_args e
    SpawnE _ locs args -> S.fromList locs `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    Ext ext ->
      case ext of
        LetRegionE r bod -> S.delete (regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetParRegionE r bod -> S.delete (regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetLocE loc locexp bod -> S.delete loc (allFreeVars_sans_datacon_args bod `S.union` gFreeVars locexp)
        RetE locs v     -> S.insert v (S.fromList locs)
        FromEndE loc    -> S.singleton loc
        BoundsCheck _ reg cur -> S.fromList [reg,cur]
        IndirectionE _ _ (a,b) (c,d) _ -> S.fromList $ [a,b,c,d]
        AddFixed v _    -> S.singleton v
        GetCilkWorkerNum-> S.empty
        LetAvail vs bod -> S.fromList vs `S.union` gFreeVars bod
        AllocateTagHere loc _ -> S.singleton loc
        AllocateScalarsHere loc -> S.singleton loc
        SSPush _ a b _ -> S.fromList [a,b]
        SSPop _ a b -> S.fromList [a,b]
    _ -> gFreeVars ex
