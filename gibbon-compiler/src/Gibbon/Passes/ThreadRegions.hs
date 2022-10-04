module Gibbon.Passes.ThreadRegions where

import qualified Data.List as L
import Data.Maybe ( fromJust )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable ( foldrM )

import Gibbon.Common
import Gibbon.DynFlags
-- import Gibbon.NewL2.Syntax as L2
import Gibbon.NewL2.Syntax as NewL2

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
type RegEnv = M.Map LocVar RegVar

-- Maps the LHS of a constructor to the region of it's last field. Because of
-- parallelism the last field of constructor may not be in the same region as
-- it's tag. The region of the last field represents the "finished writing
-- output here region", so that's the region that should be threaded.
type RightmostRegEnv = M.Map LocVar RegVar

-- Location arguments
type FnLocArgs = [LRM]

-- Allocation env
type AllocEnv = M.Map Var TyCon

--
type EnvForRAN = M.Map LocVar RegVar

-- A ordered list of locations within each region.
type OrderedLocsEnv = M.Map RegVar [LocVar]

threadRegions :: NewL2.Prog2 -> PassM NewL2.Prog2
threadRegions Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (threadRegionsFn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  threadRegionsExp ddefs fundefs [] M.empty env2 M.empty M.empty M.empty M.empty M.empty S.empty S.empty mn
  return $ Prog ddefs fundefs' mainExp'

threadRegionsFn :: DDefs Ty2 -> FunDefs2 -> NewL2.FunDef2 -> PassM NewL2.FunDef2
threadRegionsFn ddefs fundefs f@FunDef{funName,funArgs,funTy,funBody} = do
  let initRegEnv = M.fromList $ map (\(LRM lc r _) -> (lc, regionToVar r)) (locVars funTy)
      initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
      fn :: Ty2 -> M.Map Var TyCon -> M.Map Var TyCon
      fn = (\ty acc -> case unTy2 ty of
                         PackedTy tycon loc -> M.insert loc tycon acc
                         ProdTy tys -> foldr fn acc (map MkTy2 tys)
                         _ -> acc)
      rlocs_env = foldr fn M.empty (arrIns funTy)
      wlocs_env = fn (arrOut funTy) M.empty
      fnlocargs = locVars funTy
      region_locs = M.fromList $ map (\(LRM l r _m) -> (regionToVar r, [l])) (locVars funTy)
  bod' <- threadRegionsExp ddefs fundefs fnlocargs initRegEnv env2 M.empty rlocs_env wlocs_env M.empty region_locs S.empty S.empty funBody
  -- Boundschecking
  dflags <- getDynFlags
  let bod'' = if gopt Opt_BigInfiniteRegions dflags
              then bod'
              -- This function is always given a BigInfinite region.
              else if isCopySansPtrsFunName funName
              then bod'
              else
                let packed_outs = getPackedTys (unTy2 (arrOut funTy))
                    locs_tycons = foldr
                                    (\ty acc ->
                                         case ty of
                                           PackedTy t loc ->  M.insert loc t acc
                                           _ -> acc)
                                    M.empty
                                    packed_outs
                in foldr
                     (\lrm@(LRM loc reg mode) acc ->
                        if mode == Output
                        then let rv = toEndV $ regionToVar reg
                                 bc = boundsCheck ddefs (locs_tycons M.! loc)
                                 locarg = NewL2.Loc lrm
                                 regarg = NewL2.Reg rv mode
                             in -- dbgTraceIt ("boundscheck" ++ sdoc ((locs_tycons M.! loc), bc)) $
                                LetE ("_",[],MkTy2 IntTy, Ext$ BoundsCheck bc regarg locarg) acc
                        else acc)
                     bod'
                     (locVars funTy)
  return $ f {funBody = bod''}

threadRegionsExp :: DDefs Ty2 -> FunDefs2 -> [LRM] -> RegEnv -> Env2 Ty2
                 -> RightmostRegEnv -> AllocEnv -> AllocEnv -> EnvForRAN
                 -> OrderedLocsEnv -> S.Set LocVar -> S.Set LocVar
                 -> NewL2.Exp2 -> PassM NewL2.Exp2
threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs ex =
  case ex of

    AppE f applocs args -> do
      let ty = gRecoverType ddefs env2 ex
          argtys = map (gRecoverType ddefs env2) args
          argtylocs = concatMap locsInTy argtys
          in_regs = foldr (\x acc -> if S.member x indirs || S.member x redirs
                                     then (EndOfReg_Tagged x) : acc
                                     else case M.lookup x renv of
                                            Just r -> (NewL2.EndOfReg r Input (toEndV r)) : acc
                                            Nothing -> acc)
                    [] argtylocs
      -- If this function returns a Packed type, it'll have input and output
      -- locations and therefore, input and output regions.
      if hasPacked (unTy2 ty)
      then do
        let out_tylocs = locsInTy ty
        let out_regs = map (\l -> let r = (renv # l) in NewL2.EndOfReg r Output (toEndV r)) out_tylocs
        let newapplocs = in_regs ++ out_regs ++ applocs
        return $ AppE f newapplocs args
      -- Otherwise, only input regions.
      else do
        let newapplocs = in_regs ++ applocs
        return $ AppE f newapplocs args

    LetE (v,locs,ty, (AppE f applocs args)) bod -> do
        let argtylocs = concatMap
                        (\arg ->
                             let argty = gRecoverType ddefs env2 arg in
                             case arg of
                               VarE w ->
                                 case unTy2 argty of
                                   -- Indirection or redirection cursor.
                                   CursorTy -> [w]
                                   _ -> locsInTy argty
                               _ -> locsInTy argty)
                        args
        let in_regargs =
              foldr (\x acc -> if S.member x indirs || S.member x redirs
                               then (EndOfReg_Tagged x) : acc
                               else case M.lookup x renv of
                                           Just r -> (NewL2.EndOfReg r Input (toEndV r)) : acc
                                           Nothing -> acc)
              [] argtylocs
        --------------------
        let outretlocs = if hasPacked (unTy2 ty) then locsInTy ty else []
            out_regvars = map (renv #) outretlocs
        out_regvars' <- mapM (\r -> gensym r) out_regvars
        let out_regargs = map (\r -> NewL2.EndOfReg r Output (toEndV r)) out_regvars
        let out_regargs' = map (\r -> NewL2.EndOfReg r Output (toEndV r)) out_regvars'

        -- Indirections will return end-of-input-region cursor of the region
        -- where they're written, and not of their target.
        let in_regvars = map (renv #) argtylocs
        in_regvars' <- mapM (\r -> gensym r) in_regvars
        let in_regargs' = map (\r -> NewL2.EndOfReg r Input (toEndV r)) in_regvars'
        --------------------
        let ran_endofregs = map (\loc -> (loc,renv # loc)) $
                            map (\(PackedTy _ loc) -> loc) $
                            getPackedTys (unTy2 ty)
        let rans_env1 = rans_env `M.union` (M.fromList ran_endofregs)
        --------------------
        let newapplocs = in_regargs ++ out_regargs ++ applocs
        let newretlocs = in_regargs' ++ out_regargs' ++ locs
        --------------------
        -- 'locs' only has end-witnesses up to this pass. Make their regions
        -- same as regions of the locations that the function traverses.
        let traversed_indices = let fnty = funTy (fundefs # f) in
                                      map fst $
                                      filter (\(_i,loc) -> Traverse loc `S.member` (arrEffs fnty)) $
                                      zip [0..] (allLocVars fnty)
        let renv1 = M.fromList $ zip (map toLocVar locs)
                                     (map (\i -> let zipped = zip in_regvars in_regvars'
                                                     r = renv # (argtylocs !! i)
                                                     Just r' = lookup r zipped
                                                 in r')
                                          traversed_indices)
        let renv2 = M.union renv1 renv
        -- Update input and returned locations to point to the fresh regions
        let region_locs' = foldr (\(r,r') acc -> M.insert r' (acc # r) acc) region_locs (zip in_regvars in_regvars')
        let region_locs'' = foldr (\(r,r') acc -> M.insert r' (acc # r) acc) region_locs' (zip out_regvars out_regvars')
        let renv3 =
              foldr (\(lc,r,r') acc ->
                       M.insert lc r' $
                       M.map (\w -> if w == r then r' else w) acc)
              renv2
              (L.zip3 outretlocs out_regvars out_regvars')
        let (renv4,region_locs''') =
              foldr (\(lc,r,r') (acc1,acc2) ->
                       if S.member lc indirs then (acc1,acc2) else
                         let locs_in_r = (region_locs'' # r)
                         in case L.elemIndex lc locs_in_r of
                              Just idx -> if idx == (length locs_in_r - 1)
                                          then let fake_last_loc = toVar "fake_" `varAppend` lc
                                                   acc1' = M.insert fake_last_loc r' acc1
                                                   acc2' = M.adjust (\ls -> ls ++ [fake_last_loc]) r acc2
                                                   acc2'' = M.insert r' (acc2' # r) acc2'
                                                   acc2''' = foldr (\lc2 acc3 -> M.adjust (\ls -> ls ++ [fake_last_loc]) (acc1' # lc2) acc3) acc2'' locs_in_r
                                               in (acc1', acc2''')
                                          else let (_, to_update) = splitAt (idx+1) locs_in_r
                                                   updated = M.mapWithKey (\key val -> if key `elem` to_update then r' else val) acc1
                                               in (updated, acc2)
                              Nothing -> error $ "threadRegionsExp: unbound loc " ++ sdoc (lc,locs_in_r,indirs,region_locs',r))
              (renv3, region_locs'')
              (L.zip3 argtylocs in_regvars in_regvars')
        -- TODO: only keep the rightmost end-of-input-region cursor in renv.
        --------------------
        let env2' = extendVEnv v ty env2
            rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
            wlocs_env' = foldr (\loc acc -> M.delete loc acc) wlocs_env (locsInTy ty)
        bod' <- threadRegionsExp ddefs fundefs fnLocArgs renv4 env2' lfenv rlocs_env' wlocs_env' rans_env1 region_locs''' indirs redirs bod
        let -- free = S.fromList $ freeLocVars bod
            free = ss_free_locs (S.fromList (v : locsInTy ty ++ (map toLocVar locs))) env2' bod
            free_rlocs = free `S.intersection` (M.keysSet rlocs_env')
            free_wlocs = free `S.intersection` (M.keysSet wlocs_env')
        (rpush,wpush,rpop,wpop) <- ss_ops free_rlocs free_wlocs
        let binds = rpush ++ wpush ++ [(v, newretlocs, ty, AppE f newapplocs args)] ++ wpop ++ rpop
        (pure $ mkLets binds bod')


    LetE (v,locs,ty, (SpawnE f applocs args)) bod -> do
      let e' = LetE (v,locs,ty, (AppE f applocs args)) bod
      e'' <- threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs e'
      pure $ changeAppToSpawn f args e''

    -- AUDITME: this causes all all DataConE's to return an additional cursor.
    LetE (v,locs,ty@(MkTy2 (PackedTy _ loc)), rhs@(DataConE _ _ args)) bod -> do
      let reg_of_tag = renv M.! loc
          lfenv' = case args of
                     [] -> lfenv
                     _  ->
                       let last_ty = gRecoverType ddefs env2 (last args) in
                       case unTy2 last_ty of
                          PackedTy _ last_loc -> do
                            let reg_of_last_arg = renv M.! last_loc
                            if reg_of_tag /= reg_of_last_arg
                            then M.insert loc reg_of_last_arg lfenv
                            else lfenv
                          _ -> lfenv
      let rans_env1 = M.insert loc (renv # loc) rans_env
      let env2' = extendVEnv v ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc2 acc -> M.delete loc2 acc) wlocs_env (locsInTy ty)
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv' rlocs_env' wlocs_env' rans_env1 region_locs indirs redirs bod

    LetE (v,locs,ty@(MkTy2 (PackedTy _ loc)),rhs@(Ext (IndirectionE{}))) bod -> do
      let rans_env' = M.insert loc (renv # loc) rans_env
      let env2' = extendVEnv v ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc2 acc -> M.delete loc2 acc) wlocs_env (locsInTy ty)
      bod' <- threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv rlocs_env' wlocs_env' rans_env' region_locs indirs redirs bod
      pure $ LetE (v,locs,ty,rhs) bod'

    Ext (StartOfPkd cur) -> do
      let (PackedTy _ loc) = unTy2 (lookupVEnv cur env2)
      case M.lookup loc rans_env of
        Just reg -> return $ Ext $ TagCursor loc (toEndV reg)
        Nothing -> error $ "threadRegionsExp: unbound " ++ sdoc (loc, rans_env)

    -- Sometimes, this expression can have RetE forms. We should collect and update
    -- the locs here appropriately.
    LetE (v,locs,ty, rhs@(TimeIt{})) bod -> do
       rhs' <- go rhs
       let retlocs = findRetLocs rhs'
           newretlocs = retlocs ++ locs
       let env2' = extendVEnv v ty env2
           rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
           wlocs_env' = foldr (\loc acc -> M.delete loc acc) wlocs_env (locsInTy ty)
       LetE (v, newretlocs,ty, rhs') <$>
         threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv rlocs_env' wlocs_env' rans_env region_locs indirs redirs bod

    LetE (v,locs,ty,rhs@(Ext (AllocateTagHere x x_tycon))) bod -> do
      let -- x_tycon = (wlocs_env # x)
          rlocs_env' = M.insert x x_tycon rlocs_env
          wlocs_env' = M.delete x wlocs_env
      (LetE (v,locs,ty,rhs)) <$>
        threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnv v ty env2) lfenv rlocs_env' wlocs_env' rans_env region_locs indirs redirs bod

    LetE (v,locs,ty, rhs) bod ->
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnv v ty env2) lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs bod

    WithArenaE v e ->
      WithArenaE v <$> threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnv v (MkTy2 ArenaTy) env2) lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs e

    Ext ext ->
      case ext of
        AddFixed{} -> return ex
        LetLocE loc FreeLE bod ->
          Ext <$> LetLocE loc FreeLE <$>
            threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs bod
        -- Update renv with a binding for loc
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                      StartOfRegionLE r      -> regionToVar r
                      InRegionLE r           -> regionToVar r
                      AfterConstantLE _ lc   -> renv # (toLocVar lc)
                      AfterVariableLE _ lc _ -> renv # (toLocVar lc)
                      FromEndLE lc           -> renv # (toLocVar lc)
              wlocs_env' = M.insert loc hole_tycon wlocs_env
              region_locs' = case rhs of
                               AfterConstantLE{} -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                               AfterVariableLE{} -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                               StartOfRegionLE{} -> M.insert reg [loc] region_locs
                               _ -> region_locs
          Ext <$> LetLocE loc rhs <$>
            threadRegionsExp ddefs fundefs fnLocArgs (M.insert loc reg renv) env2 lfenv rlocs_env wlocs_env' rans_env region_locs' indirs redirs bod

        RetE locs v -> do
          let ty = lookupVEnv v env2
              fn m = (\r -> NewL2.EndOfReg r m (toEndV r))
              outtylocs = locsInTy ty
              outtyregvars =
                foldr (\loc acc -> case M.lookup loc lfenv of
                                     Nothing -> (renv # loc) : acc
                                     Just r  -> r : acc)
                [] outtylocs
              outtyregargs = map (fn Output) outtyregvars
              inregvars = map (\lrm -> let r = renv # (lrmLoc lrm)
                                           last_loc = last (region_locs # r)
                                           r' = (renv # last_loc)
                                       in r') $
                          filter (\lrm -> lrmMode lrm == Input) fnLocArgs
              inregargs = map (fn Input) inregvars
              newlocs = inregargs ++ outtyregargs
          return $ Ext $ RetE (newlocs ++ locs) v

        TagCursor a b -> return $ Ext $ TagCursor a b
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
          let reg = toEndV (renv # (toLocVar cur))
          return $ Ext $ BoundsCheck sz (NewL2.EndOfReg reg Output (toEndV reg)) cur
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
          PackedTy _ tyloc = unTy2 (lookupVEnv v env2)
          reg = renv M.! tyloc
      CaseE scrt <$> mapM (docase reg renv env2 lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{} -> error "threadRegionsExp: Unbound SpawnE"
    SyncE    -> pure ex
    MapE{}  -> error $ "threadRegionsExp: TODO MapE"
    FoldE{} -> error $ "threadRegionsExp: TODO FoldE"

  where
    go = threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env rans_env region_locs indirs redirs

    docase reg renv1 env21 lfenv1 rlocs_env1 wlocs_env1 rans_env1 region_locs1 indirs1 redirs1 (dcon,vlocargs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locargs) = unzip vlocargs
          locs = map toLocVar locargs
          renv0  = if isIndirectionTag dcon || isRedirectionTag dcon
                   then foldr (\lc acc -> M.insert lc reg acc) renv1 vars
                   else renv1
          renv1' = foldr (\lc acc -> M.insert lc reg acc) renv0 locs
          env21' = extendPatternMatchEnv dcon ddefs vars locs env21
          rlocs_env1' = foldr (\(loc,ty) acc ->
                                case unTy2 ty of
                                  PackedTy tycon _ -> M.insert loc tycon acc
                                  _ -> acc)
                              rlocs_env1
                              (fragileZip locs (lookupDataCon ddefs dcon))
          indirs1' = if isIndirectionTag dcon
                     then S.insert (head vars) indirs1
                     else indirs1
          redirs1' = if isRedirectionTag dcon
                     then S.insert (head vars) redirs1
                     else redirs1
          region_locs1' = if isIndirectionTag dcon || isRedirectionTag dcon
                          then M.adjust (\val -> val ++ take 1 vars) reg region_locs1
                          else M.adjust (\val -> val ++ locs) reg region_locs1
      (dcon,vlocargs,) <$>
         (threadRegionsExp ddefs fundefs fnLocArgs renv1' env21' lfenv1 rlocs_env1' wlocs_env1 rans_env1 region_locs1' indirs1' redirs1' bod)

    ss_free_locs :: S.Set Var -> Env2 Ty2 -> Exp2 -> S.Set Var
    ss_free_locs bound env20 ex0 =
                     S.map (\w -> case M.lookup w (vEnv env20) of
                                       -- assumption: it's a location
                                       Nothing -> w
                                       Just (MkTy2 (PackedTy _ loc)) -> loc
                                       Just wty -> error $ "threadRegionsExp: unexpected type " ++ show (w,wty))
                           (allFreeVars_sans_datacon_args ex0 `S.difference`
                            (bound `S.union`
                             M.keysSet (M.filter (not . isPackedTy . unTy2) (vEnv env20)) `S.union`
                             M.keysSet (fEnv env20)))

    hole_tycon = "HOLE"

    ss_ops :: S.Set Var -> S.Set Var ->
              PassM
              ([(Var, [LocArg], Ty2, Exp2)], [(Var, [LocArg], Ty2, Exp2)],
               [(Var, [LocArg], Ty2, Exp2)], [(Var, [LocArg], Ty2, Exp2)])
    ss_ops free_rlocs free_wlocs = do
          rpush <- (foldrM (\x acc -> do
                             push <- gensym "ss_push"
                             let tycon = rlocs_env # x
                             if tycon == hole_tycon
                             then pure acc
                             else pure ((push,[],MkTy2 (ProdTy []), Ext $ SSPush Read x (toEndV (renv # x)) tycon) : acc))
                           []
                           free_rlocs) :: PassM [(Var, [LocArg], Ty2, Exp2)]
          wpush <- (foldrM (\x acc -> do
                             push <- gensym "ss_push"
                             let tycon = wlocs_env # x
                             if tycon == hole_tycon
                             then pure acc
                             else pure ((push,[],MkTy2 (ProdTy []), Ext $ SSPush Write x (toEndV (renv # x)) tycon) : acc))
                           []
                           free_wlocs) :: PassM [(Var, [LocArg], Ty2, Exp2)]
          let rpop = map (\(x,locs,ty,Ext (SSPush a b c _)) -> (x,locs,ty,Ext (SSPop a b c))) (reverse rpush)
              wpop = map (\(x,locs,ty,Ext (SSPush a b c _)) -> (x,locs,ty,Ext (SSPop a b c))) (reverse wpush)
          pure (rpush,wpush,rpop,wpop)

    updRLocsEnv t acc =
                 case t of
                   PackedTy tycon loc -> M.insert loc tycon acc
                   ProdTy tys -> foldr updRLocsEnv acc tys
                   _ -> acc

-- Inspect an AST and return locations in a RetE form.
findRetLocs :: Exp2 -> [LocArg]
findRetLocs e0 = go e0 []
  where
    go :: Exp2 -> [LocArg] -> [LocArg]
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
            StartOfPkd{}      -> acc
            TagCursor{}    -> acc
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
                               else if hasPacked (unTy2 ty)
                               then ( bytes, True )
                               else ( bytes + (fromJust $ sizeOfTy (unTy2 ty)), False ))
                        (0, False)
                        tys
      tyss = map (lookupDataCon ddefs) dcons
      vals = map (fst . spaceReqd) tyss
      -- Add a byte for the tag.
      num_bytes = (1 + maximum vals)
  -- Reserve additional space for a redirection node or a forwarding pointer.
  in num_bytes + 9

----------------------------------------

-- gFreeVars ++ locations ++ region variables - (args to datacons)
allFreeVars_sans_datacon_args :: Exp2 -> S.Set Var
allFreeVars_sans_datacon_args ex =
  case ex of
    AppE _ locs args -> S.fromList (map toLocVar locs) `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    PrimAppE _ args -> (S.unions (map allFreeVars_sans_datacon_args args))
    LetE (v,locs,_,rhs) bod -> (S.fromList (map toLocVar locs) `S.union` (allFreeVars_sans_datacon_args rhs) `S.union` (allFreeVars_sans_datacon_args bod))
                               `S.difference` S.singleton v
    IfE a b c -> allFreeVars_sans_datacon_args a `S.union` allFreeVars_sans_datacon_args b `S.union` allFreeVars_sans_datacon_args c
    MkProdE args -> (S.unions (map allFreeVars_sans_datacon_args args))
    ProjE _ bod -> allFreeVars_sans_datacon_args bod
    CaseE scrt brs -> (allFreeVars_sans_datacon_args scrt) `S.union` (S.unions (map (\(_,vlocs,c) -> allFreeVars_sans_datacon_args c `S.difference`
                                                                                   S.fromList (map fst vlocs) `S.difference`
                                                                                   S.fromList (map (toLocVar . snd) vlocs))
                                                                  brs))
    DataConE loc _ _args -> S.singleton (toLocVar loc)
    TimeIt e _ _ -> allFreeVars_sans_datacon_args e
    WithArenaE _ e -> allFreeVars_sans_datacon_args e
    SpawnE _ locs args -> S.fromList (map toLocVar locs) `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    Ext ext ->
      case ext of
        LetRegionE r _sz _ty bod -> S.delete (regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetParRegionE r _sz _ty bod -> S.delete (regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetLocE loc locexp bod -> S.delete loc (allFreeVars_sans_datacon_args bod `S.union` gFreeVars locexp)
        StartOfPkd cur  -> S.singleton cur
        TagCursor a b-> S.fromList [a,b]
        RetE locs v     -> S.insert v (S.fromList (map toLocVar locs))
        FromEndE loc    -> S.singleton (toLocVar loc)
        BoundsCheck _ reg cur -> S.fromList [toLocVar reg, toLocVar cur]
        IndirectionE _ _ (a,b) (c,d) _ -> S.fromList $ [toLocVar a, b, toLocVar c, d]
        AddFixed v _    -> S.singleton v
        GetCilkWorkerNum-> S.empty
        LetAvail vs bod -> S.fromList vs `S.union` gFreeVars bod
        AllocateTagHere loc _ -> S.singleton loc
        AllocateScalarsHere loc -> S.singleton loc
        SSPush _ a b _ -> S.fromList [a,b]
        SSPop _ a b -> S.fromList [a,b]
    _ -> gFreeVars ex
