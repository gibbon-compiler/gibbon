{-| Do all things necessary to compile parallel allocations to a single region.

In the sequential semantics, (letloc-after x) can only run after x is written to
the store. In the parallel version, we relax this requirement. Every letloc-after
leads to creation of a new region, and we later tie things together with pointers.

    let x     = spawn (foo [l1])
    letloc l2 = after x
    let y     = foo [l2]
    _         = sync

will be transformed to:

    let x     = spawn (foo [l1])
    letregion r3
    letloc l3 = start r3
    let y     = foo [l3]
    _         = sync
    letloc l2 = after x
    tie l2 l3

Need a better name for this pass.

-}

module Gibbon.Passes.ParAlloc (parAlloc) where

import           Control.Monad ( when )
import           Data.Foldable ( foldrM )
import qualified Data.Map as M
import qualified Data.Set as S

import           Gibbon.L2.Syntax
import           Gibbon.Common
import           Gibbon.DynFlags

--------------------------------------------------------------------------------

-- Maps a location to a region variable
type RegEnv = M.Map LocVar Var

-- If there's a (letloc loc2 = after-variable x loc1) binding s.t. x is a
-- spawned variable (LHS of a SpawnE), this binding is swallowed into a
-- PAfter (loc2, (x, loc1)), and emitted back into the ast after a SyncE.
-- PVar is used to accomplish the same thing for let bindings.
data PendingBind = PVar   (Var,[LocVar],Ty2,Exp2)
                 | PAfter (LocVar, (Var, LocVar))
  deriving Show

-- The keys in this map are locations bound by a letloc-after, and they
-- map to the fresh locations that point to the start of a new region.
type AfterEnv = M.Map LocVar LocVar

parAlloc :: Prog2 -> PassM Prog2
parAlloc Prog{ddefs,fundefs,mainExp} = do
  region_on_spawn <- gopt Opt_RegionOnSpawn <$> getDynFlags
  fds' <- mapM parAllocFn $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  parAllocExp ddefs fundefs env2 M.empty M.empty Nothing [] S.empty S.empty region_on_spawn mn
  pure $ Prog ddefs fundefs' mainExp'
  where
    parAllocFn :: FunDef2 -> PassM FunDef2
    parAllocFn f@FunDef{funArgs,funTy,funBody} = do
      -- if hasParallelism funTy
      -- then do
        region_on_spawn <- gopt Opt_RegionOnSpawn <$> getDynFlags
        dflags <- getDynFlags
        let ret_ty = arrOut funTy
        when (hasParallelism funTy && hasPacked ret_ty && gopt Opt_Gibbon1 dflags) $
          error "gibbon: Cannot compile parallel allocations in Gibbon1 mode."

        let initRegEnv = M.fromList $ map (\(LRM lc r _) -> (lc, regionToVar r)) (locVars funTy)
            initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
            env2 = Env2 initTyEnv (initFunEnv fundefs)
            boundlocs = S.fromList (funArgs ++ allLocVars funTy ++ allRegVars funTy)
        bod' <- parAllocExp ddefs fundefs env2 initRegEnv M.empty Nothing [] S.empty boundlocs region_on_spawn funBody
        pure $ f {funBody = bod'}
      -- else pure f

parAllocExp :: DDefs2 -> FunDefs2 -> Env2 Ty2 -> RegEnv -> AfterEnv -> Maybe Var
            -> [PendingBind] -> S.Set Var -> S.Set LocVar -> Bool -> Exp2
            -> PassM Exp2
parAllocExp ddefs fundefs env2 reg_env after_env mb_parent_id pending_binds spawned boundlocs region_on_spawn ex =
  case ex of
    LetE (v, endlocs, ty, (SpawnE f locs args)) bod -> do
      let env2' = extendVEnv v ty env2
          spawned' = S.insert v spawned
          newlocs = map (\loc -> M.findWithDefault loc loc after_env) locs
          ty' = substLoc after_env ty
          pending_binds' = map
                      (\b -> case b of
                                PVar{} -> b
                                PAfter (loc1, (w, loc2)) -> PAfter (loc1, (w, M.findWithDefault loc2 loc2 after_env)))
                      pending_binds
          reg_env' = foldr (\b acc -> case b of
                                    PVar{} -> acc
                                    PAfter (loc1, (_, loc2)) ->
                                      case M.lookup loc1 reg_env of
                                        Nothing -> acc
                                        Just{}  -> M.insert loc1 (reg_env # loc2) acc)
                       reg_env pending_binds'
      parent_id <- gensym "parent_id"
      args' <- mapM go args
      bod'  <- parAllocExp ddefs fundefs env2' reg_env' after_env (Just parent_id) pending_binds' spawned' boundlocs region_on_spawn bod
      pure $ LetE (parent_id, [], IntTy, Ext GetCilkWorkerNum) $
             LetE (v, endlocs, ty', (SpawnE f newlocs args')) bod'

    LetE (v, endlocs, ty, SyncE) bod -> do
      let env2' = extendVEnv v ty env2
          boundlocs' = S.unions [spawned, boundlocs,(M.keysSet after_env)] `S.union`
                       foldr (\b acc ->
                                case b of
                                  PVar (a,_,_,_) -> S.insert a acc
                                  PAfter (a,_)   -> S.insert a acc)
                         S.empty pending_binds
      bod1 <- parAllocExp ddefs fundefs env2' reg_env after_env Nothing [] S.empty boundlocs' region_on_spawn bod
      bod2 <- foldrM
                 (\(from, to) acc -> do
                    indr <- gensym "pindr"
                    let Just tycon = foldr (\ty2 acc2 ->
                                                case ty2 of
                                                  PackedTy tycon2 loc | loc == from -> Just tycon2
                                                  _ -> acc2)
                                       Nothing (M.elems (vEnv env2))
                        indr_dcon = head $ filter isIndirectionTag $ getConOrdering ddefs tycon
                        rhs = Ext $ IndirectionE tycon indr_dcon (from, reg_env # from) (to, reg_env # to) (AppE "nocopy" [] [])
                    pure $ LetE (indr, [], PackedTy tycon from, rhs) acc)
                 bod1 (M.toList after_env)
      let bod3 = foldl
                     (\acc b ->
                        case b of
                          PVar vbnd -> mkLets [vbnd] acc
                          PAfter (loc1, (w, loc2)) -> Ext $ LetLocE loc1 (AfterVariableLE w loc2 False) $ acc)
                     bod2 pending_binds
      pure $ LetE (v, endlocs, ty, SyncE) bod3

    AppE f locs args -> do
      let newlocs = map (\loc -> M.findWithDefault loc loc after_env) locs
      args' <- mapM go args
      pure $ AppE f newlocs args'

    DataConE loc dcon args  -> do
      pure $ DataConE (M.findWithDefault loc loc after_env) dcon args

    LetE (v, locs, ty, rhs) bod -> do
      let ty' = substLoc after_env ty
          pending_binds' = map
                      (\b -> case b of
                                PVar{} -> b
                                PAfter (loc1, (w, loc2)) -> PAfter (loc1, (w, M.findWithDefault loc2 loc2 after_env)))
                      pending_binds
          reg_env' = foldr (\b acc -> case b of
                                    PVar{} -> acc
                                    PAfter (loc1, (_, loc2)) ->
                                      case M.lookup loc1 reg_env of
                                        Nothing -> acc
                                        Just{}  -> M.insert loc1 (reg_env # loc2) acc)
                       reg_env pending_binds'
          env2' = extendVEnv v ty env2

          vars = gFreeVars (substLocInExp after_env rhs) `S.difference` (M.keysSet fundefs)
          used = (allFreeVars (substLocInExp after_env rhs)) `S.difference` (M.keysSet fundefs)

      -- Swallow this binding, and add v to 'spawned'
      if not (S.disjoint vars spawned)
      then do
        rhs' <- go rhs
        let pending_binds'' = PVar (v, locs, ty', rhs') : pending_binds'
            spawned' = S.insert v spawned
        parAllocExp ddefs fundefs env2' reg_env' after_env mb_parent_id pending_binds'' spawned' boundlocs region_on_spawn bod
      -- Swallow this binding, and but don't add v to 'spawned'
      else if not (S.isSubsetOf used boundlocs)
      then do
        rhs' <- go rhs
        let pending_binds'' = PVar (v, locs, ty', rhs') : pending_binds'
        parAllocExp ddefs fundefs env2' reg_env' after_env mb_parent_id pending_binds'' spawned boundlocs region_on_spawn bod
      -- Emit this binding as usual
      else if S.disjoint vars spawned && S.isSubsetOf used boundlocs
      then do
        let boundlocs' = S.insert v boundlocs `S.union` (S.fromList locs)
        LetE <$> (v,locs,ty',) <$> go rhs
             <*> parAllocExp ddefs fundefs env2' reg_env' after_env mb_parent_id pending_binds' spawned boundlocs' region_on_spawn bod
      else error "parAlloc: LetE"

    -- Straightforward recursion
    VarE{}     -> pure ex
    LitE{}     -> pure ex
    CharE{}    -> pure ex
    FloatE{}   -> pure ex
    LitSymE{}  -> pure ex
    PrimAppE{} -> pure ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    CaseE scrt mp -> do
      let (VarE v) = scrt
          PackedTy _ tyloc = lookupVEnv v env2
          reg = reg_env # tyloc
      CaseE scrt <$> mapM (docase reg env2 reg_env after_env mb_parent_id pending_binds spawned boundlocs) mp
    TimeIt e ty b -> do
      e' <- go e
      pure $ TimeIt e' ty b
    WithArenaE v e -> (WithArenaE v) <$> go e
    SpawnE{} -> error "parAllocExp: unbound SpawnE"
    SyncE{}  -> error "parAllocExp: unbound SyncE"
    Ext ext  ->
      case ext of
        LetRegionE r sz ty bod       -> Ext <$> (LetRegionE r sz ty) <$>
                                    parAllocExp ddefs fundefs env2 reg_env after_env mb_parent_id pending_binds spawned (S.insert (regionToVar r) boundlocs) region_on_spawn bod
        LetParRegionE r sz ty bod    -> Ext <$> (LetParRegionE r sz ty) <$>
                                    parAllocExp ddefs fundefs env2 reg_env after_env mb_parent_id pending_binds spawned (S.insert (regionToVar r) boundlocs) region_on_spawn bod

        StartOfPkdCursor cur -> pure $ Ext $ StartOfPkdCursor cur
        TagCursor a b -> pure $ Ext $ TagCursor a b

        LetLocE loc locexp bod -> do
          case locexp of
            -- Binding is swallowed, and it's continuation allocates in a fresh region.
            AfterVariableLE v loc2 True | S.member v spawned -> do
              let (Just parent_id) = mb_parent_id
              cont_id <- gensym "cont_id"
              r <- gensym "rafter"
              newloc <- gensym "loc"
              let newreg = VarR r
                  reg = reg_env # loc2
                  after_env' = M.insert loc newloc after_env
                  pending_binds'   = PAfter (loc, (v, loc2)) : pending_binds
                  reg_env'   = M.insert loc reg $ M.insert newloc r reg_env
                  boundlocs1 = S.insert newloc boundlocs
                  boundlocs2 = S.insert loc $ S.insert v boundlocs
              -- If this continuation is stolen
              bod1 <- parAllocExp ddefs fundefs env2 reg_env' after_env' (Just cont_id) pending_binds' spawned boundlocs1 region_on_spawn (substLocInExp after_env' bod)
              -- If it's not stolen
              bod2 <- parAllocExp ddefs fundefs env2 reg_env' after_env (Just cont_id) pending_binds (S.delete v spawned) boundlocs2 region_on_spawn bod
              not_stolen  <- gensym "not_stolen"
              -- If we are given the --region_on_spawn flag, we disable the region-on-steal optimization.
              if S.member loc2 boundlocs && not region_on_spawn
              then
                pure $ LetE (cont_id, [], IntTy, Ext GetCilkWorkerNum) $
                       LetE (not_stolen, [], BoolTy, PrimAppE EqIntP [VarE cont_id, VarE parent_id]) $
                       IfE (VarE not_stolen)
                           (Ext $ LetAvail [v] $
                            Ext $ LetLocE loc (AfterVariableLE v loc2 False) bod2) -- don't allocate in a fresh region
                           (Ext $ LetParRegionE newreg Undefined Nothing $ Ext $ LetLocE newloc (StartOfRegionLE newreg) bod1)
              else
                pure $ Ext $ LetParRegionE newreg Undefined Nothing $ Ext $ LetLocE newloc (StartOfRegionLE newreg) bod1

            -- Binding is swallowed, but no fresh region is created. This can brought back safely after a sync.
            AfterVariableLE v loc2 True | not (S.member loc2 boundlocs) || not (S.member v boundlocs) -> do
              let pending_binds'  = PAfter (loc, (v, loc2)) : pending_binds
                  reg      = reg_env # loc2
                  reg_env' = M.insert loc reg reg_env
              parAllocExp ddefs fundefs env2 reg_env' after_env mb_parent_id pending_binds' spawned boundlocs region_on_spawn bod

            AfterVariableLE v loc2 True | S.member loc2 boundlocs && S.member v boundlocs -> do
              let reg = reg_env # loc2
                  reg_env'  = M.insert loc reg reg_env
                  boundlocs'= S.insert loc boundlocs
              bod' <- parAllocExp ddefs fundefs env2 reg_env' after_env mb_parent_id pending_binds spawned boundlocs' region_on_spawn bod
              pure $ Ext $ LetLocE loc (AfterVariableLE v loc2 False) bod'

            FreeLE -> do
              let boundlocs'= S.insert loc boundlocs
              bod' <- parAllocExp ddefs fundefs env2 reg_env after_env mb_parent_id pending_binds spawned boundlocs' region_on_spawn bod
              pure $ Ext $ LetLocE loc locexp bod'

            _ -> do
              let reg = case locexp of
                          StartOfRegionLE r  -> regionToVar r
                          InRegionLE r -> regionToVar r
                          AfterConstantLE _ lc   -> reg_env # lc
                          AfterVariableLE _ lc _ -> reg_env # lc
                          FromEndLE lc           -> reg_env # lc
                  reg_env'  = M.insert loc reg reg_env
                  boundlocs'= S.insert loc boundlocs
              bod' <- parAllocExp ddefs fundefs env2 reg_env' after_env mb_parent_id pending_binds spawned boundlocs' region_on_spawn bod
              pure $ Ext $ LetLocE loc locexp bod'
        RetE{}         -> pure ex
        FromEndE{}     -> pure ex
        BoundsCheck{}  -> pure ex
        IndirectionE{} -> pure ex
        AddFixed{}     -> pure ex
        GetCilkWorkerNum->pure ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
        AllocateTagHere{} -> pure ex
        AllocateScalarsHere{} -> pure ex
        SSPush{} -> pure ex
        SSPop{} -> pure ex
    MapE{}  -> error $ "parAllocExp: TODO MapE"
    FoldE{} -> error $ "parAllocExp: TODO FoldE"
  where
    go = parAllocExp ddefs fundefs env2 reg_env after_env mb_parent_id pending_binds spawned boundlocs region_on_spawn

    docase reg env21 reg_env2 after_env2 mb_parent_id2 pending_binds2 spawned2 boundlocs2 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          reg_env2' = foldr (\lc acc -> M.insert lc reg acc) reg_env2 locs
          env21'    = extendPatternMatchEnv dcon ddefs vars locs env21
          boundlocs2' = S.union (S.fromList (vars ++ locs)) boundlocs2
      (dcon,vlocs,) <$> parAllocExp ddefs fundefs env21' reg_env2' after_env2 mb_parent_id2 pending_binds2 spawned2 boundlocs2' region_on_spawn bod


substLocInExp :: M.Map LocVar LocVar -> Exp2 -> Exp2
substLocInExp mp ex1 =
  case ex1 of
    VarE{}    -> ex1
    LitE{}    -> ex1
    CharE{}   -> ex1
    FloatE{}  -> ex1
    LitSymE{} -> ex1
    AppE f locs args -> AppE f (map (\l -> sub l) locs) $ map go args
    PrimAppE f args  -> PrimAppE f $ map go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE (v,loc,ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE xs -> MkProdE $ map go xs
    ProjE i e  -> ProjE i $ go e
    DataConE loc dcon args -> DataConE (sub loc) dcon $ map go args
    CaseE scrt pats ->
      CaseE (go scrt) $ map (\(a,b,c) -> (a,b, go c)) pats
    TimeIt e ty b  -> TimeIt (go e) ty b
    WithArenaE v e -> WithArenaE v (go e)
    SpawnE{} -> ex1
    SyncE{}  -> ex1
    Ext ext ->
      case ext of
        LetRegionE r sz ty rhs  -> Ext $ LetRegionE r sz ty (go rhs)
        LetParRegionE r sz ty rhs -> Ext $ LetParRegionE r sz ty (go rhs)
        LetLocE l lhs rhs -> Ext $ LetLocE l (go2 lhs) (go rhs)
        StartOfPkdCursor v -> Ext $ StartOfPkdCursor v
        TagCursor a b  -> Ext $ TagCursor a b
        RetE locs v       -> Ext $ RetE (map (\l -> sub l) locs) v
        FromEndE loc      -> Ext $ FromEndE (sub loc)
        BoundsCheck i l1 l2 -> Ext $ BoundsCheck i (sub l1) (sub l2)
        IndirectionE tc dc (l1,v1) (l2,v2) e -> Ext $ IndirectionE tc dc (sub l1, v1) (sub l2, v2) (go e)
        AddFixed{}        -> ex1
        GetCilkWorkerNum  -> ex1
        LetAvail vs bod   -> Ext $ LetAvail vs (go bod)
        AllocateTagHere{} -> ex1
        AllocateScalarsHere{} -> ex1
        SSPush{} -> ex1
        SSPop{} -> ex1
    MapE{}  -> error "substLocInExpExp: TODO MapE"
    FoldE{}  -> error "substLocInExpExp: TODO FoldE"

  where go = substLocInExp mp
        sub loc = M.findWithDefault loc loc mp

        go2 lexp = case lexp of
                     StartOfRegionLE{} -> lexp
                     AfterConstantLE i loc -> AfterConstantLE i (sub loc)
                     AfterVariableLE i loc b -> AfterVariableLE i (sub loc) b
                     InRegionLE{} -> lexp
                     FreeLE -> lexp
                     FromEndLE loc -> FromEndLE (sub loc)
