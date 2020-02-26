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
-- spawned variable (LHS of a SpawnE), this map will have a (loc2 -> (x, loc1))
-- entry. These are swallowed into this map, and emitted back into the ast
-- after a SyncE.
type LetLocAfters = [(LocVar, (Var, LocVar))]

-- The keys in this map are locations bound by a letloc-after, and they
-- map to the fresh locations that point to the start of a new region.
type AfterEnv = M.Map LocVar LocVar

parAlloc :: Prog2 -> PassM Prog2
parAlloc Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM parAllocFn $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  parAllocExp ddefs env2 M.empty M.empty Nothing [] [] S.empty S.empty mn
  pure $ Prog ddefs fundefs' mainExp'
  where
    parAllocFn :: FunDef2 -> PassM FunDef2
    parAllocFn f@FunDef{funArgs,funTy,funBody} =
      if hasParallelism funTy
      then do
        dflags <- getDynFlags
        let ret_ty = arrOut funTy
        when (hasPacked ret_ty && gopt Opt_Gibbon1 dflags) $
          error "gibbon: Cannot compile parallel allocations in Gibbon1 mode."

        let initRegEnv = M.fromList $ map (\(LRM lc r _) -> (lc, regionToVar r)) (locVars funTy)
            initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
            env2 = Env2 initTyEnv (initFunEnv fundefs)
        bod' <- parAllocExp ddefs env2 initRegEnv M.empty Nothing [] [] S.empty S.empty funBody
        pure $ f {funBody = bod'}
      else pure f

parAllocExp :: DDefs2 -> Env2 Ty2 -> RegEnv -> AfterEnv -> Maybe Var
            -> LetLocAfters -> [Binds Exp2] -> S.Set Var -> S.Set LocVar -> Exp2
            -> PassM Exp2
parAllocExp ddefs env2 reg_env after_env mb_parent_id afters pending_binds spawned boundlocs ex =
  case ex of
    LetE (v, endlocs, ty, (SpawnE f locs args)) bod -> do
      let env2' = extendVEnv v ty env2
          spawned' = S.insert v spawned
          newlocs = map (\loc -> M.findWithDefault loc loc after_env) locs
          ty' = substLoc after_env ty
          afters' = map (\(loc1, (w, loc2)) -> (loc1, (w, M.findWithDefault loc2 loc2 after_env))) afters
          reg_env' = foldr (\(loc1, (_, loc2)) acc ->
                              case M.lookup loc1 reg_env of
                                Nothing -> acc
                                Just{}  -> M.insert loc1 (reg_env # loc2) acc)
                       reg_env afters'
      parent_id <- gensym "parent_id"
      args' <- mapM go args
      bod'  <- parAllocExp ddefs env2' reg_env' after_env (Just parent_id) afters' pending_binds spawned' boundlocs bod
      pure $ LetE (parent_id, [], IntTy, Ext GetCilkWorkerNum) $
             LetE (v, endlocs, ty', (SpawnE f newlocs args')) bod'

    LetE (v, endlocs, ty, SyncE) bod -> do
      let env2' = extendVEnv v ty env2
          boundlocs' = S.union boundlocs (M.keysSet after_env)
      bod1 <- parAllocExp ddefs env2' reg_env M.empty Nothing [] [] S.empty boundlocs' bod
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
                     (\acc (loc1, (w, loc2)) -> Ext $ LetLocE loc1 (AfterVariableLE w loc2 False) $ acc)
                     bod2 afters

          bod4 = mkLets pending_binds bod3
      pure $ LetE (v, endlocs, ty, SyncE) bod4

    AppE f locs args -> do
      let newlocs = map (\loc -> M.findWithDefault loc loc after_env) locs
      args' <- mapM go args
      pure $ AppE f newlocs args'

    LetE (v, locs, ty, rhs) bod -> do
      let ty' = substLoc after_env ty
          afters' = map (\(loc1, (w, loc2)) -> (loc1, (w, M.findWithDefault loc2 loc2 after_env))) afters
          reg_env' = foldr (\(loc1, (_, loc2)) acc ->
                              case M.lookup loc1 reg_env of
                                Nothing -> acc
                                Just{}  -> M.insert loc1 (reg_env # loc2) acc)
                       reg_env afters'
          env2' = extendVEnv v ty env2

          vars = (gFreeVars rhs)
      if S.null (S.intersection vars spawned)
      then
        LetE <$> (v,locs,ty',) <$> go rhs
             <*> parAllocExp ddefs env2' reg_env' after_env mb_parent_id afters' pending_binds spawned boundlocs bod
      else do
        rhs' <- go rhs
        let pending_binds' = (v, locs, ty, rhs'):pending_binds
            spawned' = S.insert v spawned
        parAllocExp ddefs env2' reg_env' after_env mb_parent_id afters' pending_binds' spawned' boundlocs bod

    -- Straightforward recursion
    VarE{}     -> pure ex
    LitE{}     -> pure ex
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
      CaseE scrt <$> mapM (docase reg env2 reg_env after_env mb_parent_id afters pending_binds spawned boundlocs) mp
    DataConE{} -> pure ex
    TimeIt e ty b -> do
      e' <- go e
      pure $ TimeIt e' ty b
    WithArenaE v e -> (WithArenaE v) <$> go e
    SpawnE{} -> error "parAllocExp: unbound SpawnE"
    SyncE{}  -> error "parAllocExp: unbound SyncE"
    Ext ext  ->
      case ext of
        LetRegionE r bod       -> Ext <$> (LetRegionE r) <$> go bod
        LetLocE loc locexp bod -> do
          case locexp of
            AfterVariableLE v loc2 True | S.member v spawned -> do
              let (Just parent_id) = mb_parent_id
              cont_id <- gensym "cont_id"
              r <- gensym "r"
              newloc <- gensym "loc"
              let newreg = VarR r
                  reg = reg_env # loc2
                  after_env' = M.insert loc newloc after_env
                  afters'    = (loc, (v, loc2)) : afters
                  reg_env'   = M.insert loc reg $ M.insert newloc r reg_env
                  boundlocs1 = S.insert newloc boundlocs
                  boundlocs2 = S.insert loc boundlocs
              -- If this continuation is stolen
              bod1 <- parAllocExp ddefs env2 reg_env' after_env' (Just cont_id) afters' pending_binds spawned boundlocs1 bod
              -- If it's not stolen
              bod2 <- parAllocExp ddefs env2 reg_env' after_env (Just cont_id) afters pending_binds (S.delete v spawned) boundlocs2 bod
              not_stolen  <- gensym "not_stolen"
              if S.member loc2 boundlocs
              then
                pure $ LetE (cont_id, [], IntTy, Ext GetCilkWorkerNum) $
                       LetE (not_stolen, [], BoolTy, PrimAppE EqIntP [VarE cont_id, VarE parent_id]) $
                       IfE (VarE not_stolen)
                           (Ext $ LetAvail [v] $
                            Ext $ LetLocE loc (AfterVariableLE v loc2 False) bod2) -- don't allocate in a fresh region
                           (Ext $ LetRegionE newreg $ Ext $ LetLocE newloc (StartOfLE newreg) bod1)
              else
                pure $ Ext $ LetRegionE newreg $ Ext $ LetLocE newloc (StartOfLE newreg) bod1

            AfterVariableLE v loc2 True | not (S.member v spawned) && S.member loc2 boundlocs -> do
              let reg      = reg_env # loc2
                  reg_env' = M.insert loc reg reg_env
                  boundlocs' = S.insert loc boundlocs
              bod' <- parAllocExp ddefs env2 reg_env' after_env mb_parent_id afters pending_binds spawned boundlocs' bod
              pure $ Ext $ LetLocE loc (AfterVariableLE v loc2 False) bod'

            _ -> do
              let reg = case locexp of
                          StartOfLE r  -> regionToVar r
                          InRegionLE r -> regionToVar r
                          AfterConstantLE _ lc   -> reg_env # lc
                          AfterVariableLE _ lc _ -> reg_env # lc
                          FromEndLE lc           -> reg_env # lc
                          FreeLE                 -> undefined
                  reg_env'  = M.insert loc reg reg_env
                  boundlocs'= S.insert loc boundlocs
              bod' <- parAllocExp ddefs env2 reg_env' after_env mb_parent_id afters pending_binds spawned boundlocs' bod
              pure $ Ext $ LetLocE loc locexp bod'
        RetE{}         -> pure ex
        FromEndE{}     -> pure ex
        BoundsCheck{}  -> pure ex
        IndirectionE{} -> pure ex
        AddFixed{}     -> pure ex
        GetCilkWorkerNum->pure ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
    IsBigE e -> IsBigE <$> go e
    MapE{}  -> error $ "parAllocExp: TODO MapE"
    FoldE{} -> error $ "parAllocExp: TODO FoldE"
  where
    go = parAllocExp ddefs env2 reg_env after_env mb_parent_id afters pending_binds spawned boundlocs

    docase reg env21 reg_env2 after_env2 mb_parent_id2 afters2 pending_binds2 spawned2 boundlocs2 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          reg_env2' = foldr (\lc acc -> M.insert lc reg acc) reg_env2 locs
          env21'    = extendPatternMatchEnv dcon ddefs vars locs env21
          boundlocs2' = S.union (S.fromList locs) boundlocs2
      (dcon,vlocs,) <$> parAllocExp ddefs env21' reg_env2' after_env2 mb_parent_id2 afters2 pending_binds2 spawned2 boundlocs2' bod
