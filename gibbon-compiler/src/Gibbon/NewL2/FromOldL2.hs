module Gibbon.NewL2.FromOldL2 ( fromOldL2, toOldL2, toOldL2Exp ) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Safe as Sf

import           Gibbon.L2.Syntax
import qualified Gibbon.NewL2.Syntax as New
import           Gibbon.Common

--------------------------------------------------------------------------------

-- Maps a location to a region
type LocEnv = M.Map LocVar New.LocArg

fromOldL2 :: Prog2 -> PassM New.Prog2
fromOldL2 Prog{ddefs,fundefs,mainExp} = do
  let ddefs' = M.map (fmap New.MkTy2) ddefs
  fds' <- mapM (fromOldL2Fn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> ((funName f),f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> do
                  let ty' = New.MkTy2 ty
                  mn' <- fromOldL2Exp ddefs fundefs M.empty env2 mn
                  pure $ Just (mn', ty')
  return $ Prog ddefs' fundefs' mainExp'


fromOldL2Fn :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM New.FunDef2
fromOldL2Fn ddefs fundefs f@FunDef{funArgs,funTy,funBody} = do
  let initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
      initLocEnv = M.fromList $ map (\lrm -> (lrmLoc lrm, New.Loc (New.fromLRM lrm))) (locVars funTy)
  bod' <- fromOldL2Exp ddefs fundefs initLocEnv env2 funBody
  return $ f { funBody = bod', funTy = fmap New.MkTy2 funTy }


fromOldL2Exp :: DDefs Ty2 -> FunDefs2 -> LocEnv -> Env2 Var Ty2 -> Exp2 -> PassM New.Exp2
fromOldL2Exp ddefs fundefs locenv env2 ex =
  case ex of
    AppE f locs args -> do
      args' <- mapM (go locenv env2) args
      let locargs = map (locenv # ) locs
      pure $ AppE f locargs args'

    SpawnE f locs args -> do
      args' <- mapM (go locenv env2) args
      let locargs = map (locenv # ) locs
      pure $ SpawnE f locargs args'

    PrimAppE pr args -> do
      args' <- mapM (go locenv env2) args
      let pr' = fmap New.MkTy2 pr
      pure $ PrimAppE pr' args'

    LetE (v, ewitnesses, ty, rhs) bod

      | SpawnE f applocs args <- rhs
      , not (null ewitnesses) ->
          do let e = LetE (v, ewitnesses, ty, AppE f applocs args) bod
             (LetE (v', ewitnesses', ty', AppE f' applocs' args') bod') <-
               go locenv env2 e
             pure $ LetE (v', ewitnesses', ty', SpawnE f' applocs' args') bod'

      | AppE f _applocs args <- rhs
      , not (null ewitnesses) ->
          do let fty = lookupFEnv f env2
                 effs = arrEffs fty
                 intys = arrIns fty
                 traversed_arg_pos =
                   map fst $
                   filter
                     (\(_i,inty) ->
                        case inty of
                          PackedTy _ loc -> S.member (Traverse loc) effs
                          _ -> False)
                     (zip [0..] intys)
                 traversed_args = map (args !!!) traversed_arg_pos
                 traversed_locs = foldr
                                      (\arg acc ->
                                         case arg of
                                           VarE w ->
                                             case lookupVEnv w env2 of
                                               PackedTy _ loc -> (loc:acc)
                                               -- For indirection/redirection pointers.
                                               CursorTy -> ((Single w):acc)
                                               _ -> acc
                                           _ -> acc)
                                      []
                                      traversed_args
                 locenv' = updModality ty locenv
                 (ewitnesses', locenv'') =
                        foldr
                          (\(witloc, tloc) (wits, env) ->
                             let (New.Loc lrem) = (env # (tloc))
                                 wit' = New.EndWitness lrem (unwrapLocVar witloc)
                                 env' = M.insert witloc wit' env
                             in (wit' : wits, env'))
                          ([], locenv')
                          (zip ewitnesses traversed_locs)
             rhs' <- go locenv env2 rhs
             bod' <- go locenv'' (extendVEnv v ty env2) bod
             let ty' = New.MkTy2 ty
             (pure $ LetE (v, ewitnesses', ty', rhs') bod')

      | CaseE _scrt _brs <- rhs
      , not (null ewitnesses) ->
          error "todo case"

      | null ewitnesses ->
          do let ty' = New.MkTy2 ty
             rhs' <- go locenv env2 rhs
             let locenv' = updModality ty locenv
             bod' <- go locenv' (extendVEnv v ty env2) bod
             pure $ LetE (v, [], ty', rhs') bod'

      | otherwise -> error $ "fromOldL2Exp: got" ++ sdoc ex


    CaseE scrt brs
      | VarE v <- scrt ->
          do let (PackedTy _ scrt_loc) = lookupVEnv v env2
                 (New.Loc lrem) = locenv # scrt_loc

                 docase (dcon, vlocs, rhs) = do

                   let mkLocArg loc = New.Loc $ lrem { New.lremLoc = loc }
                   let (vars,locs) = unzip vlocs
                       locargs = map mkLocArg locs
                       vlocs' = zip vars locargs
                       locenv' = foldr
                                   (\(New.Loc lrem') acc -> M.insert (New.lremLoc lrem') (New.Loc lrem') acc)
                                   locenv locargs
                       env2' = extendPatternMatchEnv dcon ddefs vars locs env2
                       locenv'' = if isRedirectionTag dcon || isIndirectionTag dcon
                                  then let ptr = Single $ Sf.headErr vars
                                       in M.insert ptr (mkLocArg ptr) locenv'
                                  else locenv'
                   rhs' <- go locenv'' env2' rhs
                   pure $ (dcon, vlocs', rhs')

             (CaseE (VarE v)) <$> mapM docase brs

      | otherwise -> error $ "fromOldL2Exp: CaseE " ++ sdoc scrt


    DataConE loc dcon args -> do
      let locarg = locenv # loc
      args' <- mapM (go locenv env2) args
      pure $ DataConE locarg dcon args'

    Ext ext ->
      case ext of
        LetRegionE reg reg_size mb_ty bod -> do
          bod' <- go locenv env2 bod
          pure $ Ext $ LetRegionE reg reg_size mb_ty bod'

        LetParRegionE reg reg_size mb_ty bod -> do
          bod' <- go locenv env2 bod
          pure $ Ext $ LetRegionE reg reg_size mb_ty bod'

        LetLocE loc rhs bod -> do
          let rhs' = fmap (locenv #) rhs
              locarg = toLocArg loc rhs locenv
          bod' <- go (M.insert loc locarg locenv) env2 bod
          pure $ Ext $ LetLocE loc rhs' bod'

        RetE locs v -> do
          let locargs = map (locenv #) locs
          pure $ Ext $ RetE locargs v

        FromEndE loc -> Ext <$> FromEndE <$> pure (locenv # loc)

        BoundsCheck i reg loc -> do
         let reg' = New.Reg (unwrapLocVar reg) Output
             loc' = locenv # loc
         pure $ Ext $ BoundsCheck i reg' loc'

        AddFixed v i -> pure $ Ext $ AddFixed v i

        TagCursor a b -> pure $ Ext $ TagCursor a b

        StartOfPkdCursor cur -> pure $ Ext $ StartOfPkdCursor cur

        IndirectionE tycon dcon (from,from_reg) (to,to_reg) e -> do
          e' <- go locenv env2 e
          pure $ Ext $
            IndirectionE
              tycon
              dcon
              (locenv # from, New.EndOfReg (unwrapLocVar from_reg) Output (toEndV (unwrapLocVar from_reg)))
              (locenv # to, New.EndOfReg (unwrapLocVar to_reg) Input (toEndV (unwrapLocVar to_reg)))
              e'
              -- (locenv # from, New.Reg (VarR from_reg) Output)
              -- (locenv # to, New.Reg (VarR to_reg) Input)

        GetCilkWorkerNum -> pure $ Ext GetCilkWorkerNum

        LetAvail avail rhs -> do
          rhs' <- go locenv env2 rhs
          pure $ Ext $ LetAvail avail rhs'

        AllocateTagHere loc tycon -> do
          -- let locarg = locenv # loc
          pure $ Ext $ AllocateTagHere loc tycon

        AllocateScalarsHere loc -> pure $ Ext $ AllocateScalarsHere loc

        SSPush mode loc end_loc tycon -> do
          pure $ Ext $ SSPush mode loc end_loc tycon

        SSPop mode loc end_loc -> do
          pure $ Ext $ SSPop mode loc end_loc

    -- straightforward recursion
    VarE v -> pure $ VarE v
    LitE i -> pure $ LitE i
    CharE i -> pure $ CharE i
    FloatE i  -> pure $ FloatE i
    LitSymE s -> pure $ LitSymE s
    IfE a b c -> IfE <$> go locenv env2 a <*> go locenv env2 b <*> go locenv env2 c
    MkProdE args  -> MkProdE <$> mapM (go locenv env2) args
    ProjE i e     -> (ProjE i) <$> go locenv env2 e
    TimeIt e ty b -> do e' <- go locenv env2 e
                        let ty' = New.MkTy2 ty
                        pure $ TimeIt e' ty' b
    WithArenaE v rhs -> (WithArenaE v) <$> go locenv env2 rhs
    SyncE   -> pure SyncE
    MapE{}  -> error "MapE"
    FoldE{} -> error "FoldE"
 where
  go = fromOldL2Exp ddefs fundefs

  toLocArg :: LocVar -> LocExp -> LocEnv -> New.LocArg
  toLocArg loc locexp locenv0 =
    case locexp of
      StartOfRegionLE reg -> New.Loc (New.LREM loc (regionToVar reg) (toEndV (regionToVar reg)) Output)
      AfterConstantLE _ loc2 ->
        let (New.Loc lrem) = locenv0 # loc2
        in New.Loc (New.LREM loc (New.lremReg lrem) (New.lremEndReg lrem) Output)
      AfterVariableLE _ loc2 _ ->
        let (New.Loc lrem) = locenv0 # loc2
        in New.Loc (New.LREM loc (New.lremReg lrem) (New.lremEndReg lrem) Output)
      InRegionLE reg ->
        New.Loc (New.LREM loc (regionToVar reg) (toEndV (regionToVar reg)) Output)
      FreeLE ->
        New.Loc (New.LREM loc "FREE_REG" "end_FREE_REG" Output)
      FromEndLE loc2 ->
        case (locenv0 # loc2) of
          New.Loc lrem -> New.Loc (lrem { New.lremLoc = loc })
          New.EndWitness lrem _ -> New.Loc ( lrem { New.lremLoc = loc } )
          oth -> error $ "toLocArg: got" ++ sdoc oth


  updModality :: Ty2 -> LocEnv -> LocEnv
  updModality ty env =
    let locs = locsInTy ty in
      foldr (\loc acc -> M.adjust (\locarg ->
                                     case locarg of
                                       New.Loc lrem -> New.Loc (lrem { New.lremMode = Input })
                                       _ -> locarg)
                         loc acc)
      env locs

--------------------------------------------------------------------------------


toOldL2 :: New.Prog2 -> PassM Prog2
toOldL2 Prog{ddefs,fundefs,mainExp} = do
  let ddefs' = M.map (fmap New.unTy2) ddefs
  fds' <- mapM toOldL2Fn $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> do
                  let ty' = New.unTy2 ty
                  mn' <- toOldL2Exp mn
                  pure $ Just (mn', ty')
  return $ Prog ddefs' fundefs' mainExp'


toOldL2Fn :: New.FunDef2 -> PassM FunDef2
toOldL2Fn f@FunDef{funTy,funBody} = do
  bod' <- toOldL2Exp funBody
  return $ f { funBody = bod', funTy = fmap New.unTy2 funTy }


toOldL2Exp :: New.Exp2 -> PassM Exp2
toOldL2Exp ex =
  case ex of
    AppE f locs args -> do
      args' <- mapM go args
      let locargs = map New.toLocVar locs
      pure $ AppE f locargs args'

    SpawnE f locs args -> do
      args' <- mapM go args
      let locargs = map New.toLocVar locs
      pure $ SpawnE f locargs args'

    PrimAppE pr args -> do
      args' <- mapM go args
      let pr' = fmap New.unTy2 pr
      pure $ PrimAppE pr' args'

    LetE (v, _ewitnesses, ty, rhs) bod -> do
             let ty' = New.unTy2 ty
             rhs' <- go rhs
             bod' <- go bod
             pure $ LetE (v, [], ty', rhs') bod'

    CaseE scrt brs
      | VarE v <- scrt ->
          do let docase (dcon, vlocs, rhs) = do
                   let (vars,locs) = unzip vlocs
                       locargs = map New.toLocVar locs
                       vlocs' = zip vars locargs
                   rhs' <- go rhs
                   pure $ (dcon, vlocs', rhs')

             (CaseE (VarE v)) <$> mapM docase brs

      | otherwise -> error $ "toOldL2Exp: CaseE " ++ sdoc scrt


    DataConE loc dcon args -> do
      args' <- mapM go args
      pure $ DataConE (New.toLocVar loc) dcon args'

    Ext ext ->
      case ext of
        LetRegionE reg reg_size mb_ty bod -> do
          bod' <- go bod
          pure $ Ext $ LetRegionE reg reg_size mb_ty bod'

        LetParRegionE reg reg_size mb_ty bod -> do
          bod' <- go bod
          pure $ Ext $ LetRegionE reg reg_size mb_ty bod'

        LetLocE loc rhs bod -> do
          let rhs' = fmap New.toLocVar rhs
          bod' <- go bod
          pure $ Ext $ LetLocE loc rhs' bod'

        StartOfPkdCursor cur -> do
          pure $ Ext $ StartOfPkdCursor cur

        TagCursor a b -> do
          pure $ Ext $ TagCursor a b

        RetE locs v -> do
          let locargs = map New.toLocVar locs
          pure $ Ext $ RetE locargs v

        FromEndE loc -> Ext <$> FromEndE <$> pure (New.toLocVar loc)

        BoundsCheck i reg loc -> do
         pure $ Ext $ BoundsCheck i (New.toLocVar reg) (New.toLocVar loc)

        AddFixed v i -> pure $ Ext $ AddFixed v i

        IndirectionE tycon dcon (from,from_reg) (to,to_reg) e -> do
          e' <- go e
          pure $ Ext $
            IndirectionE
              tycon
              dcon
              (New.toLocVar from, New.toLocVar from_reg)
              (New.toLocVar to, New.toLocVar to_reg)
              e'

        GetCilkWorkerNum -> pure $ Ext GetCilkWorkerNum

        LetAvail avail rhs -> do
          rhs' <- go rhs
          pure $ Ext $ LetAvail avail rhs'

        AllocateTagHere loc tycon -> do
          pure $ Ext $ AllocateTagHere loc tycon

        AllocateScalarsHere loc -> pure $ Ext $ AllocateScalarsHere loc

        SSPush mode loc end_loc tycon -> do
          pure $ Ext $ SSPush mode loc end_loc tycon

        SSPop mode loc end_loc -> do
          pure $ Ext $ SSPop mode loc end_loc

    -- straightforward recursion
    VarE v -> pure $ VarE v
    LitE i -> pure $ LitE i
    CharE i -> pure $ CharE i
    FloatE i  -> pure $ FloatE i
    LitSymE s -> pure $ LitSymE s
    IfE a b c -> IfE <$> go a <*> go b <*> go c
    MkProdE args  -> MkProdE <$> mapM go args
    ProjE i e     -> (ProjE i) <$> go e
    TimeIt e ty b -> do e' <- go e
                        let ty' = New.unTy2 ty
                        pure $ TimeIt e' ty' b
    WithArenaE v rhs -> (WithArenaE v) <$> go rhs
    SyncE   -> pure SyncE
    MapE{}  -> error "MapE"
    FoldE{} -> error "FoldE"
 where
  go = toOldL2Exp
