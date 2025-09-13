{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}

module Gibbon.Passes.ThreadRegions2 where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (foldrM)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe (fromJust)
import qualified Data.Set as S
import Gibbon.Common
import Gibbon.DynFlags
-- import Gibbon.NewL2.Syntax as L2

import Gibbon.L2.Syntax as Old
import Gibbon.NewL2.Syntax as NewL2
import qualified Safe as Sf
import System.IO (hPutStrLn, stderr)

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
type FnLocArgs = [LREM]

-- Allocation env
type AllocEnv = M.Map LocVar TyCon

-- Regions of packed values
type PkdEnv = M.Map LocVar RegVar

-- A ordered list of locations within each region.
type OrderedLocsEnv = M.Map RegVar [LocVar]

-- Bound variables that map to their corresponding shortcut pointers
type RanEnv = M.Map LocVar Var

threadRegions2 :: NewL2.Prog2 -> PassM NewL2.Prog2
threadRegions2 Prog {ddefs, fundefs, mainExp} = do
  fds' <- mapM (threadRegionsFn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f, f)) fds'
      env2 = Env2 M.empty (initFunEnv' fundefs)
  mainExp' <- case mainExp of
    Nothing -> return Nothing
    Just (mn, ty) ->
      Just . (,ty)
        <$> threadRegionsExp ddefs fundefs [] M.empty env2 M.empty M.empty M.empty M.empty M.empty M.empty S.empty S.empty mn
  return $ Prog ddefs fundefs' mainExp'

threadRegionsFn :: DDefs NewL2.Ty2 -> NewL2.FunDefs2 -> NewL2.FunDef2 -> PassM NewL2.FunDef2
threadRegionsFn ddefs fundefs f@FunDef {funName, funArgs, funTy, funMeta, funBody} = do
  let initRegEnv =
        M.fromList $
          map
            ( \(LRM lc r _) -> case r of
                SoAR _ _ -> (lc, regionToVar r)
                _ -> (lc, regionToVar r)
            )
            (locVars funTy)
      initTyEnv = M.fromList $ zip (map fromVarToFreeVarsTy funArgs) (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv' fundefs)
      fn :: NewL2.Ty2 -> M.Map LocVar TyCon -> M.Map LocVar TyCon
      fn =
        ( \ty acc -> case unTy2 ty of
            PackedTy tycon loc -> M.insert loc tycon acc
            ProdTy tys -> foldr fn acc (map MkTy2 tys)
            _ -> acc
        )
      rlocs_env = foldr fn M.empty (arrIns funTy)
      wlocs_env = fn (arrOut funTy) M.empty
      fnlocargs = map fromLRM (locVars funTy)
      region_locs =
        M.fromList $
          concatMap
            ( \(LRM l r _m) -> case r of
                SoAR dconr fregs ->
                  let parent_tup = (regionToVar r, [l])
                      dcon_tup = (regionToVar dconr, [getDconLoc l])
                      f_tuples =
                        map
                          (\(k, fr) -> (regionToVar fr, [getFieldLoc k l]))
                          fregs
                   in [parent_tup, dcon_tup] ++ f_tuples
                _ -> [(regionToVar r, [l])]
            )
            (locVars funTy)
  -- let bod' =  funBody
  bod' <- dbgTrace (minChatLvl) "Print region environment " dbgTrace (minChatLvl) (sdoc (initRegEnv)) dbgTrace (minChatLvl) "End print threadRegionsFn.\n" threadRegionsExp ddefs fundefs fnlocargs initRegEnv env2 M.empty rlocs_env wlocs_env M.empty region_locs M.empty S.empty S.empty funBody
  -- Boundschecking
  dflags <- getDynFlags
  let free_wlocs = S.fromList (map fromLocVarToFreeVarsTy (outLocVars funTy))
  let free_rlocs = S.fromList (map fromLocVarToFreeVarsTy (inLocVars funTy))
  let free_rlocs' =
        let tmp =
              concatMap
                ( \(x, ty) -> case unTy2 ty of
                    PackedTy _ loc -> [(Just x, (fromLocVarToFreeVarsTy loc))]
                    _ -> []
                )
                $ zip (map fromVarToFreeVarsTy funArgs) (arrIns funTy)
            tmp2 = map (\x -> (Nothing, x)) $ (S.toList free_rlocs) L.\\ (map snd tmp)
         in S.fromList $ tmp ++ tmp2
  (rpush, wpush, rpop, wpop) <- ss_ops free_rlocs' free_wlocs rlocs_env wlocs_env initRegEnv
  let no_eager_promote = gopt Opt_NoEagerPromote dflags
  let bod'' =
        -- This function is always given a BigInfinite region.
        if gopt Opt_BigInfiniteRegions dflags || isCopySansPtrsFunName funName
          then
            let packed_outs = getPackedTys (unTy2 (arrOut funTy))
                locs_tycons =
                  foldr
                    ( \ty acc ->
                        case ty of
                          PackedTy t loc -> M.insert loc t acc
                          _ -> acc
                    )
                    M.empty
                    packed_outs
                regInsts =
                  concatMap
                    ( \(LRM loc reg mode) ->
                        case reg of
                          SoAR dcReg fieldRegs ->
                            let dcreg = regionToVar dcReg
                                dcEndReg = toEndVRegVar dcreg
                                dcRegArg = NewL2.EndOfReg dcreg mode dcEndReg
                                regInst = [LetRegE (fromLocVarToRegVar (NewL2.toLocVar dcRegArg)) (GetDataConRegSoA (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                regInst' =
                                  concatMap
                                    ( \(d, freg) -> case freg of
                                        SoAR _ _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                        _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                    )
                                    fieldRegs
                             in regInst ++ regInst'
                          _ -> []
                    )
                    (locVars funTy)
                bod'' = L.foldr (\i acc -> Ext $ i acc) bod' regInsts
             in bod''
          else
            let packed_outs = getPackedTys (unTy2 (arrOut funTy))
                locs_tycons =
                  foldr
                    ( \ty acc ->
                        case ty of
                          PackedTy t loc -> M.insert loc t acc
                          _ -> acc
                    )
                    M.empty
                    packed_outs
                results =
                  map
                    ( \(LRM loc reg mode) ->
                        case reg of
                          SoAR dcReg fieldRegs ->
                            if mode == Output
                              then
                                let dcreg = regionToVar dcReg
                                    dcEndReg = toEndVRegVar dcreg
                                    fieldRegs' = map (\(_, freg) -> regionToVar freg) fieldRegs
                                    dcLoc = getDconLoc loc
                                    fieldLocs = getAllFieldLocsSoA loc
                                    fieldLocs' = map (\(k, floc) -> (k, floc)) fieldLocs
                                    dcLocArg = NewL2.Loc (LREM dcLoc dcreg dcEndReg mode)
                                    dcRegArg = NewL2.EndOfReg dcreg mode dcEndReg
                                    {- VS: TODO: I need to get find the correct integer for bounds check-}
                                    {- VS: New: each scalar field get a bound check size equal to the size of the field -}
                                    {- VS: As of 09.04.2025, we use a vector bounds check for an SoA region -}

                                    -- boundsCheckDcon = [("_",[],MkTy2 IntTy, Ext $ BoundsCheck 1 dcRegArg dcLocArg)]
                                    -- boundsCheckFields = concatMap (\(((dcon, idx), floc), freg) -> let ty = (lookupDataCon ddefs dcon) !! idx
                                    --                                                                 in case (unTy2 ty) of
                                    --                                                                      PackedTy{} -> []
                                    --                                                                      _ -> let
                                    --                                                                              size_of_ty = fromJust $ sizeOfTy (unTy2 ty)
                                    --                                                                             in [("_",[],MkTy2 IntTy, Ext $ BoundsCheck (size_of_ty) (NewL2.EndOfReg freg mode (toEndVRegVar freg)) (NewL2.Loc (LREM floc freg (toEndVRegVar freg) mode)))]
                                    --
                                    --                            ) $ zip fieldLocs' fieldRegs'
                                    boundsCheckDcon = [(1, dcRegArg, dcLocArg)]
                                    boundsCheckFields =
                                      concatMap
                                        ( \(((dcon, idx), floc), freg) ->
                                            let ty = (lookupDataCon ddefs dcon) !! idx
                                             in case (unTy2 ty) of
                                                  PackedTy {} -> []
                                                  _ ->
                                                    let size_of_ty = fromJust $ sizeOfTy (unTy2 ty)
                                                     in [(size_of_ty, (NewL2.EndOfReg freg mode (toEndVRegVar freg)), (NewL2.Loc (LREM floc freg (toEndVRegVar freg) mode)))]
                                        )
                                        $ zip fieldLocs' fieldRegs'
                                    boundsCheckVector = [("_", [], MkTy2 IntTy, Ext $ BoundsCheckVector (boundsCheckDcon ++ boundsCheckFields))]
                                    regInst = [LetRegE (fromLocVarToRegVar (NewL2.toLocVar dcRegArg)) (GetDataConRegSoA (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                    regInst' =
                                      concatMap
                                        ( \(d, freg) -> case freg of
                                            SoAR _ _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                            _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                        )
                                        fieldRegs
                                    -- Just in case the locations are not present, we release them here
                                    locInst = [LetLocE dcLoc (GetDataConLocSoA (NewL2.Loc (LREM loc (regionToVar reg) (toEndVRegVar (regionToVar reg)) mode)))]
                                    locInst' =
                                      concatMap
                                        ( \(d, floc) -> case floc of
                                            SoA _ _ -> [LetLocE (floc) (GetFieldLocSoA d (NewL2.Loc (LREM loc (regionToVar reg) (toEndVRegVar (regionToVar reg)) mode)))]
                                            _ -> [LetLocE floc (GetFieldLocSoA d (NewL2.Loc (LREM loc (regionToVar reg) (toEndVRegVar (regionToVar reg)) mode)))]
                                        )
                                        fieldLocs
                                 in (boundsCheckVector, locInst ++ locInst' ++ regInst ++ regInst')
                              else
                                let dcreg = regionToVar dcReg
                                    dcEndReg = toEndVRegVar dcreg
                                    dcRegArg = NewL2.EndOfReg dcreg mode dcEndReg
                                    regInst = [LetRegE (fromLocVarToRegVar (NewL2.toLocVar dcRegArg)) (GetDataConRegSoA (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                    regInst' =
                                      concatMap
                                        ( \(d, freg) -> case freg of
                                            SoAR _ _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                            _ -> [LetRegE (toEndVRegVar $ regionToVar freg) (GetFieldRegSoA d (NewL2.EndOfReg (regionToVar reg) Output (toEndVRegVar $ regionToVar reg)))]
                                        )
                                        fieldRegs
                                 in ([], regInst ++ regInst')
                          _ ->
                            if mode == Output
                              then
                                let rv = regionToVar reg
                                    end_rv = toEndVRegVar rv
                                    -- rv = end_reg
                                    bc = boundsCheck ddefs (locs_tycons M.! loc)
                                    locarg = NewL2.Loc (LREM loc rv end_rv mode)
                                    regarg = NewL2.EndOfReg rv mode end_rv
                                 in -- dbgTrace (minChatLvl) ("boundscheck" ++ sdoc ((locs_tycons M.! loc), bc)) $
                                    -- maintain shadowstack in no eager promotion mode
                                    ([("_", [], MkTy2 IntTy, Ext $ BoundsCheck bc regarg locarg)], [])
                              else ([], [])
                    )
                    (locVars funTy)
                boundschecks = concatMap fst results
                regInsts = concatMap snd results
             in -- If eager promotion is disabled, growing a region can also trigger a GC.
                if no_eager_promote && funCanTriggerGC funMeta
                  then
                    let lets = mkLets (rpush ++ wpush ++ boundschecks ++ wpop ++ rpop) bod'
                        bod'' = L.foldr (\i acc -> Ext $ i acc) lets regInsts
                     in bod''
                  else
                    let lets = mkLets boundschecks bod'
                        bod'' = L.foldr (\i acc -> Ext $ i acc) lets regInsts
                     in bod''

  return $ f {funBody = bod''}

threadRegionsExp ::
  DDefs NewL2.Ty2 ->
  NewL2.FunDefs2 ->
  [LREM] ->
  RegEnv ->
  Env2 FreeVarsTy NewL2.Ty2 ->
  RightmostRegEnv ->
  AllocEnv ->
  AllocEnv ->
  PkdEnv ->
  OrderedLocsEnv ->
  RanEnv ->
  S.Set LocVar ->
  S.Set LocVar ->
  NewL2.Exp2 ->
  PassM NewL2.Exp2
threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs ex =
  case ex of
    AppE f applocs args -> do
      let ty = gRecoverTypeLoc ddefs env2 ex
          argtys = map (gRecoverTypeLoc ddefs env2) args
          argtylocs = concatMap NewL2.locsInTy argtys
          in_regs =
            foldr
              ( \x acc ->
                  if S.member x indirs || S.member x redirs
                    -- Since a region should always point to just one cursor
                    -- Unwraping a regions stored in LocVar should be fine.
                    then (EndOfReg_Tagged (fromLocVarToRegVar x)) : acc
                    else case M.lookup x ran_env of
                      Just ran -> (EndOfReg_Tagged (fromVarToSingleRegVar ran)) : acc
                      Nothing -> case M.lookup x renv of
                        Just r -> (NewL2.EndOfReg r Input (toEndVRegVar r)) : acc
                        Nothing -> acc
              )
              []
              argtylocs
      let applocs' =
            map
              ( \loc -> case loc of
                  NewL2.Loc lrem ->
                    let x = lremLoc lrem
                     in if S.member x indirs || S.member x redirs
                          then NewL2.Loc (lrem {lremEndReg = toEndFromTaggedRegVar (fromLocVarToRegVar x)})
                          else loc
                  _ -> loc
              )
              applocs
      -- If this function returns a Packed type, it'll have input and output
      -- locations and therefore, input and output regions.
      if hasPacked (unTy2 ty)
        then do
          let out_tylocs = NewL2.locsInTy ty
          let out_regs = map (\l -> let r = (renv # l) in NewL2.EndOfReg r Output (toEndVRegVar r)) out_tylocs
          let newapplocs = in_regs ++ out_regs ++ applocs'
          return $ AppE f newapplocs args
        -- Otherwise, only input regions.
        else do
          let newapplocs = in_regs ++ applocs
          return $ AppE f newapplocs args
    LetE (v, locs, ty, (AppE f applocs args)) bod -> do
      let argtylocs =
            concatMap
              ( \arg ->
                  let argty = gRecoverTypeLoc ddefs env2 arg
                   in case arg of
                        VarE w ->
                          case unTy2 argty of
                            -- Indirection or redirection cursor.
                            CursorTy -> [singleLocVar w]
                            _ -> NewL2.locsInTy argty
                        _ -> NewL2.locsInTy argty
              )
              args
      let in_regargs =
            foldr
              ( \x acc ->
                  if S.member x indirs || S.member x redirs
                    then (EndOfReg_Tagged (fromLocVarToRegVar x)) : acc
                    else case M.lookup x ran_env of
                      Just ran -> (EndOfReg_Tagged (fromVarToSingleRegVar ran)) : acc
                      Nothing ->
                        case M.lookup x renv of
                          Just r -> (NewL2.EndOfReg r Input (toEndVRegVar r)) : acc
                          Nothing -> acc
              )
              []
              argtylocs
      --------------------
      let outretlocs = if hasPacked (unTy2 ty) then NewL2.locsInTy ty else []
          out_regvars = map (renv #) outretlocs
      out_regvars' <-
        mapM
          ( \r -> case r of
              SingleR rv -> SingleR <$> gensym rv
              SoARv (SingleR drv) frvs -> SoARv <$> (SingleR <$> gensym drv) <*> mapM (\(k, (frv)) -> (,) k <$> (genSymRegVar frv)) frvs
              _ -> error "threadRegionsExp: SoARv not implemented yet."
          )
          out_regvars
      let out_regargs = map (\r -> NewL2.EndOfReg r Output (toEndVRegVar r)) out_regvars
      let out_regargs' = map (\r -> NewL2.EndOfReg r Output (toEndVRegVar r)) out_regvars'

      -- Indirections will return end-of-input-region cursor of the region
      -- where they're written, and not of their target.
      let in_regvars = map (renv #) argtylocs
      in_regvars' <-
        mapM
          ( \r -> case r of
              SingleR rv -> SingleR <$> gensym rv
              SoARv (SingleR drv) frvs -> SoARv <$> (SingleR <$> gensym drv) <*> mapM (\(k, (frv)) -> (,) k <$> (genSymRegVar frv)) frvs
              _ -> error "threadRegionsExp: SoARv not implemented yet."
          )
          in_regvars
      let in_regargs' = map (\r -> NewL2.EndOfReg r Input (toEndVRegVar r)) in_regvars'
      --------------------
      let ran_endofregs =
            map (\loc -> (loc, renv # loc)) $
              map (\(PackedTy _ loc) -> loc) $
                getPackedTys (unTy2 ty)
      let !pkd_env1 = dbgTrace (minChatLvl) "Print stuff: " dbgTrace (minChatLvl) (sdoc (renv, in_regvars, in_regvars', out_regvars, out_regvars')) dbgTrace (minChatLvl) "End stuff.\n" pkd_env `M.union` (M.fromList ran_endofregs)
      --------------------
      let applocs' =
            map
              ( \loc -> case loc of
                  NewL2.Loc lrem ->
                    let x = lremLoc lrem
                     in if S.member x indirs || S.member x redirs
                          then NewL2.Loc (lrem {lremEndReg = toEndFromTaggedRegVar (fromLocVarToRegVar x)})
                          else loc
                  _ -> loc
              )
              applocs
      let newapplocs = in_regargs ++ out_regargs ++ applocs'
      let newretlocs = in_regargs' ++ out_regargs' ++ locs
      --------------------
      -- 'locs' only has end-witnesses up to this pass. Make their regions
      -- same as regions of the locations that the function traverses.
      let !traversed_indices =
            dbgTrace
              (minChatLvl)
              "Print (renv) in LetE: "
              dbgTrace
              (minChatLvl)
              (sdoc (renv, (v, locs, ty, (AppE f applocs args))))
              dbgTrace
              (minChatLvl)
              "End (renv) LetE.\n"
              let fnty = funTy (fundefs # f)
               in map fst $
                    filter (\(_i, loc) -> Traverse loc `S.member` (arrEffs fnty)) $
                      zip [0 ..] (allLocVars fnty)
      let !renv1 =
            M.fromList $
              zip
                (map toLocVar locs)
                ( map
                    ( \i ->
                        let zipped = zip in_regvars in_regvars'
                            r = renv # (argtylocs !! i)
                            Just r' = lookup r zipped
                         in r'
                    )
                    traversed_indices
                )
      let !renv2 = dbgTrace (minChatLvl) "Print (renv1) in LetE: " dbgTrace (minChatLvl) (sdoc (renv1, traversed_indices, (v, locs, ty, (AppE f applocs args)))) dbgTrace (minChatLvl) "End (renv1) LetE.\n" M.union renv1 renv

      -- Update input and returned locations to point to the fresh regions
      --

      let !region_locs1 =
            foldr
              ( \(r, r') acc ->
                  let rr' = case (M.lookup r acc) of
                        Just rr' -> rr'
                        Nothing -> []
                   in dbgTrace (minChatLvl) "Print (renv2) in LetE: " dbgTrace (minChatLvl) (sdoc (renv2, (v, locs, ty, (AppE f applocs args)))) dbgTrace (minChatLvl) "End (renv2) LetE.\n" M.insert r' rr' acc
              )
              region_locs
              (zip in_regvars in_regvars')
      let region_locs2 =
            foldr
              ( \(r, r') acc ->
                  let rr' = case (M.lookup r acc) of
                        Just rr' -> rr'
                        Nothing -> []
                   in M.insert r' rr' acc
              )
              region_locs1
              (zip out_regvars out_regvars')
      -- liftIO $ hPutStrLn stderr "RRRRRRRRRRRRRRRRR"
      -- [2022.10.04]: do outregvars need to updated like inregvars below?
      let (!renv3, !bod1) =
            dbgTrace
              (minChatLvl)
              "Print region_locs1: "
              dbgTrace
              (minChatLvl)
              (sdoc (region_locs1, region_locs2, in_regvars, in_regvars'))
              dbgTrace
              (minChatLvl)
              "End region_locs1.\n"
              foldr
              ( \(lc, r, r') (acc, bod_acc) ->
                  ( (M.insert lc r' $ M.map (\w -> if w == r then r' else w) acc),
                    substEndReg (Right r) (toEndVRegVar r') bod_acc
                  )
              )
              (renv2, bod)
              (L.zip3 outretlocs out_regvars out_regvars')
      let !(!renv4, !region_locs3, !bod2) =
            dbgTrace
              (minChatLvl)
              "Print (renv3) in LetE: "
              dbgTrace
              (minChatLvl)
              (sdoc (renv3, (v, locs, ty, (AppE f applocs args))))
              dbgTrace
              (minChatLvl)
              "End (renv3) LetE.\n"
              foldr
              ( \(lc, r, r') (acc1, acc2, bod_acc) ->
                  -- Keep the old mapping for lc in renv because at the end of a
                  -- branch for indirections we want to return the end-of-input-region
                  -- cursor this function was called with, as opposed to what
                  -- the function call using the indirection pointer returns.
                  if S.member lc indirs
                    then (acc1, acc2, bod_acc)
                    else
                      let locs_in_r = case (M.lookup r region_locs2) of
                            Just locs2_reg -> locs2_reg
                            Nothing ->
                              error $
                                "Did not find key in map (region_locs2): "
                                  ++ show r
                                  ++ "\n\nrenv:\n\n"
                                  ++ show renv
                                  ++ "\n\nrenv1:\n\n"
                                  ++ show renv1
                                  ++ "\n\nrenv2:\n\n"
                                  ++ show renv2
                                  ++ "\n\nregion_locs:\n\n"
                                  ++ show region_locs
                                  ++ "\n\nregion_locs1:\n\n"
                                  ++ show region_locs1
                                  ++ "\n\nregion_locs2:\n\n"
                                  ++ show region_locs2
                                  ++ "\n\n Print argtylocs: "
                                  ++ sdoc argtylocs
                                  ++ "\n\nin_regvars:\n\n"
                                  ++ show in_regvars
                                  ++ "\n\nin_regvars':\n\n"
                                  ++ show in_regvars'
                                  ++ "\n\nPrint fun: "
                                  ++ show f
                                  ++ "\n\nPrint "
                                  ++ show (v, locs, ty, (AppE f applocs args))
                       in case L.elemIndex lc locs_in_r of
                            Just idx ->
                              if idx == (length locs_in_r - 1)
                                then
                                  let fake_last_loc = case lc of
                                        Single locv -> Single $ toVar "fake_" `varAppend` locv
                                        SoA dcloc fieldLocs ->
                                          let dcloc' = toVar "fake_" `varAppend` dcloc
                                              fieldLocs' = L.map (\(k, loc) -> (k, appendNameToLocVar (toVar "fake_") loc)) fieldLocs
                                           in SoA dcloc' fieldLocs'
                                      -- fake_last_loc = toVar "fake_" `varAppend` (unwrapLocVar lc) {- Probably not good to do this -}
                                      acc1' = M.insert fake_last_loc r' acc1
                                      acc2' = M.adjust (\ls -> ls ++ [fake_last_loc]) r acc2
                                      acc2'' = M.insert r' (acc2' # r) acc2'
                                      acc2''' =
                                        foldr
                                          ( \lc2 acc3 -> case (M.lookup lc2 acc1') of
                                              Just rr' -> M.adjust (\ls -> ls ++ [fake_last_loc]) rr' acc3
                                              Nothing -> error "Expected location to be in argtylocs.\n"
                                          )
                                          acc2''
                                          locs_in_r
                                   in dbgTrace (minChatLvl) "Print in updated: " dbgTrace (minChatLvl) (sdoc (acc1')) dbgTrace (minChatLvl) "End in updated!\n" (acc1', acc2''', bod_acc)
                                else
                                  let (_, to_update) = splitAt (idx + 1) locs_in_r
                                      updated = M.mapWithKey (\key val -> if key `elem` to_update then r' else val) acc1
                                      bod_acc' =
                                        foldr
                                          (\l b -> substEndReg (Left l) (toEndVRegVar r') b)
                                          bod_acc
                                          (S.toList (M.keysSet acc1 `S.intersection` (S.fromList to_update)))
                                   in dbgTrace (minChatLvl) "Print in updated: " dbgTrace (minChatLvl) (sdoc (updated, to_update)) dbgTrace (minChatLvl) "End in updated!\n" (updated, acc2, bod_acc')
                            Nothing ->
                              error $
                                "threadRegionsExp: unbound loc "
                                  ++ sdoc (lc, locs_in_r, indirs, region_locs1, r)
                                  ++ "\n\nPrint region of the loc: "
                                  ++ sdoc r
                                  ++ "\n\nPrint the LetE expression: "
                                  ++ sdoc (v, locs, ty, (AppE f applocs args))
                                  ++ "\n\n region_locs2: "
                                  ++ sdoc region_locs2
                                  ++ "\n\n Print argtylocs: "
                                  ++ sdoc argtylocs
                                  ++ "\n\n Print in_regargs: "
                                  ++ sdoc in_regargs
                                  ++ "\n\n Print in_regvars: "
                                  ++ sdoc in_regvars
                                  ++ "\n\n Print in_regvars': "
                                  ++ sdoc in_regvars'
              )
              (renv3, region_locs2, bod1)
              (L.zip3 argtylocs in_regvars in_regvars')
      -- TODO: only keep the rightmost end-of-input-region cursor in renv.
      --------------------
      let !env2' = dbgTrace (minChatLvl) "Print (renv4) in LetE: " dbgTrace (minChatLvl) (sdoc (renv4, (v, locs, ty, (AppE f applocs args)))) dbgTrace (minChatLvl) "End (renv4) LetE.\n" extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc acc -> M.delete loc acc) wlocs_env (NewL2.locsInTy ty)
      bod3 <- threadRegionsExp ddefs fundefs fnLocArgs renv4 env2' lfenv rlocs_env' wlocs_env' pkd_env1 region_locs3 ran_env indirs redirs bod2

      -- shadowstack  ops
      --------------------
      let -- free = S.fromList $ freeLocVars bod
          free = ss_free_locs (S.fromList ((fromVarToFreeVarsTy v) : (map fromLocVarToFreeVarsTy (NewL2.locsInTy ty)) ++ (map (fromLocVarToFreeVarsTy . toLocVar) locs))) env2' bod
          free_wlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy $ M.keysSet wlocs_env')
          free_rlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy $ M.keysSet rlocs_env')
          free_rlocs' =
            let tmp =
                  map (\(x, (MkTy2 (PackedTy _ loc))) -> (Just x, (fromLocVarToFreeVarsTy loc))) $
                    filter
                      (\(_x, _y@(MkTy2 (PackedTy tycon loc))) -> (fromLocVarToFreeVarsTy loc) `S.member` free_rlocs && tycon /= hole_tycon)
                      (M.toList $ M.filter (isPackedTy . unTy2) (vEnv env2))
                tmp2 = map (\x -> (Nothing, x)) $ (S.toList free_rlocs) L.\\ (map snd tmp)
             in S.fromList $ tmp ++ tmp2
      (rpush, wpush, rpop, wpop) <- ss_ops free_rlocs' free_wlocs rlocs_env wlocs_env renv
      emit_ss <- emit_ss_instrs
      if emit_ss && funCanTriggerGC (funMeta (fundefs # f))
        then do
          let binds = rpush ++ wpush ++ [(v, newretlocs, ty, AppE f newapplocs args)] ++ wpop ++ rpop
          (pure $ mkLets binds bod3)
        else pure $ mkLets [(v, newretlocs, ty, AppE f newapplocs args)] bod3
    LetE (v, locs, ty, (SpawnE f applocs args)) bod -> do
      let e' = LetE (v, locs, ty, (AppE f applocs args)) bod
      e'' <- threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs e'
      pure $ changeAppToSpawn f args e''

    -- AUDITME: this causes all all DataConE's to return an additional cursor.
    LetE (v, locs, ty@(MkTy2 (PackedTy _ loc)), rhs@(DataConE _ _ args)) bod -> do
      let reg_of_tag = renv M.! loc
          lfenv' = case args of
            [] -> lfenv
            _ ->
              let last_ty = gRecoverTypeLoc ddefs env2 (last args)
               in case unTy2 last_ty of
                    PackedTy _ last_loc -> do
                      let reg_of_last_arg = renv M.! last_loc
                      if reg_of_tag /= reg_of_last_arg
                        then M.insert loc reg_of_last_arg lfenv
                        else lfenv
                    _ -> lfenv
      let pkd_env1 = M.insert loc (renv # loc) pkd_env
      let env2' = extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc2 acc -> M.delete loc2 acc) wlocs_env (NewL2.locsInTy ty)
      LetE
        <$> (v,locs,ty,)
        <$> go rhs
        <*> threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv' rlocs_env' wlocs_env' pkd_env1 region_locs ran_env indirs redirs bod
    LetE (v, locs, ty@(MkTy2 (PackedTy _ loc)), (Ext (IndirectionE tcon dcon (a, _b) (c, _d) cpy))) bod -> do
      let fn x mode =
            if S.member x indirs || S.member x redirs
              then (EndOfReg_Tagged (fromLocVarToRegVar x))
              else case M.lookup x ran_env of
                Just ran -> (EndOfReg_Tagged (fromVarToSingleRegVar ran {-VS: Might need an SoA ran in the futre??-}))
                Nothing -> case M.lookup x renv of
                  Just r -> (NewL2.EndOfReg r mode (toEndVRegVar r))
                  Nothing -> error $ "threadRegionsExp: unbound loc " ++ sdoc x
      let b' = fn (toLocVar a) Output
      let d' = fn (toLocVar c) Input
      let fn2 (Loc lrem) end = Loc (lrem {lremEndReg = (fromLocVarToRegVar end)})
          fn2 oth _ = error $ "fn2: " ++ sdoc oth
      let a' = fn2 a (toLocVar b')
          c' = fn2 c (toLocVar d')
      let pkd_env' = M.insert loc (renv # loc) pkd_env
      let env2' = extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc2 acc -> M.delete loc2 acc) wlocs_env (NewL2.locsInTy ty)
      bod' <- threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv rlocs_env' wlocs_env' pkd_env' region_locs ran_env indirs redirs bod
      let boundscheck =
            let locarg = a'
                regarg = b'
                -- bc = boundsCheck ddefs tcon
                bc = 18
             in LetE ("_", [], MkTy2 IntTy, Ext $ BoundsCheck bc regarg locarg)
      pure $ boundscheck $ LetE (v, locs, ty, (Ext (IndirectionE tcon dcon (a', b') (c', d') cpy))) bod'
    Ext (StartOfPkdCursor cur) -> do
      let (PackedTy _ loc) = unTy2 (lookupVEnvLocVar (fromVarToFreeVarsTy cur) env2)
      case M.lookup loc pkd_env of
        {-Unsafe : unwrapLocVar loc, semantics for L3 need to change-}
        Just reg -> do
          {-Undafe, what if this is an SoA region? Terrible hack-}
          let reg' = case reg of
                SingleR v -> v
                SoARv _ _ -> error "threadRegionsExp: (StartOfPkdCursor) SoARv not implemented yet."
          -- TagCursor's type is TagCuror Var Var
          -- This is too narrow to represent a SoA region at the moment.
          -- I also don't think this is used in the L2 IR atm.
          -- I but in case it is, then its type needs to be changed.
          dbgTrace (minChatLvl) "Print TagCursor: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End TagCursor\n" return $ Ext $ TagCursor (unwrapLocVar loc) (toEndV reg')
        Nothing -> error $ "threadRegionsExp: unbound " ++ sdoc (loc, pkd_env)

    -- Sometimes, this expression can have RetE forms. We should collect and update
    -- the locs here appropriately.
    LetE (v, locs, ty, rhs@(TimeIt {})) bod -> do
      rhs' <- go rhs
      let retlocs = findRetLocs rhs'
          newretlocs = retlocs ++ locs
      let env2' = extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2
          rlocs_env' = updRLocsEnv (unTy2 ty) rlocs_env
          wlocs_env' = foldr (\loc acc -> M.delete loc acc) wlocs_env (NewL2.locsInTy ty)
      bod1 <- threadRegionsExp ddefs fundefs fnLocArgs renv env2' lfenv rlocs_env' wlocs_env' pkd_env region_locs ran_env indirs redirs bod

      -- shadowstack  ops
      --------------------
      let -- free = S.fromList $ freeLocVars bod
          free = ss_free_locs (S.fromList ((fromVarToFreeVarsTy v) : (map fromLocVarToFreeVarsTy (NewL2.locsInTy ty)) ++ (map (fromLocVarToFreeVarsTy . toLocVar) locs))) env2' bod
          free_wlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy (M.keysSet wlocs_env'))
          free_rlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy (M.keysSet rlocs_env'))
          free_rlocs' =
            let tmp =
                  map (\(x, (MkTy2 (PackedTy _ loc))) -> (Just x, (fromLocVarToFreeVarsTy loc))) $
                    filter
                      (\(_x, _y@(MkTy2 (PackedTy tycon loc))) -> (fromLocVarToFreeVarsTy loc) `S.member` free_rlocs && tycon /= hole_tycon)
                      (M.toList $ M.filter (isPackedTy . unTy2) (vEnv env2))
                tmp2 = map (\x -> (Nothing, x)) $ (S.toList free_rlocs) L.\\ (map snd tmp)
             in S.fromList $ tmp ++ tmp2
      (rpush, wpush, rpop, wpop) <- ss_ops free_rlocs' free_wlocs rlocs_env wlocs_env renv
      emit_ss <- emit_ss_instrs
      if emit_ss
        then do
          let binds = rpush ++ wpush ++ [(v, newretlocs, ty, rhs')] ++ wpop ++ rpop
          (pure $ mkLets binds bod1)
        else pure $ mkLets [(v, newretlocs, ty, rhs')] bod1
    LetE (v, locs, ty, rhs@(Ext (AllocateTagHere x x_tycon))) bod -> do
      let -- x_tycon = (wlocs_env # x)
          rlocs_env' = M.insert x x_tycon rlocs_env
          wlocs_env' = M.delete x wlocs_env
      (LetE (v, locs, ty, rhs))
        <$> threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) lfenv rlocs_env' wlocs_env' pkd_env region_locs ran_env indirs redirs bod
    LetE (v, locs, ty, rhs) bod ->
      LetE
        <$> (v,locs,ty,)
        <$> go rhs
        <*> threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs bod
    WithArenaE v e ->
      WithArenaE v <$> threadRegionsExp ddefs fundefs fnLocArgs renv (extendVEnvLocVar (fromVarToFreeVarsTy v) (MkTy2 ArenaTy) env2) lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs e
    Ext ext ->
      case ext of
        AddFixed {} -> return ex
        LetLocE loc FreeLE bod ->
          Ext
            <$> LetLocE loc FreeLE
            <$> threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs bod
        -- Update renv with a binding for loc
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                StartOfRegionLE r -> regionToVar r
                InRegionLE r -> regionToVar r
                AfterConstantLE _ lc -> renv # (toLocVar lc)
                AfterVariableLE _ lc _ -> renv # (toLocVar lc)
                FromEndLE lc -> renv # (toLocVar lc)
                -- TODO (VS) : Handle SoA loc exp cases
                GetDataConLocSoA lc ->
                  let soa_reg = renv # (toLocVar lc)
                      dcon_reg = case soa_reg of
                        SoARv dreg _ -> dreg
                   in dcon_reg
                GetFieldLocSoA (dcon, idx) lc ->
                  let soa_reg = renv # (toLocVar lc)
                      field_reg = case soa_reg of
                        SoARv _ fregs -> case L.lookup (dcon, idx) fregs of
                          Just freg -> freg
                          Nothing -> error "threadRegionsExp: GetFieldLocSoA: data constructor not found!"
                   in field_reg
                GenSoALoc dlc flcs ->
                  let dlcr = renv # (toLocVar dlc)
                      fieldRegs =
                        map
                          ( \(d, flc) ->
                              let flcr = renv # (toLocVar flc)
                               in (d, flcr)
                          )
                          flcs
                   in SoARv dlcr fieldRegs
                _ -> error "threadRegionsExp: todo"
              region_locs1 = case rhs of
                AfterConstantLE {} -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                AfterVariableLE {} -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                StartOfRegionLE {} -> M.insert reg [loc] region_locs
                GenSoALoc {} -> case (M.member reg region_locs) of
                  True -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                  False -> M.insert reg [loc] region_locs
                FromEndLE {} -> case (M.member reg region_locs) of
                  True -> M.adjust (\locs -> locs ++ [loc]) reg region_locs
                  False -> M.insert reg [loc] region_locs
                _ -> region_locs
              wlocs_env' = dbgTrace (minChatLvl) "Print renv LetLocE: " dbgTrace (minChatLvl) (sdoc (loc, reg, renv, region_locs, region_locs1)) dbgTrace (minChatLvl) "End renv LetLocE.\n" M.insert loc hole_tycon wlocs_env
          Ext
            <$> LetLocE loc rhs
            <$> threadRegionsExp ddefs fundefs fnLocArgs (M.insert loc reg renv) env2 lfenv rlocs_env wlocs_env' pkd_env region_locs1 ran_env indirs redirs bod
        RetE locs v -> do
          let ty = lookupVEnvLocVar (fromVarToFreeVarsTy v) env2
              fn m = (\r -> NewL2.EndOfReg r m (toEndVRegVar r))
              outtylocs = NewL2.locsInTy ty
              outtyregvars =
                foldr
                  ( \loc acc -> case M.lookup loc lfenv of
                      Nothing -> (renv # loc) : acc
                      Just r -> r : acc
                  )
                  []
                  outtylocs
              outtyregargs = map (fn Output) outtyregvars
              inregvars =
                map
                  ( \lrm ->
                      let r = renv # (lremLoc lrm)
                          last_loc = last (region_locs # r)
                          r' = (renv # last_loc)
                       in r'
                  )
                  $ filter (\lrm -> lremMode lrm == Input) fnLocArgs
              inregargs = map (fn Input) inregvars
              newlocs = dbgTrace (minChatLvl) "Print in RetE: " dbgTrace (minChatLvl) (sdoc (fnLocArgs, renv, region_locs, inregargs)) dbgTrace (minChatLvl) "End in RetE.\n" inregargs ++ outtyregargs
          return $ Ext $ RetE (newlocs ++ locs) v
        TagCursor a b -> return $ Ext $ TagCursor a b
        LetRegionE r sz ty bod -> do
          -- shadowstack  ops
          --------------------
          let -- free = S.fromList $ freeLocVars bod
              free = ss_free_locs (S.singleton (fromRegVarToFreeVarsTy $ regionToVar r)) env2 bod
              free_wlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy (M.keysSet wlocs_env))
              free_rlocs = free `S.intersection` (S.map fromLocVarToFreeVarsTy (M.keysSet rlocs_env))
              free_rlocs' =
                let tmp =
                      map (\(x, (MkTy2 (PackedTy _ loc))) -> (Just x, (fromLocVarToFreeVarsTy loc))) $
                        filter
                          (\(_x, _y@(MkTy2 (PackedTy tycon loc))) -> (fromLocVarToFreeVarsTy loc) `S.member` free_rlocs && tycon /= hole_tycon)
                          (M.toList $ M.filter (isPackedTy . unTy2) (vEnv env2))
                    tmp2 = map (\x -> (Nothing, x)) $ (S.toList free_rlocs) L.\\ (map snd tmp)
                 in S.fromList $ tmp ++ tmp2
          (rpush, wpush, rpop, wpop) <- ss_ops free_rlocs' free_wlocs rlocs_env wlocs_env renv
          emit_ss <- emit_ss_instrs
          bod' <- go bod
          if emit_ss
            then do
              let pre = mkLets (rpush ++ wpush)
                  post = mkLets (wpop ++ rpop) bod'
              pure $ pre (Ext $ LetRegionE r sz ty post)
            else pure $ Ext $ LetRegionE r sz ty bod'
        LetParRegionE r sz ty bod -> Ext <$> LetParRegionE r sz ty <$> go bod
        FromEndE {} -> return ex
        BoundsCheck sz _bound cur -> do
          let reg = toEndVRegVar (renv # (toLocVar cur))
          return $ Ext $ BoundsCheck sz (NewL2.EndOfReg reg Output (toEndVRegVar reg)) cur
        IndirectionE {} -> return ex
        GetCilkWorkerNum -> return ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
        AllocateTagHere {} -> pure ex
        AllocateScalarsHere {} -> pure ex
        SSPush {} -> pure ex
        SSPop {} -> pure ex
    -- Straightforward recursion

    VarE {} -> return ex
    LitE {} -> return ex
    CharE {} -> return ex
    FloatE {} -> return ex
    LitSymE {} -> return ex
    PrimAppE {} -> return ex
    DataConE {} -> return ex
    ProjE i e -> ProjE i <$> go e
    IfE a b c -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    CaseE scrt mp -> do
      let (VarE v) = scrt
          PackedTy _ tyloc = unTy2 (lookupVEnvLocVar (fromVarToFreeVarsTy v) env2)
          reg = dbgTrace (minChatLvl) "Print in CaseE: " dbgTrace (minChatLvl) (sdoc (region_locs)) dbgTrace (minChatLvl) "End in CaseE.\n" renv M.! tyloc
      -- region_locs' = case reg of
      --                     SingleR _ -> region_locs
      --                     SoARv _ fregs -> let locs_case = (concatMap (\(a, b, c) -> map snd b) mp)
      --                                          acc' = foldr (\(loc, idx) acc -> case (M.lookup (dcon, idx) fregs) of
      --                                                                                           Nothing -> acc
      --                                                                                           Just reg' -> M.adjust (\locs -> locs ++ [loc]) reg' acc
      --                                                               ) region_locs zip $ (concatMap (\(a, b, c) -> map snd b) mp) [0..(length locs_case)]
      --                                        in acc'
      mp' <-
        mapM
          ( \tup@(dcon, b, c) -> do
              let locs_case = dbgTrace (minChatLvl) "Print ty of Scrut: " dbgTrace (minChatLvl) (sdoc (reg)) dbgTrace (minChatLvl) "End scrut ty.\n" map (toLocVar . snd) b
              let region_locs' = case reg of
                    SingleR _ -> region_locs
                    SoARv _ fregs ->
                      let acc' =
                            foldr
                              ( \(loc, idx) acc -> case (L.lookup (dcon, idx) fregs) of
                                  Nothing -> acc
                                  Just reg' -> M.adjust (\locs -> locs ++ [loc]) reg' acc
                              )
                              region_locs
                              (zip locs_case [0 .. (length locs_case)])
                       in acc'
              tup' <- dbgTrace (minChatLvl) "Print in CaseE after: " dbgTrace (minChatLvl) (sdoc (region_locs, region_locs')) dbgTrace (minChatLvl) "End in CaseE after.\n" docase reg renv env2 lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs tup
              pure tup'
          )
          mp
      let !new_expr = CaseE scrt mp'
      pure $ new_expr
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE {} -> error "threadRegionsExp: Unbound SpawnE"
    SyncE -> pure ex
    MapE {} -> error $ "threadRegionsExp: TODO MapE"
    FoldE {} -> error $ "threadRegionsExp: TODO FoldE"
  where
    emit_ss_instrs =
      do
        dflags <- getDynFlags
        pure $ gopt Opt_GenGc dflags && not (gopt Opt_DisableGC dflags)

    go = threadRegionsExp ddefs fundefs fnLocArgs renv env2 lfenv rlocs_env wlocs_env pkd_env region_locs ran_env indirs redirs

    docase reg renv1 env21 lfenv1 rlocs_env1 wlocs_env1 pkd_env1 region_locs1 ran_env1 indirs1 redirs1 (dcon, vlocargs, bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars, locargs) = unzip vlocargs
          dcon_tys = lookupDataCon ddefs dcon
          locs = map toLocVar locargs
          renv0 =
            if isIndirectionTag dcon || isRedirectionTag dcon
              then
                foldr
                  ( \(lc, idx) acc -> case reg of
                      SingleR _ -> M.insert (singleLocVar lc) reg acc
                      SoARv _ fregs -> case (L.lookup (dcon, idx) fregs) of
                        Just reg' -> M.insert (singleLocVar lc) reg' acc
                        Nothing -> M.insert (singleLocVar lc) reg acc
                  )
                  renv1
                  (zip vars [0 .. (length vars)])
              else renv1
          -- renv0  = if isIndirectionTag dcon || isRedirectionTag dcon
          --          then foldr (\lc acc -> M.insert (singleLocVar lc) reg acc) renv1 vars
          --          else renv1
          renv1' = foldr (\lc acc -> M.insert lc reg acc) renv0 locs
          renv1'' =
            foldr
              ( \(lc, idx) acc -> case reg of
                  SingleR _ -> M.insert lc reg acc
                  SoARv _ fregs -> case (L.lookup (dcon, idx) fregs) of
                    Just reg' -> M.insert lc reg' acc
                    Nothing -> M.insert lc reg acc
              )
              renv1'
              (zip locs [0 .. (length locs)])
          env21' = NewL2.extendPatternMatchEnvLocVar dcon ddefs vars locs env21
          rlocs_env1' =
            foldr
              ( \(loc, ty) acc ->
                  case unTy2 ty of
                    PackedTy tycon _ -> M.insert loc tycon acc
                    _ -> acc
              )
              rlocs_env1
              (fragileZip locs dcon_tys)
          pkd_env1' =
            foldr
              ( \(loc, ty) acc ->
                  case unTy2 ty of
                    PackedTy {} -> M.insert loc reg acc
                    _ -> acc
              )
              pkd_env1
              (fragileZip locs dcon_tys)
          indirs1' =
            if isIndirectionTag dcon
              then S.insert (singleLocVar $ Sf.headErr vars) indirs1
              else indirs1
          redirs1' =
            if isRedirectionTag dcon
              then S.insert (singleLocVar $ Sf.headErr vars) redirs1
              else redirs1
          region_locs1' =
            if isIndirectionTag dcon || isRedirectionTag dcon
              then M.adjust (\val -> val ++ (L.map singleLocVar (take 1 vars))) reg region_locs1
              else case reg of
                SingleR _ -> M.adjust (\val -> val ++ locs) reg region_locs1
                SoARv _ fregs ->
                  let acc' =
                        foldr
                          ( \(loc, idx) acc -> case L.lookup (dcon, idx) fregs of
                              Nothing -> M.adjust (\val -> val ++ [loc]) reg acc
                              Just reg' -> M.adjust (\val -> val ++ [loc]) reg' acc
                          )
                          region_locs1
                          (zip locs [0 .. length (locs)])
                   in acc'
          num_cursor_tys = dbgTrace (minChatLvl) "print in doCase (renv0): " dbgTrace (minChatLvl) (sdoc (renv1'', renv0, region_locs1')) dbgTrace (minChatLvl) "End doCase (renv0).\n" length $ filter ((== CursorTy) . unTy2) dcon_tys
          ran_env1' =
            ran_env1
              `M.union` ( if isIndirectionTag dcon || isRedirectionTag dcon
                            then M.empty
                            else
                              M.fromList $
                                zip
                                  (reverse $ take num_cursor_tys $ reverse locs)
                                  (take num_cursor_tys vars)
                        )
      (dcon,vlocargs,)
        <$> (threadRegionsExp ddefs fundefs fnLocArgs renv1'' env21' lfenv1 rlocs_env1' wlocs_env1 pkd_env1' region_locs1' ran_env1' indirs1' redirs1' bod)

    ss_free_locs :: S.Set FreeVarsTy -> Env2 FreeVarsTy NewL2.Ty2 -> NewL2.Exp2 -> S.Set FreeVarsTy
    ss_free_locs bound env20 ex0 =
      let mapfunc =
            S.map
              ( \w -> case M.lookup w (vEnv env20) of
                  -- assumption: it's a location
                  Nothing -> w
                  Just (MkTy2 (PackedTy _ loc)) -> fromLocVarToFreeVarsTy loc
                  Just wty -> error $ "threadRegionsExp: unexpected type " ++ show (w, wty)
              )
          freeVars = allFreeVars_sans_datacon_args ex0
          keysSet1 = M.keysSet (M.filter (not . isPackedTy . unTy2) (vEnv env20))
          keysSet2 = M.keysSet (fEnv env20)
          -- keysSet1' = S.map singleLocVar keysSet1
          -- keysSet2' = S.map singleLocVar keysSet2
          -- bound' = bound {-terrible hack !!-}
          -- freeVars' = S.fromList $ L.concatMap (\fv -> case fv of
          --                                    FL l -> case l of
          --                                               _ -> [l]
          --                                               -- Single lv -> [lv]
          --                                               -- _ -> error "threadRegionsExp: unexpected location type"
          --                                    V v -> [singleLocVar v]
          --                                    _ -> []) (S.toList freeVars)
          -- allLocs = (freeVars' `S.difference` (bound' `S.union`
          --            keysSet1'  `S.union` keysSet2'))
          allLocs =
            ( freeVars
                `S.difference` ( bound
                                   `S.union` keysSet1
                                   `S.union` keysSet2
                               )
            )
       in mapfunc allLocs

    updRLocsEnv t acc =
      case t of
        PackedTy tycon loc -> M.insert loc tycon acc
        ProdTy tys -> foldr updRLocsEnv acc tys
        _ -> acc

hole_tycon :: String
hole_tycon = "HOLE"

ss_ops ::
  S.Set (Maybe FreeVarsTy, FreeVarsTy) ->
  S.Set FreeVarsTy ->
  AllocEnv ->
  AllocEnv ->
  RegEnv ->
  PassM
    ( [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)],
      [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)],
      [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)],
      [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)]
    )
ss_ops free_rlocs free_wlocs rlocs_env wlocs_env renv = do
  rpush <-
    ( foldrM
        ( \(mb_x, loc) acc -> do
            push <- gensym "ss_push"
            let locv = case loc of
                  FL l -> l
                  _ -> error "threadRegionsExp: ss_ops: did not expect anything other than a location!"
            let tycon = rlocs_env # locv
            if tycon == hole_tycon
              then pure acc
              else case mb_x of
                Nothing -> pure ((push, [], MkTy2 (ProdTy []), Ext $ SSPush Read locv (fromRegVarToLocVar $ toEndVRegVar (renv # locv)) tycon) : acc)
                Just fv -> case fv of
                  V x -> pure ((push, [], MkTy2 (ProdTy []), Ext $ SSPush Read (singleLocVar x) (fromRegVarToLocVar $ toEndVRegVar (renv # locv)) tycon) : acc)
                  _ -> error "threadRegionsExp: ss_ops: unexpected case"
        )
        []
        free_rlocs
    ) ::
      PassM [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)]
  wpush <-
    ( foldrM
        ( \x acc -> do
            push <- gensym "ss_push"
            let xloc = case x of
                  FL l -> l
                  _ -> error "threadRegionsExp: ss_ops: did not expect anything other than a location!"
            let tycon = wlocs_env # xloc
            if tycon == hole_tycon
              then pure acc
              else pure ((push, [], MkTy2 (ProdTy []), Ext $ SSPush Write xloc (fromRegVarToLocVar $ toEndVRegVar (renv # xloc)) tycon) : acc)
        )
        []
        free_wlocs
    ) ::
      PassM [(Var, [LocArg], NewL2.Ty2, NewL2.Exp2)]
  let fn = (\(_x, locs, ty, Ext (SSPush a b c _)) -> gensym "ss_pop" >>= \y -> pure (y, locs, ty, Ext (SSPop a b c)))
  rpop <- mapM fn (reverse rpush)
  wpop <- mapM fn (reverse wpush)
  pure (rpush, wpush, rpop, wpop)

-- Inspect an AST and return locations in a RetE form.
findRetLocs :: NewL2.Exp2 -> [LocArg]
findRetLocs e0 = go e0 []
  where
    go :: NewL2.Exp2 -> [LocArg] -> [LocArg]
    go ex acc =
      case ex of
        VarE {} -> acc
        LitE {} -> acc
        CharE {} -> acc
        FloatE {} -> acc
        LitSymE {} -> acc
        AppE _ _ args -> foldr go acc args
        PrimAppE _ args -> foldr go acc args
        LetE (_, _, _, rhs) bod -> do
          foldr go acc [rhs, bod]
        IfE a b c -> foldr go acc [a, b, c]
        MkProdE xs -> foldr go acc xs
        ProjE _ e -> go e acc
        DataConE _ _ args -> foldr go acc args
        CaseE _ mp ->
          foldr (\(_, _, c) acc2 -> go c acc2) acc mp
        TimeIt e _ty _b -> go e acc
        WithArenaE _v e -> go e acc
        SpawnE {} -> acc
        SyncE {} -> acc
        Ext ext ->
          case ext of
            LetRegionE _ _ _ bod -> go bod acc
            LetParRegionE _ _ _ bod -> go bod acc
            LetLocE _ _ bod -> go bod acc
            StartOfPkdCursor {} -> acc
            TagCursor {} -> acc
            RetE locs _ -> locs ++ acc
            FromEndE {} -> acc
            BoundsCheck {} -> acc
            IndirectionE {} -> acc
            AddFixed {} -> acc
            GetCilkWorkerNum -> acc
            LetAvail _ bod -> go bod acc
            AllocateTagHere {} -> acc
            AllocateScalarsHere {} -> acc
            SSPush {} -> acc
            SSPop {} -> acc
        MapE {} -> error "findRetLocs: TODO MapE"
        FoldE {} -> error "findRetLocs: TODO FoldE"

----------------------------------------

-- Maximal sum of sizes of scalars before the first packed thing in the
-- constructors of this type. The assumption is that whatever writes
-- that packed value will do a bounds check again. Note that only AppE's
-- do boundschecking, DataConE's dont. We should fix this.
boundsCheck :: NewL2.DDefs2 -> TyCon -> Int
boundsCheck ddefs tycon =
  let dcons = getConOrdering ddefs tycon
      spaceReqd tys =
        foldl
          ( \(bytes, seen_packed) ty ->
              if seen_packed
                then (bytes, seen_packed)
                else
                  if hasPacked (unTy2 ty)
                    then (bytes, True)
                    else (bytes + (fromJust $ sizeOfTy (unTy2 ty)), False)
          )
          (0, False)
          tys
      tyss = map (lookupDataCon ddefs) dcons
      vals = map (fst . spaceReqd) tyss
      -- Add a byte for the tag.
      num_bytes = (1 + maximum vals)
   in -- Reserve additional space for a redirection node or a forwarding pointer.
      dbgTrace (minChatLvl) "Print boundsCheck: " dbgTrace (minChatLvl) (sdoc (dcons, vals, tyss)) dbgTrace (minChatLvl) "End boundsCheck.\n" num_bytes + 9

-- Not making a seperate function for bounds checking an SoA location at the moment.
-- For a data constructor region -- it is 1 byte
-- For a field region, it is size of field.
-- Do a bounds check for an SoA region / location
-- It should return me an integer value for checking the bounds with each corresponding region
-- One for a data construction region, I think for now its safe to assume that we should use 1 byte for the data constructor region.
-- One for each field region,
-- If it is another packed region, that is the field is a packed region, we can use 0 (following the same assumption as AoS) that the AppE function
-- will do a bounds check.
-- For a scalar, we can use the size of the field.
-- boundsCheckSoA :: NewL2.DDefs2 -> TyCon -> [Int]
-- boundsCheckSoA ddefs tycon =
--   let dcons = getConOrdering ddefs tycon

----------------------------------------

-- gFreeVars ++ locations ++ region variables - (args to datacons)
-- Terrible hack to unwrapLocVar atm, this will likely need to change.
allFreeVars_sans_datacon_args :: NewL2.Exp2 -> S.Set FreeVarsTy
allFreeVars_sans_datacon_args ex =
  case ex of
    AppE _ locs args -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs) `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    PrimAppE _ args -> (S.unions (map allFreeVars_sans_datacon_args args))
    LetE (v, locs, _, rhs) bod ->
      (S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs) `S.union` (allFreeVars_sans_datacon_args rhs) `S.union` (allFreeVars_sans_datacon_args bod))
        `S.difference` S.singleton (fromVarToFreeVarsTy v)
    IfE a b c -> allFreeVars_sans_datacon_args a `S.union` allFreeVars_sans_datacon_args b `S.union` allFreeVars_sans_datacon_args c
    MkProdE args -> (S.unions (map allFreeVars_sans_datacon_args args))
    ProjE _ bod -> allFreeVars_sans_datacon_args bod
    CaseE scrt brs ->
      (allFreeVars_sans_datacon_args scrt)
        `S.union` ( S.unions
                      ( map
                          ( \(_, vlocs, c) ->
                              allFreeVars_sans_datacon_args c
                                `S.difference` S.fromList (map (fromVarToFreeVarsTy . fst) vlocs)
                                `S.difference` S.fromList (map (fromLocVarToFreeVarsTy . toLocVar . snd) vlocs)
                          )
                          brs
                      )
                  )
    DataConE loc _ _args -> S.singleton ((fromLocVarToFreeVarsTy . toLocVar) loc)
    TimeIt e _ _ -> allFreeVars_sans_datacon_args e
    WithArenaE _ e -> allFreeVars_sans_datacon_args e
    SpawnE _ locs args -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs) `S.union` (S.unions (map allFreeVars_sans_datacon_args args))
    Ext ext ->
      case ext of
        LetRegionE r _sz _ty bod -> S.delete (fromRegVarToFreeVarsTy $ regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetParRegionE r _sz _ty bod -> S.delete (fromRegVarToFreeVarsTy $ regionToVar r) (allFreeVars_sans_datacon_args bod)
        LetLocE loc locexp bod -> S.delete (fromLocVarToFreeVarsTy loc) (allFreeVars_sans_datacon_args bod `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars locexp))
        StartOfPkdCursor cur -> S.singleton (fromVarToFreeVarsTy cur)
        TagCursor a b -> S.fromList [fromVarToFreeVarsTy a, fromVarToFreeVarsTy b]
        RetE locs v -> S.insert (fromVarToFreeVarsTy v) (S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs))
        FromEndE loc -> S.singleton ((fromLocVarToFreeVarsTy . toLocVar) loc)
        BoundsCheck _ reg cur -> S.fromList [(fromLocVarToFreeVarsTy . toLocVar) reg, (fromLocVarToFreeVarsTy . toLocVar) cur]
        IndirectionE _ _ (a, b) (c, d) _ -> S.fromList $ [(fromLocVarToFreeVarsTy . toLocVar) a, (fromLocVarToFreeVarsTy . toLocVar) b, (fromLocVarToFreeVarsTy . toLocVar) c, (fromLocVarToFreeVarsTy . toLocVar) d]
        AddFixed v _ -> S.singleton (fromVarToFreeVarsTy v)
        GetCilkWorkerNum -> S.empty
        LetAvail vs bod -> S.fromList (map fromVarToFreeVarsTy vs) `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars bod)
        AllocateTagHere loc _ -> S.singleton (fromLocVarToFreeVarsTy loc)
        AllocateScalarsHere loc -> S.singleton (fromLocVarToFreeVarsTy loc)
        SSPush _ a b _ -> S.fromList [(fromLocVarToFreeVarsTy a), (fromLocVarToFreeVarsTy b)]
        SSPop _ a b -> S.fromList [(fromLocVarToFreeVarsTy a), (fromLocVarToFreeVarsTy b)]
    _ -> S.map fromVarToFreeVarsTy $ gFreeVars ex

----------------------------------------

substEndReg :: Either LocVar RegVar -> RegVar -> NewL2.Exp2 -> NewL2.Exp2
substEndReg loc_or_reg end_reg ex =
  case ex of
    AppE f locs args -> AppE f (map gosubst locs) (map go args)
    PrimAppE pr args -> PrimAppE pr (map go args)
    LetE (v, locs, ty, rhs) bod -> LetE (v, map gosubst locs, ty, go rhs) (go bod)
    IfE a b c -> IfE (go a) (go b) (go c)
    MkProdE args -> MkProdE (map go args)
    ProjE i bod -> ProjE i (go bod)
    CaseE scrt brs -> CaseE (go scrt) (map (\(dcon, vlocs, c) -> (dcon, vlocs, go c)) brs)
    DataConE loc dcon args -> DataConE (gosubst loc) dcon (map go args)
    TimeIt e ty b -> TimeIt (go e) ty b
    WithArenaE v e -> WithArenaE v (go e)
    SpawnE f locs args -> SpawnE f (map gosubst locs) (map go args)
    Ext ext ->
      case ext of
        LetRegionE r sz ty bod -> Ext $ LetRegionE r sz ty (go bod)
        LetParRegionE r sz ty bod -> Ext $ LetParRegionE r sz ty (go bod)
        LetLocE loc locexp bod -> Ext $ LetLocE loc locexp (go bod)
        RetE locs v -> Ext $ RetE (map gosubst locs) v
        FromEndE loc -> Ext $ FromEndE (gosubst loc)
        BoundsCheck i reg cur -> Ext $ BoundsCheck i (gosubst reg) (gosubst cur)
        IndirectionE tycon dcon (a, b) (c, d) e ->
          Ext $ IndirectionE tycon dcon (gosubst a, gosubst b) (gosubst c, gosubst d) e
        LetAvail vs bod -> Ext $ LetAvail vs (go bod)
        StartOfPkdCursor {} -> ex
        TagCursor {} -> ex
        AddFixed {} -> ex
        GetCilkWorkerNum -> ex
        AllocateTagHere {} -> ex
        AllocateScalarsHere {} -> ex
        SSPush {} -> ex
        SSPop {} -> ex
    _ -> ex
  where
    go = substEndReg loc_or_reg end_reg
    gosubst = substEndReg_locarg loc_or_reg end_reg

substEndReg_locarg :: Either LocVar RegVar -> RegVar -> LocArg -> LocArg
substEndReg_locarg loc_or_reg end_reg locarg =
  case locarg of
    Loc lrem -> case loc_or_reg of
      Left loc0 ->
        if lremLoc lrem == loc0
          then Loc (lrem {lremEndReg = end_reg})
          else locarg
      Right reg0 ->
        if lremReg lrem == reg0
          then Loc (lrem {lremEndReg = end_reg})
          else locarg
    EndWitness lrem v -> case loc_or_reg of
      Left loc0 ->
        if lremLoc lrem == loc0
          then EndWitness (lrem {lremEndReg = end_reg}) v
          else locarg
      Right reg0 ->
        if lremReg lrem == reg0
          then EndWitness (lrem {lremEndReg = end_reg}) v
          else locarg
    Reg {} -> locarg
    EndOfReg {} -> locarg
    EndOfReg_Tagged {} -> locarg
