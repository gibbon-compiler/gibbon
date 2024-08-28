module Gibbon.Passes.MarkTailCalls (markTailCalls) where

import Data.Foldable (foldrM)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe (fromJust)
import qualified Data.Set as S
import Prelude as P

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L2.Syntax as Old
import Gibbon.NewL2.Syntax as NewL2

-- ^ A map that tracks location variables that need to be mutable.

type TrackLocVariables = M.Map LocVar (S.Set LocVar, Bool)

markTailCalls :: NewL2.Prog2 -> PassM NewL2.Prog2
markTailCalls Prog{ddefs, fundefs, mainExp} = do
    fds' <- mapM (markTailCallsFn ddefs) $ M.elems fundefs
    let newFundefs = M.fromList $ map (\f -> (funName f, f)) fds'
    let newProg = Prog{ddefs = ddefs, fundefs = newFundefs, mainExp = mainExp}
    pure $ newProg {- dbgTraceIt (sdoc newProg) dbgTraceIt (sdoc $ M.elems fundefs')-}

markTailCallsFn :: NewL2.DDefs2 -> NewL2.FunDef2 -> PassM NewL2.FunDef2
markTailCallsFn ddefs f@FunDef{funName, funArgs, funTy, funMeta, funBody} = do
    let (funBody', env) = markTailCallsFnBody funName M.empty funBody
        (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = dbgTraceIt "Print env at the end." dbgTraceIt (sdoc (env, M.elems env)) dbgTraceIt "End\n" funTy
        locVars' =
            P.map
                ( \(LRM l r m) -> case (backTrackLocs env l False M.empty) of
                    (False, _) -> LRM l r m
                    (True, _) -> LRM l r OutputMutable
                )
                locVars
        funTy' = (ArrowTy2 locVars' arrIns _arrEffs arrOut _locRets _isPar)
        funBody'' = markMutableLocsAfterInitialPass env funBody'
    --funBody''' <- copyOutputMutableBeforeCallsAndReplace funBody''
    return $ FunDef funName funArgs funTy' funBody'' funMeta

--  if tailCallTy == TMC
--  then
--     let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = funTy
--         locVars' = P.map (\(LRM l r m) -> if m == Output
--                                           then LRM l r OutputMutable
--                                           else LRM l r m
--                          ) locVars
--         funTy' = (ArrowTy2 locVars' arrIns _arrEffs arrOut _locRets _isPar)
--       in return $ FunDef funName funArgs funTy' funBody' funMeta  {-dbgTraceIt (sdoc (tailCallTy, funName, funTy')) dbgTraceIt "a" dbgTraceIt (sdoc (tailCallTy, funName, funTy')) dbgTraceIt "a"  -}
--  else if tailCallTy == TC
--  then
--     let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = funTy
--         funTy' = (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar)
--       in return $ FunDef funName funArgs funTy' funBody' funMeta {-dbgTraceIt (sdoc (tailCallTy, funName, funTy')) dbgTraceIt "b" dbgTraceIt (sdoc (tailCallTy, funName, funTy')) dbgTraceIt "b"  -}
--  else pure f {-dbgTraceIt (sdoc (tailCallTy, funName, funTy)) dbgTraceIt "c" dbgTraceIt (sdoc (tailCallTy, funName, funTy)) dbgTraceIt "c"-}
--  --dbgTraceIt (sdoc tailCallTy) pure f
-- pure f

backTrackLocs :: TrackLocVariables -> LocVar -> Bool -> M.Map LocVar Bool -> (Bool, M.Map LocVar Bool)
backTrackLocs env v accum visited = case M.lookup v env of
    Nothing ->
        let visited' = M.insert v True visited
         in (accum, visited')
    Just (s, mut) ->
        let locsToLook = S.toList s
            results =
                P.map
                    ( \l ->
                        let (a', v') = backTrackLocs env l accum visited
                         in (a', v')
                    )
                    locsToLook
            accum' = P.foldr (\b a -> b || a) accum $ P.map fst results
            visited' = M.unions $ P.map snd results
            visited'' = M.insert v True visited
            accum'' = accum' || mut
         in (accum'', visited'')

markTailCallsFnBody :: Var -> TrackLocVariables -> NewL2.Exp2 -> (NewL2.Exp2, TrackLocVariables, TailRecType)
markTailCallsFnBody funName env exp2 = case exp2 of
    VarE v -> (VarE v, env)
    LitE l -> (LitE l, env)
    CharE c -> (CharE c, env)
    FloatE f -> (FloatE f, env)
    LitSymE v -> (LitSymE v, env)
    AppE (v, t) locs args ->
        let results = P.map (markTailCallsFnBody funName env) args
            args' = P.map fst results
            env' = M.unionsWith unionMapLambda $ P.map snd results
         in (AppE (v, t) locs args', env')
    PrimAppE p args ->
        let results = P.map (markTailCallsFnBody funName env) args
            args' = P.map fst results
            env' = M.unionsWith unionMapLambda $ P.map snd results
         in (PrimAppE p args', env')
    LetE (v, loc, ty, rhs) bod -> case rhs of
        AppE (v', _) locs' args' ->
            if v' == funName
                then
                    let tailCallType = markTailCallsFnBodyHelper 0 bod
                        env' = case tailCallType of
                            NoTail -> env
                            TC -> env
                            TMC ->
                                P.foldr
                                    ( \loc e -> case M.lookup (toLocVar loc) e of
                                        Nothing -> case loc of
                                            Loc (LREM l' r' e' m') -> case m' of
                                                Output -> M.insert (toLocVar loc) (S.empty, True) e
                                                OutputMutable -> M.insert (toLocVar loc) (S.empty, True) e
                                                _ -> e
                                            _ -> e
                                        Just (s, m) -> case loc of
                                            Loc (LREM l' r' e' m') -> case m' of
                                                Output -> M.insert (toLocVar loc) (s, True) e
                                                OutputMutable -> M.insert (toLocVar loc) (s, True) e
                                                _ -> e
                                            _ -> e
                                    )
                                    env
                                    locs'
                        rhs' = AppE (v', tailCallType) locs' args'
                        (rhs'', env'') = markTailCallsFnBody funName env' rhs'
                        (bod', env''') = markTailCallsFnBody funName env'' bod
                     in (LetE (v, loc, ty, rhs'') bod', env''', tailCallType)
                else
                    let (rhs', env') = markTailCallsFnBody funName env rhs
                        (bod', env'') = markTailCallsFnBody funName env' bod
                     in (LetE (v, loc, ty, rhs') bod', env'', tailCallType)
        _ ->
            let (rhs', env', tailTy) = markTailCallsFnBody funName env rhs
                (bod', env'', tailTy) = markTailCallsFnBody funName env' bod
             in (LetE (v, loc, ty, rhs') bod', env'')
    IfE a b c ->
        let (a', e1) = markTailCallsFnBody funName env a
            (b', e2) = markTailCallsFnBody funName e1 b
            (c', e3) = markTailCallsFnBody funName e2 c
         in (IfE a' b' c', e3)
    MkProdE ls ->
        let results = P.map (markTailCallsFnBody funName env) ls
            ls' = P.map fst results
            env' = M.unionsWith unionMapLambda $ P.map snd results
         in (MkProdE ls', env')
    ProjE i e ->
        let (e', env') = markTailCallsFnBody funName env e
         in (ProjE i e', env')
    -- [(DataCon, [(Var,loc)], EXP)]
    CaseE scrt brs ->
        let results =
                P.map
                    ( \(a, b, c) ->
                        let (c', env') = markTailCallsFnBody funName env c
                         in ((a, b, c'), env')
                    )
                    brs
            brs' = P.map fst results
            env'' = M.unionsWith unionMapLambda $ P.map snd results
         in (CaseE scrt brs', env'')
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    DataConE loc c args ->
        let locInDataCon = dbgTraceIt "In DataCon:" dbgTraceIt (sdoc (env, M.elems env)) dbgTraceIt ("End\n") toLocVar loc
         in case (backTrackLocs env locInDataCon False M.empty) of
                (False, _) ->
                    let results = P.map (markTailCallsFnBody funName env) args
                        args' = P.map fst results
                        env' = M.unionsWith unionMapLambda $ P.map snd results
                     in (DataConE loc c args', env')
                (True, _) ->
                    let loc' = case loc of
                            NewL2.Loc lrem -> NewL2.Loc lrem{lremMode = OutputMutable}
                            _ -> loc
                        results = P.map (markTailCallsFnBody funName env) args
                        args' = P.map fst results
                        env' = M.unionsWith unionMapLambda $ P.map snd results
                     in (DataConE loc' c args', env')
    TimeIt e d b ->
        let (e', env') = markTailCallsFnBody funName env e
         in (TimeIt e' d b, env')
    MapE d e ->
        let (e', env') = markTailCallsFnBody funName env e
         in (MapE d e', env')
    FoldE i it e ->
        let (e', env') = markTailCallsFnBody funName env e
         in (FoldE i it e', env')
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    SpawnE v locs exps ->
        let results = P.map (markTailCallsFnBody funName env) exps
            exps' = P.map fst results
            env' = M.unionsWith unionMapLambda $ P.map snd results
         in (SpawnE v locs exps', env')
    SyncE -> (exp2, env)
    WithArenaE _v e ->
        let (e', env') = markTailCallsFnBody funName env e
         in (WithArenaE _v e', env')
    Ext ext ->
        case ext of
            Old.LetRegionE r a b bod ->
                let (bod', env') = markTailCallsFnBody funName env bod
                 in (Ext $ Old.LetRegionE r a b bod', env')
            Old.LetParRegionE r a b bod ->
                let (bod', env') = markTailCallsFnBody funName env bod
                 in (Ext $ Old.LetParRegionE r a b bod', env')
            Old.LetLocE loc locexp bod ->
                let locInExp = freeLoc locexp
                    env' = case locInExp of
                        Nothing -> env
                        Just l -> M.insert l (S.singleton (toLocVar loc), False) env
                    (bod', env'') = markTailCallsFnBody funName env' bod
                    locexp' = case locInExp of
                        Nothing -> locexp
                        Just l -> case (backTrackLocs env'' l False M.empty) of
                            (False, _) -> locexp
                            (True, _) -> changeLocData locexp l
                 in (Ext $ Old.LetLocE loc locexp' bod', env'')
            _ -> (Ext ext, env)
  where
    -- Old.StartOfPkdCursor v -> [NoTail]
    -- Old.TagCursor a b -> [NoTail]
    -- Old.RetE locs v -> [NoTail]
    -- Old.FromEndE loc -> [NoTail]
    -- Old.BoundsCheck _ reg cur -> [NoTail]
    -- Old.IndirectionE _ _ (a,b) (c,d) _ -> [NoTail]
    -- Old.AddFixed v _    -> [NoTail]
    -- Old.GetCilkWorkerNum -> [NoTail]
    -- Old.LetAvail vs bod -> [NoTail]
    -- Old.AllocateTagHere loc _ -> [NoTail]
    -- Old.AllocateScalarsHere loc -> [NoTail]
    -- Old.SSPush _ a b _ -> [NoTail]
    -- Old.SSPop _ a b -> [NoTail]
    -- Old.LetRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)

    unionMapLambda = (\(locSet, m) (locSet', m') -> (S.union locSet locSet', m))

freeLoc :: PreLocExp LocArg -> Maybe LocVar
freeLoc exp = case exp of
    AfterConstantLE c loc -> Just (toLocVar loc)
    AfterVariableLE v loc b -> Just (toLocVar loc)
    FromEndLE loc -> Just (toLocVar loc)
    _ -> Nothing

changeLocData :: PreLocExp LocArg -> LocVar -> PreLocExp LocArg
changeLocData exp var = case exp of
    AfterConstantLE c loc -> case loc of
        NewL2.Loc lrem -> AfterConstantLE c (NewL2.Loc lrem{lremMode = OutputMutable})
        _ -> exp
    AfterVariableLE v loc b -> case loc of
        NewL2.Loc lrem -> AfterVariableLE v (NewL2.Loc lrem{lremMode = OutputMutable}) b
        _ -> exp
    FromEndLE loc -> case loc of
        NewL2.Loc lrem -> FromEndLE $ NewL2.Loc lrem{lremMode = OutputMutable}
        _ -> exp
        _ -> exp

-- Old.LetRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)
-- Old.LetParRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)
-- Old.LetLocE loc locexp bod -> S.delete loc (allFreeVars bod `S.union` gFreeVars locexp)
-- Old.StartOfPkdCursor v -> S.singleton v
-- Old.TagCursor a b-> S.fromList [a,b]
-- Old.RetE locs v     -> S.insert v (S.fromList (map toLocVar locs))
-- Old.FromEndE loc    -> S.singleton (toLocVar loc)
-- Old.BoundsCheck _ reg cur -> S.fromList (map toLocVar [reg, cur])
-- Old.IndirectionE _ _ (a,b) (c,d) _ -> S.fromList $ [toLocVar a, toLocVar b, toLocVar c, toLocVar d]
-- Old.AddFixed v _    -> S.singleton v
-- Old.GetCilkWorkerNum-> S.empty
-- Old.LetAvail vs bod -> S.fromList vs `S.union` gFreeVars bod
-- Old.AllocateTagHere loc _ -> S.singleton loc
-- Old.AllocateScalarsHere loc -> S.singleton loc
-- Old.SSPush _ a b _ -> S.fromList [a,b]
-- Old.SSPop _ a b -> S.fromList [a,b]

markTailCallsFnBodyHelper :: Int -> NewL2.Exp2 -> TailRecType
markTailCallsFnBodyHelper depth exp2 = case exp2 of
    --   VarE v -> False
    --   LitE _ -> False
    --   CharE{} -> False
    --   FloatE{} -> False
    --   LitSymE _ -> False
    --   AppE v locs args -> False
    --   PrimAppE p args -> False
    LetE (v, _, _, rhs) bod ->
        if True --depth == 0
            then case rhs of
                -- TODO
                -- Here, check if the data con is the one that's in the return type.
                -- Then, also return the output loc that in the datacon, only that loc should be marked as OutputMutable
                DataConE loc d args -> markTailCallsFnBodyHelper (depth + 1) bod {-dbgTraceIt ("Here2!") dbgTraceIt (sdoc rhs)-}
                -- TODO: figure out a way to get the return type of the function
                --let tyConOfDataConE = getTyOfDataCon ddefs d
                --    returnTy = outTy ty2
                -- in if tyConOfDataConE == returnTy
                --    then markTailCallsFnBodyHelper ddefs bod ty2 (depth+1)
                --    else NoTail
                _ -> NoTail {- dbgTraceIt (sdoc rhs) dbgTraceIt ("Here!")-}
            else NoTail {-dbgTraceIt ("Here3!")-}
            --   IfE a b c ->
            --   MkProdE ls ->
            --   ProjE i e ->
            --   CaseE scrt brs ->
            --   DataConE loc c args ->
            --   TimeIt e _ _ ->
            --   MapE _ e ->
            --   FoldE _ _ e ->
            --   SpawnE v locs _ ->
            --   SyncE ->
            --   WithArenaE _v e ->
    Ext ext -> case ext of
        -- Old.LetRegionE r _ _ bod ->
        -- Old.LetParRegionE r _ _ bod ->
        -- Old.LetLocE loc locexp bod ->
        -- Old.StartOfPkdCursor v ->
        -- Old.TagCursor a b ->
        Old.RetE locs v ->
            if depth == 0
                then TC
                else
                    if depth == 1
                        then TMC
                        else NoTail
        -- Old.FromEndE loc    ->
        -- Old.BoundsCheck _ reg cur ->
        -- Old.IndirectionE _ _ (a,b) (c,d) _ ->
        -- Old.AddFixed v _    ->
        -- Old.GetCilkWorkerNum->
        -- Old.LetAvail vs bod ->
        -- Old.AllocateTagHere loc _ ->
        -- Old.AllocateScalarsHere loc ->
        -- Old.SSPush _ a b _ ->
        -- Old.SSPop _ a b ->
        _ -> NoTail
    _ -> NoTail

markMutableLocsAfterInitialPass :: TrackLocVariables -> NewL2.Exp2 -> NewL2.Exp2
markMutableLocsAfterInitialPass env exp =
    case exp of
        VarE v -> exp
        LitE l -> exp
        CharE c -> exp
        FloatE f -> exp
        LitSymE v -> exp
        AppE (v, t) locs args ->
            let args' = P.map (markMutableLocsAfterInitialPass env) args
                locs' =
                    P.map
                        ( \l -> case l of
                            Loc (LREM l' r e _) -> case (backTrackLocs env l' False M.empty) of
                                (False, _) -> l
                                (True, _) -> Loc (LREM l' r e OutputMutable)
                            _ -> l
                        )
                        locs
             in AppE (v, t) locs' args'
        PrimAppE p args ->
            let args' = P.map (markMutableLocsAfterInitialPass env) args
             in PrimAppE p args'
        LetE (v, loc, ty, rhs) bod ->
            let rhs' = markMutableLocsAfterInitialPass env rhs
                bod' = markMutableLocsAfterInitialPass env bod
             in LetE (v, loc, ty, rhs') bod'
        IfE a b c ->
            let a' = markMutableLocsAfterInitialPass env a
                b' = markMutableLocsAfterInitialPass env b
                c' = markMutableLocsAfterInitialPass env c
             in IfE a' b' c'
        MkProdE ls ->
            let ls' = P.map (markMutableLocsAfterInitialPass env) ls
             in MkProdE ls'
        ProjE i e ->
            let e' = markMutableLocsAfterInitialPass env e
             in ProjE i e'
        -- [(DataCon, [(Var,loc)], EXP)]
        CaseE scrt brs ->
            let brs' =
                    P.map
                        ( \(a, b, c) ->
                            let c' = markMutableLocsAfterInitialPass env c
                             in (a, b, c')
                        )
                        brs
             in CaseE scrt brs'
        -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
        DataConE loc c args ->
            let locInDataCon = toLocVar loc
             in case (backTrackLocs env locInDataCon False M.empty) of
                    (False, _) ->
                        let args' = P.map (markMutableLocsAfterInitialPass env) args
                         in DataConE loc c args'
                    (True, _) ->
                        let loc' = case loc of
                                NewL2.Loc lrem -> NewL2.Loc lrem{lremMode = OutputMutable}
                                _ -> loc
                            args' = P.map (markMutableLocsAfterInitialPass env) args
                         in DataConE loc' c args'
        TimeIt e d b ->
            let e' = markMutableLocsAfterInitialPass env e
             in TimeIt e' d b
        MapE d e ->
            let e' = markMutableLocsAfterInitialPass env e
             in MapE d e'
        FoldE i it e ->
            let e' = markMutableLocsAfterInitialPass env e
             in FoldE i it e'
        -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
        SpawnE v locs exps ->
            let exps' = P.map (markMutableLocsAfterInitialPass env) exps
             in SpawnE v locs exps'
        SyncE -> exp
        WithArenaE _v e ->
            let e' = markMutableLocsAfterInitialPass env e
             in WithArenaE _v e'
        Ext ext ->
            case ext of
                Old.LetRegionE r a b bod ->
                    let bod' = markMutableLocsAfterInitialPass env bod
                     in Ext $ Old.LetParRegionE r a b bod'
                Old.LetParRegionE r a b bod ->
                    let bod' = markMutableLocsAfterInitialPass env bod
                     in Ext $ Old.LetParRegionE r a b bod'
                Old.LetLocE loc locexp bod ->
                    let locInExp = freeLoc locexp
                        bod' = markMutableLocsAfterInitialPass env bod
                        locexp' = case locInExp of
                            Nothing -> locexp
                            Just l -> case (backTrackLocs env l False M.empty) of
                                (False, _) -> locexp
                                (True, _) -> changeLocData locexp l
                        loc' = case (backTrackLocs env (toLocVar loc) False M.empty) of
                            (False, _) -> loc
                            (True, _) -> case loc of
                                Loc lrem -> Loc lrem{lremMode = OutputMutable}
                                _ -> loc
                     in Ext $ Old.LetLocE loc' locexp' bod'
                Old.BoundsCheck a reg cur ->
                    let locInCur = toLocVar cur
                     in case (backTrackLocs env locInCur False M.empty) of
                            (False, _) -> Ext ext
                            (True, _) ->
                                let cur' = case cur of
                                        NewL2.Loc lrem -> NewL2.Loc lrem{lremMode = OutputMutable}
                                        _ -> cur
                                 in Ext $ Old.BoundsCheck a reg cur'
                Old.AllocateTagHere loc tycon ->
                    let loc' = case (backTrackLocs env (toLocVar loc) False M.empty) of
                            (False, _) -> loc
                            (True, _) -> case loc of
                                Loc lrem -> Loc lrem{lremMode = OutputMutable}
                                _ -> loc
                     in Ext $ Old.AllocateTagHere loc' tycon
                Old.AllocateScalarsHere loc ->
                    let loc' = case (backTrackLocs env (toLocVar loc) False M.empty) of
                            (False, _) -> loc
                            (True, _) -> case loc of
                                Loc lrem -> Loc lrem{lremMode = OutputMutable}
                                _ -> loc
                     in Ext $ Old.AllocateScalarsHere loc'
                _ -> Ext ext

-- Old.StartOfPkdCursor v -> [NoTail]
-- Old.TagCursor a b -> [NoTail]
-- Old.RetE locs v -> [NoTail]
-- Old.FromEndE loc -> [NoTail]
-- Old.BoundsCheck _ reg cur -> [NoTail]
-- Old.IndirectionE _ _ (a,b) (c,d) _ -> [NoTail]
-- Old.AddFixed v _    -> [NoTail]
-- Old.GetCilkWorkerNum -> [NoTail]
-- Old.LetAvail vs bod -> [NoTail]
-- Old.AllocateTagHere loc _ -> [NoTail]
-- Old.AllocateScalarsHere loc -> [NoTail]
-- Old.SSPush _ a b _ -> [NoTail]
-- Old.SSPop _ a b -> [NoTail]
-- Old.LetRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)

copyOutputMutableBeforeCallsAndReplace :: NewL2.Exp2 -> PassM NewL2.Exp2
copyOutputMutableBeforeCallsAndReplace exp = case exp of
    VarE v -> return exp
    LitE l -> return exp
    CharE c -> return exp
    FloatE f -> return exp
    LitSymE v -> return exp
    AppE (v, t) locs args -> do
        args' <- mapM copyOutputMutableBeforeCallsAndReplace args
        return $ AppE (v, t) locs args'
    PrimAppE p args -> do
        args' <- mapM copyOutputMutableBeforeCallsAndReplace args
        return $ PrimAppE p args'
    LetE (v, lca, ty, rhs) bod -> do
        case rhs of
            AppE (v', t) locs args ->
                if True --should a t == TMC or similar check be necessary ?
                    then do
                        let outputMutableLocs =
                                P.concatMap
                                    ( \l -> case l of
                                        Loc (LREM lc _ _ m) ->
                                            if m == OutputMutable
                                                then [l]
                                                else []
                                        _ -> []
                                    )
                                    locs
                        -- create new LetLoc binds for all mutable locations passed to the TMC call.
                        (letList :: [E2Ext loc dec], locMap) <-
                            foldrM
                                ( \l (lst, map) -> case l of
                                    Loc (LREM ll a b m') -> do
                                        -- use gemsym to get name for a new varible
                                        new_loc <- gensym "loc"
                                        let locexp = AfterConstantLE 0 l
                                        let map' = M.insert ll new_loc map
                                        let new_loc_arg = Loc (LREM new_loc a b m') -- TODO: should this be outputMutable or just Output
                                        return $ (lst ++ [NewL2.LetLocE new_loc_arg locexp (VarE new_loc)], map')
                                )
                                ([], M.empty)
                                outputMutableLocs
                        -- fix all downstream locs.
                        rhs' <- copyOutputMutableBeforeCallsAndReplace rhs
                        bod' <- replaceLocsHelper locMap bod
                        bod'' <- copyOutputMutableBeforeCallsAndReplace bod'
                        let sub_exp = LetE (v, lca, ty, rhs') bod''
                        exp' <-
                            foldrM
                                ( \expr expr' -> case expr of
                                    NewL2.LetLocE new_loc locexp bd -> return $ Ext $ NewL2.LetLocE new_loc locexp expr'
                                )
                                sub_exp
                                letList
                        return $ exp'
                    else do
                        rhs' <- copyOutputMutableBeforeCallsAndReplace rhs
                        bod' <- copyOutputMutableBeforeCallsAndReplace bod
                        return $ LetE (v, lca, ty, rhs') bod'
            _ -> do
                rhs' <- copyOutputMutableBeforeCallsAndReplace rhs
                bod' <- copyOutputMutableBeforeCallsAndReplace bod
                return $ LetE (v, lca, ty, rhs') bod'
    IfE a b c -> do
        a' <- copyOutputMutableBeforeCallsAndReplace a
        b' <- copyOutputMutableBeforeCallsAndReplace b
        c' <- copyOutputMutableBeforeCallsAndReplace c
        return $ IfE a' b' c'
    MkProdE ls -> do
        ls' <- mapM copyOutputMutableBeforeCallsAndReplace ls
        return $ MkProdE ls'
    ProjE i e -> do
        e' <- copyOutputMutableBeforeCallsAndReplace e
        return $ ProjE i e'
    -- [(DataCon, [(Var,loc)], EXP)]
    CaseE scrt brs -> do
        brs' <-
            mapM
                ( \(a, b, c) -> do
                    c' <- copyOutputMutableBeforeCallsAndReplace c
                    return (a, b, c')
                )
                brs
        return $ CaseE scrt brs'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    DataConE loc c args -> do
        args' <- mapM copyOutputMutableBeforeCallsAndReplace args
        return $ DataConE loc c args'
    TimeIt e d b -> do
        e' <- copyOutputMutableBeforeCallsAndReplace e
        return $ TimeIt e' d b
    MapE d e -> do
        e' <- copyOutputMutableBeforeCallsAndReplace e
        return $ MapE d e'
    FoldE i it e -> do
        e' <- copyOutputMutableBeforeCallsAndReplace e
        return $ FoldE i it e'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    SpawnE v locs exps -> do
        exps' <- mapM copyOutputMutableBeforeCallsAndReplace exps
        return $ SpawnE v locs exps'
    SyncE -> return exp
    WithArenaE _v e -> do
        e' <- copyOutputMutableBeforeCallsAndReplace e
        return $ WithArenaE _v e'
    Ext ext ->
        case ext of
            Old.LetRegionE r a b bod -> do
                bod' <- copyOutputMutableBeforeCallsAndReplace bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetParRegionE r a b bod -> do
                bod' <- copyOutputMutableBeforeCallsAndReplace bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetLocE loc locexp bod -> do
                bod' <- copyOutputMutableBeforeCallsAndReplace bod
                return $ Ext $ Old.LetLocE loc locexp bod'
            _ -> return $ Ext ext

-- Old.StartOfPkdCursor v -> [NoTail]
-- Old.TagCursor a b -> [NoTail]
-- Old.RetE locs v -> [NoTail]
-- Old.FromEndE loc -> [NoTail]
-- Old.BoundsCheck _ reg cur -> [NoTail]
-- Old.IndirectionE _ _ (a,b) (c,d) _ -> [NoTail]
-- Old.AddFixed v _    -> [NoTail]
-- Old.GetCilkWorkerNum -> [NoTail]
-- Old.LetAvail vs bod -> [NoTail]
-- Old.AllocateTagHere loc _ -> [NoTail]
-- Old.AllocateScalarsHere loc -> [NoTail]
-- Old.SSPush _ a b _ -> [NoTail]
-- Old.SSPop _ a b -> [NoTail]
-- Old.LetRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)

replaceLocsHelper :: M.Map LocVar LocVar -> NewL2.Exp2 -> PassM NewL2.Exp2
replaceLocsHelper map exp = case exp of
    VarE v -> return exp
    LitE l -> return exp
    CharE c -> return exp
    FloatE f -> return exp
    LitSymE v -> return exp
    AppE (v, t) locs args -> do
        let locs' =
                P.map
                    ( \l -> case l of
                        Loc (LREM l' r' e' m') -> case M.lookup l' map of
                            Nothing -> l
                            Just l'' -> Loc (LREM l'' r' e' m')
                        _ -> l
                    )
                    locs
        args' <- mapM (replaceLocsHelper map) args
        return $ AppE (v, t) locs' args'
    PrimAppE p args -> do
        args' <- mapM (replaceLocsHelper map) args
        return $ PrimAppE p args'
    LetE (v, locs, ty, rhs) bod -> do
        let locs' =
                P.map
                    ( \l -> case M.lookup (toLocVar l) map of
                        Nothing -> l
                        Just l' -> case l of
                            Loc (LREM _ r e m) -> Loc (LREM l' r e m)
                    )
                    locs
        rhs' <- replaceLocsHelper map rhs
        bod' <- replaceLocsHelper map bod
        return $ LetE (v, locs', ty, rhs') bod'
    IfE a b c -> do
        a' <- replaceLocsHelper map a
        b' <- replaceLocsHelper map b
        c' <- replaceLocsHelper map c
        return $ IfE a' b' c'
    MkProdE ls -> do
        ls' <- mapM (replaceLocsHelper map) ls
        return $ MkProdE ls'
    ProjE i e -> do
        e' <- replaceLocsHelper map e
        return $ ProjE i e'
    -- [(DataCon, [(Var,loc)], EXP)]
    CaseE scrt brs -> do
        brs' <-
            mapM
                ( \(a, b, c) -> do
                    let b' =
                            P.map
                                ( \(v, loc) -> case M.lookup (toLocVar loc) map of
                                    Nothing -> (v, loc)
                                    Just l -> case loc of
                                        Loc (LREM _ r e m) -> (v, Loc (LREM l r e m))
                                )
                                b
                    c' <- replaceLocsHelper map c
                    return (a, b', c')
                )
                brs
        return $ CaseE scrt brs'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    DataConE loc c args -> do
        let loc' = case M.lookup (toLocVar loc) map of
                Nothing -> loc
                Just l -> case loc of
                    Loc (LREM _ r e m) -> Loc (LREM l r e m)
        args' <- mapM (replaceLocsHelper map) args
        return $ DataConE loc' c args'
    TimeIt e d b -> do
        e' <- replaceLocsHelper map e
        return $ TimeIt e' d b
    MapE d e -> do
        e' <- replaceLocsHelper map e
        return $ MapE d e'
    FoldE i it e -> do
        e' <- replaceLocsHelper map e
        return $ FoldE i it e'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    SpawnE v locs exps -> do
        exps' <- mapM (replaceLocsHelper map) exps
        return $ SpawnE v locs exps'
    SyncE -> return exp
    WithArenaE _v e -> do
        e' <- replaceLocsHelper map e
        return $ WithArenaE _v e'
    Ext ext ->
        case ext of
            Old.LetRegionE r a b bod -> do
                bod' <- replaceLocsHelper map bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetParRegionE r a b bod -> do
                bod' <- replaceLocsHelper map bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetLocE loc locexp bod -> do
                let locexp' = case locexp of
                        StartOfRegionLE r -> locexp
                        AfterConstantLE i loc -> case M.lookup (toLocVar loc) map of
                            Nothing -> locexp
                            Just l -> case loc of
                                Loc (LREM a b c d) -> AfterConstantLE i (Loc (LREM l b c d))
                        AfterVariableLE v loc b -> case M.lookup (toLocVar loc) map of
                            Nothing -> locexp
                            Just l -> case loc of
                                Loc (LREM _ r e m) -> AfterVariableLE v (Loc (LREM l r e m)) b
                        InRegionLE r -> locexp
                        FreeLE -> locexp
                        FromEndLE loc -> case M.lookup (toLocVar loc) map of
                            Nothing -> locexp
                            Just l -> case loc of
                                Loc (LREM _ r e m) -> FromEndLE (Loc (LREM l r e m))
                bod' <- replaceLocsHelper map bod
                return $ Ext $ Old.LetLocE loc locexp' bod'
            _ -> return $ Ext ext

-- Old.StartOfPkdCursor v -> [NoTail]
-- Old.TagCursor a b -> [NoTail]
-- Old.RetE locs v -> [NoTail]
-- Old.FromEndE loc -> [NoTail]
-- Old.BoundsCheck _ reg cur -> [NoTail]
-- Old.IndirectionE _ _ (a,b) (c,d) _ -> [NoTail]
-- Old.AddFixed v _    -> [NoTail]
-- Old.GetCilkWorkerNum -> [NoTail]
-- Old.LetAvail vs bod -> [NoTail]
-- Old.AllocateTagHere loc _ -> [NoTail]
-- Old.AllocateScalarsHere loc -> [NoTail]
-- Old.SSPush _ a b _ -> [NoTail]
-- Old.SSPop _ a b -> [NoTail]
-- Old.LetRegionE r _ _ bod -> S.delete (Old.regionToVar r) (allFreeVars bod)
