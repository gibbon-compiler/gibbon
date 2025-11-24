module Gibbon.Passes.InferCallType (inferCallType) where

import Data.Foldable (foldrM)
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude as P

import Gibbon.Common
import Gibbon.L2.Syntax as Old
import Gibbon.NewL2.Syntax as NewL2


-- ^ A map that tracks location variables that need to be mutable.

type TrackLocVariables = M.Map LocVar (S.Set LocVar, Bool)

inferCallType :: NewL2.Prog2 -> PassM NewL2.Prog2
inferCallType Prog{ddefs, fundefs, mainExp} = do
    fds' <- mapM (inferCallTypeFn ddefs) $ M.elems fundefs
    let newFundefs = M.fromList $ map (\f -> (funName f, f)) fds'
    let newProg = Prog{ddefs = ddefs, fundefs = newFundefs, mainExp = mainExp}
    pure $ newProg {- dbgTrace minChatLvl (sdoc newProg) dbgTrace minChatLvl (sdoc $ M.elems fundefs')-}

inferCallTypeFn :: NewL2.DDefs2 -> NewL2.FunDef2 -> PassM NewL2.FunDef2
inferCallTypeFn _ddefs _f@FunDef{funName, funArgs, funTy, funMeta, funBody} = do
    let (funBody', _env, _tailTy) = inferCallTypeFnBody funName M.empty funBody
        --(ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = dbgTrace minChatLvl "Print env at the end." dbgTrace minChatLvl (sdoc (_env, M.elems _env)) dbgTrace minChatLvl "End\n" funTy
        -- locVars' =
        --     P.map
        --         ( \(LRM l r m) -> case (backTrackLocs env l False M.empty) of
        --             (False, _) -> LRM l r m
        --             (True, _) -> LRM l r OutputMutable
        --         )
        --         locVars
        -- funTy' = (ArrowTy2 locVars' arrIns _arrEffs arrOut _locRets _isPar)
        --funBody'' = markMutableLocsAfterInitialPass env funBody'
        meta@FunMeta{funRec} = funMeta
        funRec' = case _tailTy of 
                        Just TailCall -> TailRec 
                        Just TailModuloCons -> TailRec 
                        _ -> funRec
        funMeta' = meta{funRec=funRec'}
        -- If a function is identified to be tailRecursive
        -- Here is the blueprint of what we want to do 
        -- TODO: don't make tail recursion optimization automatic 
        -- make a compiler flag to enable it in cursorize at the very least.
        -- AoS: 
        -- 1.) TailModCons -- We need to make OutputPutMutable
        -- 2.) We always keep the Inputs ReadOnly 
        -- 3.) We try to make the function return void. 
        -- SoA: 
        -- 1.) We make all inputs/outputs mutable and try to make the function 
        -- return void.
    --funBody''' <- copyOutputMutableBeforeCallsAndReplace funBody''
    dbgTrace minChatLvl "Print tail call type!" dbgTrace minChatLvl (sdoc (funName, _tailTy)) dbgTrace minChatLvl "End tail call type!" return $ FunDef funName funArgs funTy funBody' funMeta'

--  if tailCallTy == TMC
--  then
--     let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = funTy
--         locVars' = P.map (\(LRM l r m) -> if m == Output
--                                           then LRM l r OutputMutable
--                                           else LRM l r m
--                          ) locVars
--         funTy' = (ArrowTy2 locVars' arrIns _arrEffs arrOut _locRets _isPar)
--       in return $ FunDef funName funArgs funTy' funBody' funMeta  {-dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy')) dbgTrace minChatLvl "a" dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy')) dbgTrace minChatLvl "a"  -}
--  else if tailCallTy == TC
--  then
--     let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) = funTy
--         funTy' = (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar)
--       in return $ FunDef funName funArgs funTy' funBody' funMeta {-dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy')) dbgTrace minChatLvl "b" dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy')) dbgTrace minChatLvl "b"  -}
--  else pure f {-dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy)) dbgTrace minChatLvl "c" dbgTrace minChatLvl (sdoc (tailCallTy, funName, funTy)) dbgTrace minChatLvl "c"-}
--  --dbgTrace minChatLvl (sdoc tailCallTy) pure f
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
            visited'' = M.insert v True visited'
            accum'' = accum' || mut
         in (accum'', visited'')

inferCallTypeFnBody :: Var -> TrackLocVariables -> NewL2.Exp2 -> (NewL2.Exp2, TrackLocVariables, Maybe TailRecType)
inferCallTypeFnBody funName env exp2 = case exp2 of
    VarE v -> (VarE v, env, Nothing)
    LitE l -> (LitE l, env, Nothing)
    CharE c -> (CharE c, env, Nothing)
    FloatE f -> (FloatE f, env, Nothing)
    LitSymE v -> (LitSymE v, env, Nothing)
    AppE v t locs args ->
        let results = P.map (inferCallTypeFnBody funName env) args
            args' = P.map fst3 results
            env' = M.unionsWith unionMapLambda $ P.map snd3 results
            tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
         in (AppE v t locs args', env', tailTy)
    PrimAppE p args ->
        let results = P.map (inferCallTypeFnBody funName env) args
            args' = P.map fst3 results
            env' = M.unionsWith unionMapLambda $ P.map snd3 results
            tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
         in (PrimAppE p args', env', tailTy)
    LetE (v, loc, ty, rhs) bod -> case rhs of
        AppE v' _ locs' args' ->
            if v' == funName
                then
                    let tailCallType = inferCallTypeFnBodyHelper 0 bod
                        env' = case tailCallType of
                            UnknownTailType -> env
                            NotTailRec -> env
                            TailCall -> env
                            TailModuloCons ->
                                P.foldr
                                    ( \innerloc e -> case M.lookup (toLocVar innerloc) e of
                                        Nothing -> case innerloc of
                                            Loc (LREM _l' _r' _e' m') -> case m' of
                                                Output -> M.insert (toLocVar innerloc) (S.empty, True) e
                                                OutputMutable -> M.insert (toLocVar innerloc) (S.empty, True) e
                                                _ -> e
                                            _ -> e
                                        Just (s, _m) -> case innerloc of
                                            Loc (LREM _l' _r' _e' m') -> case m' of
                                                Output -> M.insert (toLocVar innerloc) (s, True) e
                                                OutputMutable -> M.insert (toLocVar innerloc) (s, True) e
                                                _ -> e
                                            _ -> e
                                    )
                                    env
                                    locs'
                        rhs' = dbgTrace minChatLvl "Print tailCallType: " dbgTrace minChatLvl (sdoc tailCallType) dbgTrace minChatLvl "End tailCallType!\n" AppE v' tailCallType locs' args'
                        (rhs'', env'', t1) = inferCallTypeFnBody funName env' rhs'
                        (bod', env''', t2) = inferCallTypeFnBody funName env'' bod
                        ret_lst = [Just tailCallType, t1, t2]
                        ret_lst' = concatMap (\l -> case l of 
                                                       Nothing -> [] 
                                                       Just x -> [x]          
                                            ) ret_lst
                        ret_lst'' = case ret_lst' of 
                                            [] -> Nothing 
                                            rst -> Just $ P.minimum rst
                     in (LetE (v, loc, ty, rhs'') bod', env''', ret_lst'')
                else
                    let (rhs', env', t1) = inferCallTypeFnBody funName env rhs
                        (bod', env'', t2) = inferCallTypeFnBody funName env' bod
                        ret_lst = [t1, t2]
                        ret_lst' = concatMap (\l -> case l of 
                                                       Nothing -> [] 
                                                       Just x -> [x]          
                                            ) ret_lst
                        ret_lst'' = case ret_lst' of 
                                            [] -> Nothing 
                                            rst -> Just $ P.minimum rst
                     in (LetE (v, loc, ty, rhs') bod', env'', ret_lst'')
        _ ->
            let (rhs', env', tailTy) = inferCallTypeFnBody funName env rhs
                (bod', env'', tailTy') = inferCallTypeFnBody funName env' bod
                ret_lst = [tailTy, tailTy']
                ret_lst' = concatMap (\l -> case l of 
                                                       Nothing -> [] 
                                                       Just x -> [x]          
                                            ) ret_lst
                ret_lst'' = case ret_lst' of 
                                            [] -> Nothing 
                                            rst -> Just $ P.minimum rst
             in (LetE (v, loc, ty, rhs') bod', env'', ret_lst'')
    IfE a b c ->
        let (a', e1, t) = inferCallTypeFnBody funName env a
            (b', e2, t1) = inferCallTypeFnBody funName e1 b
            (c', e3, t2) = inferCallTypeFnBody funName e2 c
            ret_lst = [t, t1, t2]
            ret_lst' = concatMap (\l -> case l of 
                                                       Nothing -> [] 
                                                       Just x -> [x]          
                                            ) ret_lst
            ret_lst'' = case ret_lst' of 
                                            [] -> Nothing 
                                            rst -> Just $ P.minimum rst
         in (IfE a' b' c', e3, ret_lst'')
    MkProdE ls ->
        let results = P.map (inferCallTypeFnBody funName env) ls
            ls' = P.map fst3 results
            env' = M.unionsWith unionMapLambda $ P.map snd3 results
            tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst' 
         in (MkProdE ls', env', tailTy)
    ProjE i e ->
        let (e', env', t) = inferCallTypeFnBody funName env e
         in (ProjE i e', env', t)
    -- [(DataCon, [(Var,loc)], EXP)]
    CaseE scrt brs ->
        let results =
                P.map
                    ( \(a, b, c) ->
                        let (c', env', t) = inferCallTypeFnBody funName env c
                         in ((a, b, c'), env', t)
                    )
                    brs
            brs' = P.map fst3 results
            env'' = M.unionsWith unionMapLambda $ P.map snd3 results
            tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
         in (CaseE scrt brs', env'', tailTy)
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    DataConE loc c args ->
        let locInDataCon = dbgTrace minChatLvl "In DataCon:" dbgTrace minChatLvl (sdoc (env, M.elems env)) dbgTrace minChatLvl ("End\n") toLocVar loc
         in case (backTrackLocs env locInDataCon False M.empty) of
                (False, _) ->
                    let results = P.map (inferCallTypeFnBody funName env) args
                        args' = P.map fst3 results
                        env' = M.unionsWith unionMapLambda $ P.map snd3 results
                        tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
                     in (DataConE loc c args', env', tailTy)
                (True, _) ->
                    let loc' = case loc of
                            NewL2.Loc lrem -> NewL2.Loc lrem{lremMode = OutputMutable}
                            _ -> loc
                        results = P.map (inferCallTypeFnBody funName env) args
                        args' = P.map fst3 results
                        env' = M.unionsWith unionMapLambda $ P.map snd3 results
                        tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
                     in (DataConE loc' c args', env', tailTy)
    TimeIt e d b ->
        let (e', env', t) = inferCallTypeFnBody funName env e
         in (TimeIt e' d b, env', t)
    MapE d e ->
        let (e', env', t) = inferCallTypeFnBody funName env e
         in (MapE d e', env', t)
    FoldE i it e ->
        let (e', env', t) = inferCallTypeFnBody funName env e
         in (FoldE i it e', env', t)
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    SpawnE v locs exps ->
        let results = P.map (inferCallTypeFnBody funName env) exps
            exps' = P.map fst3 results
            env' = M.unionsWith unionMapLambda $ P.map snd3 results
            tailTy = case P.map thd3 results of 
                                [] -> Nothing
                                lst -> let lst' = concatMap (\l -> case l of 
                                                                  Nothing -> []
                                                                  Just x -> [x]
                                                             ) lst 
                                        in case lst' of 
                                                 [] -> Nothing 
                                                 _ -> Just $ P.minimum lst'
         in (SpawnE v locs exps', env', tailTy)
    SyncE -> (exp2, env, Nothing)
    WithArenaE _v e ->
        let (e', env', t) = inferCallTypeFnBody funName env e
         in (WithArenaE _v e', env', t)
    Ext ext ->
        case ext of
            Old.LetRegionE r a b bod ->
                let (bod', env', t) = inferCallTypeFnBody funName env bod
                 in (Ext $ Old.LetRegionE r a b bod', env', t)
            Old.LetParRegionE r a b bod ->
                let (bod', env', t) = inferCallTypeFnBody funName env bod
                 in (Ext $ Old.LetParRegionE r a b bod', env', t)
            Old.LetLocE loc locexp bod ->
                let locInExp = freeLoc locexp
                    env' = case locInExp of
                        Nothing -> env
                        Just l -> M.insert l (S.singleton (toLocVar loc), False) env
                    (bod', env'', t) = inferCallTypeFnBody funName env' bod
                    locexp' = case locInExp of
                        Nothing -> locexp
                        Just l -> case (backTrackLocs env'' l False M.empty) of
                            (False, _) -> locexp
                            (True, _) -> changeLocData locexp l
                 in (Ext $ Old.LetLocE loc locexp' bod', env'', t)
            Old.LetRegE reg regexp bod -> 
                let (bod', env', t) = inferCallTypeFnBody funName env bod
                 in (Ext $ Old.LetRegE reg regexp bod', env', t)
            Old.BoundsCheckVector _bounds -> (exp2, env, Nothing)
            Old.RetE{} -> (exp2, env, Nothing)
            Old.StartOfPkdCursor{} -> (exp2, env, Nothing)
            Old.TagCursor{} -> (exp2, env, Nothing)
            Old.FromEndE{} -> (exp2, env, Nothing)
            Old.BoundsCheck{} -> (exp2, env, Nothing)
            Old.IndirectionE{} -> (exp2, env, Nothing)
            Old.AddFixed{}    -> (exp2, env, Nothing)
            Old.GetCilkWorkerNum -> (exp2, env, Nothing)
            Old.LetAvail{} -> (exp2, env, Nothing)
            Old.AllocateTagHere{} -> (exp2, env, Nothing)
            Old.AllocateScalarsHere{} -> (exp2, env, Nothing)
            Old.SSPush{} -> (exp2, env, Nothing)
            Old.SSPop{} -> (exp2, env, Nothing)
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

    unionMapLambda = (\(locSet, m) (locSet', _m') -> (S.union locSet locSet', m))

freeLoc :: PreLocExp LocArg -> Maybe LocVar
freeLoc _exp = case _exp of
    AfterConstantLE _c loc -> Just (toLocVar loc)
    AfterVariableLE _v loc _b -> Just (toLocVar loc)
    FromEndLE loc -> Just (toLocVar loc)
    _ -> Nothing

changeLocData :: PreLocExp LocArg -> LocVar -> PreLocExp LocArg
changeLocData _exp _var = case _exp of
    AfterConstantLE c loc -> case loc of
        NewL2.Loc lrem -> AfterConstantLE c (NewL2.Loc lrem{lremMode = OutputMutable})
        _ -> _exp
    AfterVariableLE v loc b -> case loc of
        NewL2.Loc lrem -> AfterVariableLE v (NewL2.Loc lrem{lremMode = OutputMutable}) b
        _ -> _exp
    FromEndLE loc -> case loc of
        NewL2.Loc lrem -> FromEndLE $ NewL2.Loc lrem{lremMode = OutputMutable}
        _ -> _exp
    _ -> _exp

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

inferCallTypeFnBodyHelper :: Int -> NewL2.Exp2 -> TailRecType
inferCallTypeFnBodyHelper depth exp2 = case exp2 of
    --   VarE v -> False
    --   LitE _ -> False
    --   CharE{} -> False
    --   FloatE{} -> False
    --   LitSymE _ -> False
    --   AppE v locs args -> False
    --   PrimAppE p args -> False
    LetE (_v, _, _, rhs) bod ->
        if True --depth == 0
            then case rhs of
                -- TODO
                -- Here, check if the data con is the one that's in the return type.
                -- Then, also return the output loc that in the datacon, only that loc should be marked as OutputMutable
                DataConE _loc _d _args -> inferCallTypeFnBodyHelper (depth + 1) bod {-dbgTrace minChatLvl ("Here2!") dbgTrace minChatLvl (sdoc rhs)-}
                -- TODO: figure out a way to get the return type of the function
                --let tyConOfDataConE = getTyOfDataCon ddefs d
                --    returnTy = outTy ty2
                -- in if tyConOfDataConE == returnTy
                --    then inferCallTypeFnBodyHelper ddefs bod ty2 (depth+1)
                --    else NoTail
                _ -> NotTailRec {- dbgTrace minChatLvl (sdoc rhs) dbgTrace minChatLvl ("Here!")-}
            else NotTailRec {-dbgTrace minChatLvl ("Here3!")-}
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
        Old.RetE _locs _v ->
            if depth == 0
                then TailCall
                else
                    if depth == 1
                        then TailModuloCons
                        else NotTailRec
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
        _ -> NotTailRec
    _ -> NotTailRec

markMutableLocsAfterInitialPass :: TrackLocVariables -> NewL2.Exp2 -> NewL2.Exp2
markMutableLocsAfterInitialPass env _exp =
    case _exp of
        VarE{} -> _exp
        LitE{} -> _exp
        CharE{} -> _exp
        FloatE{} -> _exp
        LitSymE{} -> _exp
        AppE v t locs args ->
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
             in AppE v t locs' args'
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
        SyncE -> _exp
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
                                --Loc lrem -> Loc lrem{lremMode = OutputMutable}
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
copyOutputMutableBeforeCallsAndReplace _exp = case _exp of
    VarE{} -> return _exp
    LitE{} -> return _exp
    CharE{} -> return _exp
    FloatE{} -> return _exp
    LitSymE{} -> return _exp
    AppE v t locs args -> do
        args' <- mapM copyOutputMutableBeforeCallsAndReplace args
        return $ AppE v t locs args'
    PrimAppE p args -> do
        args' <- mapM copyOutputMutableBeforeCallsAndReplace args
        return $ PrimAppE p args'
    LetE (v, lca, ty, rhs) bod -> do
        case rhs of
            AppE _v' _t locs _args ->
                if True --should a t == TMC or similar check be necessary ?
                    then do
                        let outputMutableLocs =
                                P.concatMap
                                    ( \l -> case l of
                                        Loc (LREM _ _ _ m) ->
                                            if m == OutputMutable
                                                then [l]
                                                else []
                                        _ -> []
                                    )
                                    locs
                        -- create new LetLoc binds for all mutable locations passed to the TMC call.
                        (letList :: [E2Ext loc dec], locMap) <-
                            foldrM
                                ( \l (lst, _map) -> case l of
                                    Loc (LREM ll _a _b _m') -> do
                                        -- use gemsym to get name for a new varible
                                        new_loc <- freshCommonLoc "loc" ll
                                        let locexp = AfterConstantLE 0 l
                                        let map' = M.insert ll new_loc _map
                                        let new_loc_arg = Loc (LREM new_loc _a _b _m') -- TODO: should this be outputMutable or just Output
                                        return $ (lst ++ [NewL2.LetLocE new_loc_arg locexp (VarE "")], map')
                                        --return $ (lst ++ [NewL2.LetLocE new_loc locexp (VarE "")], map')
                                    _ -> error "Did not expect!!"
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
                                    NewL2.LetLocE new_loc locexp _bd -> return $ Ext $ NewL2.LetLocE new_loc locexp expr'
                                    _ -> error "Did not Expect!!"
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
    SyncE -> return _exp
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
replaceLocsHelper menv _exp = case _exp of
    VarE{} -> return _exp
    LitE{} -> return _exp
    CharE{} -> return _exp
    FloatE{} -> return _exp
    LitSymE{} -> return _exp
    AppE v t locs args -> do
        let locs' =
                P.map
                    ( \l -> case l of
                        Loc (LREM l' r' e' m') -> case M.lookup l' menv of
                            Nothing -> l
                            Just l'' -> Loc (LREM l'' r' e' m')
                        _ -> l
                    )
                    locs
        args' <- mapM (replaceLocsHelper menv) args
        return $ AppE v t locs' args'
    PrimAppE p args -> do
        args' <- mapM (replaceLocsHelper menv) args
        return $ PrimAppE p args'
    LetE (v, locs, ty, rhs) bod -> do
        let locs' =
                P.map
                    ( \l -> case M.lookup (toLocVar l) menv of
                        Nothing -> l
                        Just l' -> case l of
                            Loc (LREM _ r e m) -> Loc (LREM l' r e m)
                            _ -> error "Did not expect type!!"
                    )
                    locs
        rhs' <- replaceLocsHelper menv rhs
        bod' <- replaceLocsHelper menv bod
        return $ LetE (v, locs', ty, rhs') bod'
    IfE a b c -> do
        a' <- replaceLocsHelper menv a
        b' <- replaceLocsHelper menv b
        c' <- replaceLocsHelper menv c
        return $ IfE a' b' c'
    MkProdE ls -> do
        ls' <- mapM (replaceLocsHelper menv) ls
        return $ MkProdE ls'
    ProjE i e -> do
        e' <- replaceLocsHelper menv e
        return $ ProjE i e'
    -- [(DataCon, [(Var,loc)], EXP)]
    CaseE scrt brs -> do
        brs' <-
            mapM
                ( \(a, b, c) -> do
                    let b' =
                            P.map
                                ( \(v, loc) -> case M.lookup (toLocVar loc) menv of
                                    Nothing -> (v, loc)
                                    Just l -> case loc of
                                        Loc (LREM _ r e m) -> (v, Loc (LREM l r e m))
                                        _ -> error "Did not expect type!"
                                )
                                b
                    c' <- replaceLocsHelper menv c
                    return (a, b', c')
                )
                brs
        return $ CaseE scrt brs'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    DataConE loc c args -> do
        let loc' = case M.lookup (toLocVar loc) menv of
                Nothing -> loc
                Just l -> case loc of
                    Loc (LREM _ r e m) -> Loc (LREM l r e m)
                    _ -> error "did not expect type!"
        args' <- mapM (replaceLocsHelper menv) args
        return $ DataConE loc' c args'
    TimeIt e d b -> do
        e' <- replaceLocsHelper menv e
        return $ TimeIt e' d b
    MapE d e -> do
        e' <- replaceLocsHelper menv e
        return $ MapE d e'
    FoldE i it e -> do
        e' <- replaceLocsHelper menv e
        return $ FoldE i it e'
    -- TODO: Check map for any mutable output locations, if they are in the data con then mark them outputMutable
    SpawnE v locs exps -> do
        exps' <- mapM (replaceLocsHelper menv) exps
        return $ SpawnE v locs exps'
    SyncE -> return _exp
    WithArenaE _v e -> do
        e' <- replaceLocsHelper menv e
        return $ WithArenaE _v e'
    Ext ext ->
        case ext of
            Old.LetRegionE r a b bod -> do
                bod' <- replaceLocsHelper menv bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetParRegionE r a b bod -> do
                bod' <- replaceLocsHelper menv bod
                return $ Ext $ Old.LetParRegionE r a b bod'
            Old.LetLocE loc locexp bod -> do
                let locexp' = case locexp of
                        StartOfRegionLE _r -> locexp
                        AfterConstantLE i locv -> case M.lookup (toLocVar locv) menv of
                            Nothing -> locexp
                            Just l -> case locv of
                                Loc (LREM _a b c d) -> AfterConstantLE i (Loc (LREM l b c d))
                                _ -> error "Did not expect!"
                        AfterVariableLE v locv b -> case M.lookup (toLocVar locv) menv of
                            Nothing -> locexp
                            Just l -> case locv of
                                Loc (LREM _ r e m) -> AfterVariableLE v (Loc (LREM l r e m)) b
                                _ -> error "Did not expect!"
                        InRegionLE _r -> locexp
                        FreeLE -> locexp
                        FromEndLE locv -> case M.lookup (toLocVar locv) menv of
                            Nothing -> locexp
                            Just l -> case locv of
                                Loc (LREM _ r e m) -> FromEndLE (Loc (LREM l r e m))
                                _ -> error "Did not expect!"
                        _ -> error "Did not expected type!"
                bod' <- replaceLocsHelper menv bod
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
