module Gibbon.Passes.ReorderLetExprs (reorderLetExprs) where

import qualified Data.List as L 
import qualified Data.Set as S

import qualified Data.Map as M

import Data.Foldable as F
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L2.Syntax
import Data.Maybe ()
import qualified Data.Maybe as S


data DelayedExpr = LetExpr (Var, [LocVar], Ty2, Exp2)
                 | LetLocExpr LocVar LocExp 
                    deriving (Eq, Ord, Show, Generic)

instance Out DelayedExpr

type DefinedVars = S.Set FreeVarsTy
type DelayedExprMap = M.Map DefinedVars DelayedExpr

reorderLetExprs :: Prog2 -> PassM Prog2
reorderLetExprs (Prog ddefs fundefs mainExp) = do
    fds' <- mapM reorderLetExprsFun (M.elems fundefs)
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
                    Just (e,ty) -> do
                                      (e', env) <- reorderLetExprsFunBody S.empty M.empty e
                                      e'' <- releaseExprsFunBody S.empty env e'
                                      pure $ Just (e'', ty)
                    Nothing     -> pure Nothing
    pure $ Prog ddefs fundefs' mainExp'

reorderLetExprsFun :: FunDef2 -> PassM FunDef2
reorderLetExprsFun f@FunDef{funName,funTy,funArgs,funBody,funMeta} = do
    let args = S.fromList $ map (fromVarToFreeVarsTy) funArgs
    {- Add location variables to defined environment from funTy -}
        inLocs = inLocVars funTy
        outLoc = outLocVars funTy
        locToFreeVarsTy = S.fromList $ map fromLocVarToFreeVarsTy (inLocs ++ outLoc)
        definedVars = S.union args locToFreeVarsTy
    (funBody', env') <- reorderLetExprsFunBody definedVars M.empty funBody
    funBody'' <- releaseExprsFunBody definedVars env' funBody'
    -- dbgTrace (minChatLvl) "Print Meta: " dbgTrace (minChatLvl) (sdoc (funTy, funMeta)) dbgTrace (minChatLvl) "Print end.\n"
    funBody''' <- ensureLocationsAreDefinedForWrite S.empty funBody''
    dbgTrace (minChatLvl) "Print Env: " dbgTrace (minChatLvl) (sdoc (env', funBody''')) dbgTrace (minChatLvl) ("End Print Env.\n") pure $ f { funBody = funBody''' }


{- We also need to release let expressions which are defined -}
reorderLetExprsFunBody :: DefinedVars -> DelayedExprMap -> Exp2 -> PassM (Exp2, DelayedExprMap)
reorderLetExprsFunBody definedVars delayedExprMap ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let freeVarsRhs = case rhs of 
                                   TimeIt e _ _ -> case e of 
                                                      LetE (_, _, _, rhs') bod' -> S.union (allFreeVars rhs') (allFreeVars bod')
                                                      _ -> allFreeVars e
                                   _ -> allFreeVars rhs
                -- pckdLoc = locsInTy ty
                freeVarsRhs' = freeVarsRhs --S.union (S.fromList $ map fromLocVarToFreeVarsTy pckdLoc) freeVarsRhs
                {- Check if variables in rhs are in the DefinedVars-}
                isDefined = S.isSubsetOf freeVarsRhs' definedVars
              in if isDefined 
                 then do
                    let definedVars' = S.insert (fromVarToFreeVarsTy v) definedVars
                    {- Check which expressions can be released -}
                    -- (bod', definedVars'', delayedExprMap') <- foldrM (\(dvars, expr) (body, env, env2) -> do 
                    --                                         let can_release = S.isSubsetOf dvars env 
                    --                                           in if can_release
                    --                                              then do
                    --                                                 case expr of 
                    --                                                     LetExpr (v', locs', ty', rhs') -> do
                    --                                                         let env' = S.insert (fromVarToFreeVarsTy v') env
                    --                                                             new_body = LetE (v', locs', ty', rhs') body
                    --                                                             env2' = M.delete dvars env2
                    --                                                         pure (new_body, env', env2')
                    --                                                     LetLocExpr loc rhs' -> do
                    --                                                         let env' = S.insert (fromLocVarToFreeVarsTy loc) env
                    --                                                             new_body = Ext $ LetLocE loc rhs' body
                    --                                                             env2' = M.delete dvars env2
                    --                                                         pure (new_body, env', env2')
                    --                                              else do
                    --                                                 pure (body, env, env2)
                    --                                   ) (bod, definedVars', delayedExprMap) (M.toList delayedExprMap)
                    (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars' delayedExprMap bod
                    pure $ (LetE (v, locs, ty, rhs) bod', delayedExprMap')
                    -- dbgTrace (minChatLvl) "reorderLetExprsFunBody (LetE isdef): " dbgTrace (minChatLvl) (sdoc (freeVarsRhs')) dbgTrace (minChatLvl) "End reorderLetExprsFunBody (LetE isdef)\n."
                 else do
                    (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap bod
                    let delayedLetE = LetExpr (v, locs, ty, rhs)
                        delayedExprMap'' = M.insert freeVarsRhs' delayedLetE delayedExprMap'
                    -- (bod', definedVars'', delayedExprMap'') <- foldrM (\(dvars, expr) (body, env, env2) -> do 
                    --                                         let can_release = S.isSubsetOf dvars env 
                    --                                           in if can_release
                    --                                              then do
                    --                                                 case expr of 
                    --                                                     LetExpr (v', locs', ty', rhs') -> do
                    --                                                         let env' = S.insert (fromVarToFreeVarsTy v') env
                    --                                                             new_body = LetE (v', locs', ty', rhs') body
                    --                                                             env2' = M.delete dvars env2
                    --                                                         pure (new_body, env', env2')
                    --                                                     LetLocExpr loc' rhs' -> do
                    --                                                         let env' = S.insert (fromLocVarToFreeVarsTy loc') env
                    --                                                             new_body = Ext $ LetLocE loc' rhs' body
                    --                                                             env2' = M.delete dvars env2
                    --                                                         pure (new_body, env', env2')
                    --                                              else do
                    --                                                 pure (body, env, env2)
                    --                                   ) (bod, definedVars, delayedExprMap') (M.toList delayedExprMap')    
                    -- bod'' <- reorderLetExprsFunBody definedVars'' delayedExprMap'' bod'
                   
                    -- dbgTrace (minChatLvl) "reorderLetExprsFunBody (LetE isndef): " dbgTrace (minChatLvl) (sdoc (delayedLetE, freeVarsRhs', definedVars, delayedExprMap'', bod, bod', bod'')) dbgTrace (minChatLvl) "End reorderLetExprsFunBody (LetE isndef)\n."
                    pure (bod', delayedExprMap'')
        
        LitE _ -> pure (ex, delayedExprMap)
        CharE _ -> pure (ex, delayedExprMap)
        FloatE{} -> pure (ex, delayedExprMap)
        LitSymE _ -> pure (ex, delayedExprMap)
        VarE _ -> pure (ex, delayedExprMap)
        LitSymE _ -> pure (ex, delayedExprMap)

        AppE f lvs ls -> do 
                         results <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
                         let ls' = map fst results
                             delayedExprMap' = M.unions $ map snd results 
                         pure $ (AppE f lvs ls', delayedExprMap') 

        PrimAppE p ls -> do
                         results <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
                         let ls' = map fst results
                             delayedExprMap' = M.unions $ map snd results
                         pure $ (PrimAppE p ls', delayedExprMap')

        MkProdE ls -> do
                      results <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
                      let ls' = map fst results
                          delayedExprMap' = M.unions $ map snd results
                      pure $ (MkProdE ls', delayedExprMap') 
        
        DataConE loc k ls -> do 
                             results <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
                             let ls' = map fst results
                                 delayedExprMap' = M.unions $ map snd results
                             pure $ (DataConE loc k ls', delayedExprMap')
        
        IfE a b c -> do
            (a', enva) <- reorderLetExprsFunBody definedVars delayedExprMap a
            (b', envb) <- reorderLetExprsFunBody definedVars enva b
            (c', envc) <- reorderLetExprsFunBody definedVars envb c
            pure $ (IfE a' b' c', envc) 

        ProjE i e -> do
            (e', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ (ProjE i e', delayedExprMap')

        CaseE e ls -> do 
            (e', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap e
            ls' <- mapM (\(dcon, vs, rhs) -> do
                            let definedVars' = S.union definedVars (S.fromList (map (fromVarToFreeVarsTy . fst) vs))
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocVarToFreeVarsTy . snd) vs))
                            (rhs', env) <- reorderLetExprsFunBody definedVars'' delayedExprMap' rhs
                            pure ((dcon, vs, rhs'), env)
                        ) ls
            let ls'' = map fst ls'
                delayedExprMap'' = M.unions $ map snd ls'
            pure $ (CaseE e' ls'', delayedExprMap'')

        TimeIt e _t b -> do
            (e', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap e
            dbgTrace (minChatLvl) "Print in TimeIt: " dbgTrace (minChatLvl) (sdoc (definedVars, delayedExprMap)) dbgTrace (minChatLvl) "1End TimeIt.\n" pure $ (TimeIt e' _t b, delayedExprMap')

        SpawnE f lvs ls -> do 
            ls' <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
            let ls'' = map fst ls'
                delayedExprMap' = M.unions $ map snd ls'
            pure $ (SpawnE f lvs ls'', delayedExprMap')
        
        SyncE -> pure (SyncE, delayedExprMap)

        WithArenaE v e -> do
            (e', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ (WithArenaE v e', delayedExprMap') 

        MapE _ _ -> error "reorderLetExprsFunBody: MapE not supported!"


        FoldE _ _ _ -> error "reorderLetExprsFunBody: FoldE not supported!"

        WithArenaE v e -> do
            (e', delayedExprMap')  <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ (WithArenaE v e', delayedExprMap')

        Ext (LetLocE loc rhs bod) -> do
            let freeVarsRhs = freeVarsInLocExp rhs
                --freeVarsRhs' = S.map (fromVarToFreeVarsTy) freeVarsRhs
                {- Check if variables in rhs are defined -}
                isDefined = S.isSubsetOf freeVarsRhs definedVars
              in if isDefined
                 then do
                    let definedVars' = S.insert (fromLocVarToFreeVarsTy loc) definedVars
                    -- (bod', definedVars'', delayedExprMap') <- foldrM (\(dvars, expr) (body, env, env2) -> do 
                    --                                                     let can_release = S.isSubsetOf dvars env 
                    --                                                        in if can_release
                    --                                                           then do
                    --                                                             case expr of 
                    --                                                                 LetExpr (v', locs', ty', rhs') -> do
                    --                                                                     let env' = S.insert (fromVarToFreeVarsTy v') env
                    --                                                                         new_body = LetE (v', locs', ty', rhs') body
                    --                                                                         env2' = M.delete dvars env2
                    --                                                                     pure (new_body, env', env2')
                    --                                                                 LetLocExpr loc' rhs' -> do
                    --                                                                     let env' = S.insert (fromLocVarToFreeVarsTy loc') env
                    --                                                                         new_body = Ext $ LetLocE loc' rhs' body
                    --                                                                         env2' = M.delete dvars env2
                    --                                                                     pure (new_body, env', env2')
                    --                                                           else do
                    --                                                             pure (body, env, env2)
                    --                                                  ) (bod, definedVars', delayedExprMap) (M.toList delayedExprMap)
                    -- bod'' <- reorderLetExprsFunBody definedVars'' delayedExprMap' bod'
                    (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars' delayedExprMap bod
                    pure $ (Ext $ LetLocE loc rhs bod', delayedExprMap')
                 else do
                    (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap bod
                    let delayedLetLocE = LetLocExpr loc rhs
                        delayedExprMap'' = M.insert freeVarsRhs delayedLetLocE delayedExprMap'
                    --(bod', definedVars', delayedExprMap'') <- foldrM (\(dvars, expr) (body, env, env2) -> do 
                    --                                                    let can_release = S.isSubsetOf dvars env 
                    --                                                       in if can_release
                    --                                                          then do
                    --                                                            case expr of 
                    --                                                                LetExpr (v', locs', ty', rhs') -> do
                    --                                                                    let env' = S.insert (fromVarToFreeVarsTy v') env
                    --                                                                        new_body = LetE (v', locs', ty', rhs') body
                    --                                                                        env2' = M.delete dvars env2
                    --                                                                    pure (new_body, env', env2')
                    --                                                                LetLocExpr loc' rhs' -> do
                    --                                                                    let env' = S.insert (fromLocVarToFreeVarsTy loc') env
                    --                                                                        new_body = Ext $ LetLocE loc' rhs' body
                    --                                                                        env2' = M.delete dvars env2
                    --                                                                    pure (new_body, env', env2')
                    --                                                          else do
                    --                                                            pure (body, env, env2)
                    --                                                 ) (bod, definedVars, delayedExprMap') (M.toList delayedExprMap')    
                    --bod'' <- reorderLetExprsFunBody definedVars' delayedExprMap'' bod'
                    
                    pure (bod', delayedExprMap'')
                    -- dbgTrace (minChatLvl) "reorderLetExprsFunBody (LetLocE isndef): " dbgTrace (minChatLvl) (sdoc (delayedLetLocE, freeVarsRhs, definedVars, delayedExprMap'', bod, bod', bod'')) dbgTrace (minChatLvl) "End reorderLetExprsFunBody (LetLocE isndef)\n."

        Ext (StartOfPkdCursor cur) -> pure (ex, delayedExprMap)

        Ext (TagCursor a _b) -> pure (ex, delayedExprMap) 

        Ext (FromEndE{}) -> pure (ex, delayedExprMap)

        Ext (AddFixed{}) -> pure (ex, delayedExprMap)

        Ext (RetE _ls v) -> pure (ex, delayedExprMap)

        Ext (BoundsCheck{}) -> pure (ex, delayedExprMap)

        Ext (IndirectionE tycon _ (a, _) _ _) -> pure (ex, delayedExprMap) 

        Ext GetCilkWorkerNum -> pure (ex, delayedExprMap)

        Ext (LetAvail _ bod) -> pure (ex, delayedExprMap)

        Ext (AllocateTagHere{}) -> pure (ex, delayedExprMap)

        Ext (AllocateScalarsHere{}) -> pure (ex, delayedExprMap)

        Ext (SSPush{}) -> pure (ex, delayedExprMap)

        Ext (SSPop{}) -> pure (ex, delayedExprMap)

        Ext (LetRegionE r sz ty bod) -> do
            (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap bod
            pure $ (Ext $ LetRegionE r sz ty bod', delayedExprMap')
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure (ex, delayedExprMap)


{- We also need to release let expressions which are defined -}
releaseExprsFunBody :: DefinedVars -> DelayedExprMap -> Exp2 -> PassM Exp2
releaseExprsFunBody definedVars delayedExprMap ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let definedVars' = S.union (S.insert (fromVarToFreeVarsTy v) definedVars) (S.fromList (map fromLocVarToFreeVarsTy locs))
            (bod', definedVars'', delayedExprMap') <- foldlM (\(body, env, env2) (dvars, expr) -> do 
                                                            let can_release = S.isSubsetOf dvars env 
                                                              in if can_release
                                                                 then do
                                                                    case expr of 
                                                                        LetExpr (v', locs', ty', rhs') -> do
                                                                            let env' = S.insert (fromVarToFreeVarsTy v') env
                                                                                new_body = LetE (v', locs', ty', rhs') body
                                                                                env2' = M.delete dvars env2
                                                                            pure (new_body, env', env2')
                                                                        LetLocExpr loc rhs' -> do
                                                                            let env' = S.insert (fromLocVarToFreeVarsTy loc) env
                                                                                new_body = Ext $ LetLocE loc rhs' body
                                                                                env2' = M.delete dvars env2
                                                                            pure (new_body, env', env2')
                                                                 else do
                                                                    pure (body, env, env2)
                                                               ) (bod, definedVars', delayedExprMap) (M.toList delayedExprMap)
            --let bod' = foldr (\exp -> Ext $ exp ) bod [] 
            bod'' <- releaseExprsFunBody definedVars'' delayedExprMap' bod'
            pure $ LetE (v, locs, ty, rhs) bod''
        
        LitE _ -> pure ex
        CharE _ -> pure ex
        FloatE{} -> pure ex
        LitSymE _ -> pure ex
        VarE v -> pure ex
        LitSymE _ -> pure ex

        AppE f lvs ls -> AppE f lvs <$> mapM (releaseExprsFunBody definedVars delayedExprMap) ls

        PrimAppE p ls -> PrimAppE p <$> mapM (releaseExprsFunBody definedVars delayedExprMap) ls

        MkProdE ls -> MkProdE <$> mapM (releaseExprsFunBody definedVars delayedExprMap) ls 
        
        DataConE loc k ls -> DataConE loc k <$> mapM (releaseExprsFunBody definedVars delayedExprMap) ls
        
        IfE a b c -> do
            a' <- releaseExprsFunBody definedVars delayedExprMap a
            b' <- releaseExprsFunBody definedVars delayedExprMap b
            c' <- releaseExprsFunBody definedVars delayedExprMap c
            pure $ IfE a' b' c' 

        ProjE i e -> do
            e' <- releaseExprsFunBody definedVars delayedExprMap e
            pure $ ProjE i e'

        CaseE e ls -> do 
            e' <- releaseExprsFunBody definedVars delayedExprMap e
            ls' <- mapM (\(dcon, vs, rhs) -> do
                            let definedVars' = S.union definedVars (S.fromList (map (fromVarToFreeVarsTy . fst) vs))
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocVarToFreeVarsTy . snd) vs))
                            rhs' <- releaseExprsFunBody definedVars'' delayedExprMap rhs
                            pure (dcon, vs, rhs')) ls
            pure $ CaseE e' ls'

        TimeIt e _t b -> do
            e' <- dbgTrace (minChatLvl) "Print in TimeIt: " dbgTrace (minChatLvl) (sdoc (definedVars, delayedExprMap)) dbgTrace (minChatLvl) "End TimeIt.\n" releaseExprsFunBody definedVars delayedExprMap e
            pure $ TimeIt e' _t b

        SpawnE f lvs ls -> do 
            ls' <- mapM (releaseExprsFunBody definedVars delayedExprMap) ls
            pure $ SpawnE f lvs ls'
        
        SyncE -> pure SyncE

        WithArenaE v e -> do
            e' <- releaseExprsFunBody definedVars delayedExprMap e
            pure $ WithArenaE v e' 

        MapE _ _ -> error "releaseExprsFunBody: MapE not supported!"


        FoldE _ _ _ -> error "releaseExprsFunBody: FoldE not supported!"

        WithArenaE v e -> do
            e' <- releaseExprsFunBody definedVars delayedExprMap e
            pure $ WithArenaE v e'

        Ext (LetLocE loc rhs bod) -> do
            let definedVars' = dbgTrace (minChatLvl) "Print in LetLocE: " dbgTrace (minChatLvl) (sdoc (loc, definedVars, delayedExprMap)) dbgTrace (minChatLvl) "End print in LetLocE.\n" S.insert (fromLocVarToFreeVarsTy loc) definedVars
            (bod', definedVars'', delayedExprMap') <- foldrM (\(dvars, expr) (body, env, env2) -> do 
                                                            let can_release = S.isSubsetOf dvars env 
                                                              in if can_release
                                                                 then do
                                                                    case expr of 
                                                                        LetExpr (v', locs', ty', rhs') -> do
                                                                            let env' = S.insert (fromVarToFreeVarsTy v') env
                                                                                new_body = LetE (v', locs', ty', rhs') body
                                                                                env2' = M.delete dvars env2
                                                                            pure (new_body, env', env2')
                                                                        LetLocExpr loc' rhs' -> do
                                                                            let env' = S.insert (fromLocVarToFreeVarsTy loc) env
                                                                                new_body = Ext $ LetLocE loc' rhs' body
                                                                                env2' = M.delete dvars env2
                                                                            pure (new_body, env', env2')
                                                                 else do
                                                                    pure (body, env, env2)
                                                        ) (bod, definedVars', delayedExprMap) (M.toList delayedExprMap)
            bod'' <- releaseExprsFunBody definedVars'' delayedExprMap' bod'
            pure $ Ext $ LetLocE loc rhs bod''

        Ext (StartOfPkdCursor cur) -> pure ex

        Ext (TagCursor a _b) -> pure ex 

        Ext (FromEndE{}) -> pure ex

        Ext (AddFixed{}) -> pure ex

        Ext (RetE _ls v) -> pure ex

        Ext (BoundsCheck{}) -> pure ex

        Ext (IndirectionE tycon _ (a, _) _ _) -> pure ex 

        Ext GetCilkWorkerNum -> pure ex

        Ext (LetAvail _ bod) -> pure ex

        Ext (AllocateTagHere{}) -> pure ex

        Ext (AllocateScalarsHere{}) -> pure ex

        Ext (SSPush{}) -> pure ex

        Ext (SSPop{}) -> pure ex

        Ext (LetRegionE r sz ty bod) -> do
            bod' <- releaseExprsFunBody definedVars delayedExprMap bod
            pure $ Ext $ LetRegionE r sz ty bod'
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex


freeVarsInLocExp :: LocExp -> S.Set FreeVarsTy
freeVarsInLocExp expr = case expr of
                    StartOfRegionLE _ -> S.empty
                    AfterConstantLE _ loc -> S.singleton (fromLocVarToFreeVarsTy loc)
                    AfterVariableLE v loc _ -> S.fromList [(fromVarToFreeVarsTy v), (fromLocVarToFreeVarsTy loc)]
                    InRegionLE _ -> S.empty
                    FreeLE -> S.empty
                    FromEndLE loc -> S.singleton (fromLocVarToFreeVarsTy loc)
                    GenSoALoc loc flocs -> let env = S.singleton (fromLocVarToFreeVarsTy loc)
                                               env' = S.fromList $ map (\(_, l) -> fromLocVarToFreeVarsTy l) flocs
                                             in S.union env env'
                    GetDataConLocSoA loc -> S.singleton (fromLocVarToFreeVarsTy loc)
                    GetFieldLocSoA _ loc -> S.singleton (fromLocVarToFreeVarsTy loc)
                    AssignLE loc -> S.singleton (fromLocVarToFreeVarsTy loc)


ensureLocationsAreDefinedForWrite :: S.Set FreeVarsTy -> Exp2 -> PassM Exp2
ensureLocationsAreDefinedForWrite definedVars ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let definedVars' = S.insert (fromVarToFreeVarsTy v) definedVars
            bod' <- ensureLocationsAreDefinedForWrite definedVars' bod
            pure $ LetE (v, locs, ty, rhs) bod'
        LitE _ -> pure ex
        CharE _ -> pure ex
        FloatE{} -> pure ex
        LitSymE _ -> pure ex
        VarE _ -> pure ex
        LitSymE _ -> pure ex
        AppE f lvs ls -> AppE f lvs <$> mapM go ls
        PrimAppE p ls -> PrimAppE p <$> mapM go ls
        MkProdE ls -> MkProdE <$> mapM go ls 
        DataConE loc k ls -> do 
                              case loc of 
                                    Single _ -> return ex
                                    SoA dcloc fieldlocs -> do
                                        if S.member (fromLocVarToFreeVarsTy (singleLocVar dcloc)) definedVars
                                            then do
                                                ls' <- mapM go ls
                                                pure $ DataConE loc k ls'
                                            else do
                                                let definedVars' = S.insert (fromLocVarToFreeVarsTy (singleLocVar dcloc)) definedVars
                                                let letDcon = [LetLocE (singleLocVar dcloc) (GetDataConLocSoA loc)]
                                                let (letFieldLocs, definedVars'') = foldr (\(i, floc) (lets, denv) -> if S.member (fromLocVarToFreeVarsTy floc) definedVars'
                                                                                                    then (lets, denv)
                                                                                                    else 
                                                                                                        let fieldLetE = [LetLocE floc (GetFieldLocSoA i loc)]
                                                                                                            denv' = S.insert (fromLocVarToFreeVarsTy floc) denv
                                                                                                          in (lets ++ fieldLetE, denv') 

                                                                         ) (letDcon, definedVars') fieldlocs
                                                ls' <- mapM (ensureLocationsAreDefinedForWrite definedVars'') ls
                                                let ex' = foldr (\l body -> Ext $ l body) (DataConE loc k ls') letFieldLocs
                                                pure ex'
        
        IfE a b c -> do
            a' <- go a
            b' <- go b
            c' <- go c
            pure $ IfE a' b' c' 

        ProjE i e -> do
            e' <- go e
            pure $ ProjE i e'

        CaseE e ls -> do 
            e' <- go e
            ls' <- mapM (\(dcon, vs, rhs) -> do
                            let definedVars' = S.union definedVars (S.fromList (map (fromVarToFreeVarsTy . fst) vs))
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocVarToFreeVarsTy . snd) vs))
                            rhs' <- ensureLocationsAreDefinedForWrite definedVars'' rhs
                            pure (dcon, vs, rhs')) ls
            pure $ CaseE e' ls'

        TimeIt e _t b -> do
            e' <- go e
            pure $ TimeIt e' _t b

        SpawnE f lvs ls -> do 
            ls' <- mapM go ls
            pure $ SpawnE f lvs ls'
        
        SyncE -> pure SyncE

        WithArenaE v e -> do
            e' <- go e
            pure $ WithArenaE v e' 

        MapE _ _ -> error "releaseExprsFunBody: MapE not supported!"


        FoldE _ _ _ -> error "releaseExprsFunBody: FoldE not supported!"

        WithArenaE v e -> do
            e' <- go e
            pure $ WithArenaE v e'

        Ext (LetLocE loc rhs bod) -> do
            let definedVars' = S.insert (fromLocVarToFreeVarsTy loc) definedVars
            bod' <- ensureLocationsAreDefinedForWrite definedVars' bod
            pure $ Ext $ LetLocE loc rhs bod'

        Ext (StartOfPkdCursor cur) -> pure ex

        Ext (TagCursor a _b) -> pure ex 

        Ext (FromEndE{}) -> pure ex

        Ext (AddFixed{}) -> pure ex

        Ext (RetE _ls v) -> pure ex

        Ext (BoundsCheck{}) -> pure ex

        Ext (IndirectionE tycon _ (a, _) _ _) -> pure ex 

        Ext GetCilkWorkerNum -> pure ex

        Ext (LetAvail _ bod) -> pure ex

        Ext (AllocateTagHere{}) -> pure ex

        Ext (AllocateScalarsHere{}) -> pure ex

        Ext (SSPush{}) -> pure ex

        Ext (SSPop{}) -> pure ex

        Ext (LetRegionE r sz ty bod) -> do
            bod' <- go bod
            pure $ Ext $ LetRegionE r sz ty bod'
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex
    where 
        go = ensureLocationsAreDefinedForWrite definedVars