module Gibbon.Passes.ReorderLetExprNewL2 (reorderLetExprsL2) where

import qualified Data.List as L 
import qualified Data.Set as S

import qualified Data.Map as M

import Data.Foldable as F
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.NewL2.Syntax
import Data.Maybe ()
import qualified Data.Maybe as S

data DelayedExpr = LetExpr (Var, [LocArg], Ty2, Exp2)
                 | LetLocExpr LocVar LocExp 
                    deriving (Eq, Ord, Show, Generic)


instance Out DelayedExpr

type DefinedVars = S.Set FreeVarsTy
type DelayedExprMap = M.Map (Var, DefinedVars) DelayedExpr

reorderLetExprsL2 :: Prog2 -> PassM Prog2
reorderLetExprsL2 (Prog ddefs fundefs mainExp) = do
    fds' <- mapM reorderLetExprsFun (M.elems fundefs)
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
                    Just (e,ty) -> do
                                      (e', env) <- reorderLetExprsFunBody S.empty M.empty e
                                      e'' <- releaseExprsFunBody S.empty env e'
                                      e''' <- removeDuplicateLocations S.empty e''
                                      pure $ Just (e''', ty)
                    Nothing     -> pure Nothing
    pure $ Prog ddefs fundefs' mainExp'

reorderLetExprsFun :: FunDef2 -> PassM FunDef2
reorderLetExprsFun f@FunDef{funName,funTy,funArgs,funBody,funMeta} = do
    let args = S.fromList $ map (fromVarToFreeVarsTy) funArgs
    {- Add location variables to defined environment from funTy -}
        inLocs = allLocVars funTy
        --outLoc = outLocVars funTy
        inRegs = allRegVars funTy
        endRegs = map toEndVRegVar inRegs 
        --outRegs = outRegVars funTy
        locToFreeVarsTy = S.fromList $ map fromLocVarToFreeVarsTy (inLocs)
        regToFreeVarsTy = S.fromList $ map fromRegVarToFreeVarsTy (inRegs)
        endRegToFreeVarsTy = S.fromList $ map fromRegVarToFreeVarsTy (endRegs)
        definedVars = S.unions [args, locToFreeVarsTy, regToFreeVarsTy, endRegToFreeVarsTy]
    (funBody', env') <- reorderLetExprsFunBody definedVars M.empty funBody
    funBody'' <- releaseExprsFunBody definedVars env' funBody'
    -- dbgTrace (minChatLvl) "Print Meta: " dbgTrace (minChatLvl) (sdoc (funTy, funMeta)) dbgTrace (minChatLvl) "Print end.\n"
    funBody''' <- ensureLocationsAreDefinedForWrite S.empty funBody''
    funBody'''' <- removeDuplicateLocations S.empty funBody'''
    dbgTrace (minChatLvl) "Print Env: " dbgTrace (minChatLvl) (sdoc (definedVars, env', funBody''')) dbgTrace (minChatLvl) ("End Print Env.\n") pure $ f { funBody = funBody'''' } --funBody'''


{- We also need to release let expressions which are defined -}
reorderLetExprsFunBody :: DefinedVars -> DelayedExprMap -> Exp2 -> PassM (Exp2, DelayedExprMap)
reorderLetExprsFunBody definedVars delayedExprMap ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let freeVarsRhs = case rhs of 
                                   TimeIt _ _ _ -> S.empty {-VS: For now leaving TimeIt as is. TODO: Implement. -}
                                   AppE _ _ _ -> dbgTraceIt "Print stuff: " dbgTraceIt (sdoc (v, definedVars, allFreeVars' rhs)) dbgTraceIt "End reorder 5!\n" allFreeVars' rhs
                                   DataConE loc _ args -> 
                                       let extractVars argvar = case argvar of
                                               VarE v' -> [fromVarToFreeVarsTy v']
                                               _ -> []
                                       in S.union (S.singleton (fromLocArgToFreeVarsTy loc)) (S.fromList $ concatMap extractVars args)
                                   _ -> S.empty
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
                    key_str <- gensym ""
                    let delayedLetE = LetExpr (v, locs, ty, rhs)
                        delayedExprMap'' = M.insert (key_str, freeVarsRhs') delayedLetE delayedExprMap'
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
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocArgToFreeVarsTy . snd) vs))
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
                    key_str <- gensym ""
                    let delayedLetLocE = LetLocExpr loc rhs
                        delayedExprMap'' = M.insert (key_str, freeVarsRhs) delayedLetLocE delayedExprMap'
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

        Ext (LetRegE r rhs bod) -> do
            (bod', delayedExprMap') <- reorderLetExprsFunBody definedVars delayedExprMap bod
            pure $ (Ext $ LetRegE r rhs bod', delayedExprMap')
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure (ex, delayedExprMap)


{- We also need to release let expressions which are defined -}
releaseExprsFunBody :: DefinedVars -> DelayedExprMap -> Exp2 -> PassM Exp2
releaseExprsFunBody definedVars delayedExprMap ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let definedVars' = S.union (S.insert (fromVarToFreeVarsTy v) definedVars) (S.fromList (map fromLocArgToFreeVarsTy locs))
            (definedVars'', delayedExprMap', letsToRel) <- foldlM (\(env, env2, eprs) ((kid, dvars), expr) -> do 
                                                            let can_release = S.isSubsetOf dvars env 
                                                              in if can_release
                                                                 then do
                                                                    case expr of 
                                                                        LetExpr (v', locs', ty', rhs') -> do
                                                                            let env' = S.insert (fromVarToFreeVarsTy v') env
                                                                                new_body = LetE (v', locs', ty', rhs') (VarE v')
                                                                                env2' = M.delete (kid, dvars) env2
                                                                            pure (env', env2', eprs ++ [new_body])
                                                                        LetLocExpr loc rhs' -> do
                                                                            let env' = S.insert (fromLocVarToFreeVarsTy loc) env
                                                                                new_body = Ext $ LetLocE loc rhs' (VarE "")
                                                                                env2' = M.delete (kid, dvars) env2
                                                                            pure (env', env2', eprs ++ [new_body])
                                                                 else do
                                                                    pure (env, env2, eprs)
                                                               ) (definedVars', delayedExprMap, []) (M.toList delayedExprMap)
            let bod' = foldr (\expr b -> case expr of 
                                            LetE (_v, _locs, _ty, _rhs) _ ->  LetE (_v, _locs, _ty, _rhs) b
                                            Ext (LetLocE _loc _rhs _) ->  Ext $ LetLocE _loc _rhs b
                
                             ) bod letsToRel  
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
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocArgToFreeVarsTy . snd) vs))
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
            -- (definedVars'', delayedExprMap', letsToRel) <- foldlM (\(env, env2, eprs) ((kid, dvars), expr)  -> do 
            --                                                 let can_release = S.isSubsetOf dvars env 
            --                                                   in if can_release
            --                                                      then do
            --                                                         case expr of 
            --                                                             LetExpr (v', locs', ty', rhs') -> do
            --                                                                 let env' = S.insert (fromVarToFreeVarsTy v') env
            --                                                                     new_body = LetE (v', locs', ty', rhs') (VarE v')
            --                                                                     env2' = M.delete (kid, dvars) env2
            --                                                                 pure (env', env2', eprs ++ [new_body])
            --                                                             LetLocExpr loc' rhs' -> do
            --                                                                 let env' = S.insert (fromLocVarToFreeVarsTy loc') env
            --                                                                     new_body = Ext $ LetLocE loc' rhs' (VarE "")
            --                                                                     env2' = M.delete (kid, dvars) env2
            --                                                                 pure (env', env2', eprs ++ [new_body])
            --                                                      else do
            --                                                         pure (env, env2, eprs)
            --                                             ) (definedVars', delayedExprMap, []) (M.toList delayedExprMap)
            (definedVars'', delayedExprMap', letsToRel) <- releaseAllLetLocE definedVars' delayedExprMap []
            let bod' = foldr (\expr b -> case expr of 
                                            LetE (_v, _locs, _ty, _rhs) _ ->  LetE (_v, _locs, _ty, _rhs) b
                                            Ext (LetLocE _loc _rhs _) ->  Ext $ LetLocE _loc _rhs b
                
                             ) bod letsToRel  
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

        Ext (LetRegE r rhs bod) -> do
            bod' <- releaseExprsFunBody definedVars delayedExprMap bod
            pure $ Ext $ LetRegE r rhs bod'
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex
        where
            releaseAllLetLocE :: DefinedVars -> DelayedExprMap -> [Exp2] -> PassM (DefinedVars, DelayedExprMap, [Exp2])
            releaseAllLetLocE envDefinedVars envDelayedExprMap letsToBeReleased = do
                case (M.toList envDelayedExprMap) of 
                       [] -> pure (envDefinedVars, envDelayedExprMap, letsToBeReleased) 
                       _ -> do  
                            (definedVars'', delayedExprMap', letsToRel) <- foldlM (\(env, env2, eprs) ((kid, dvars), expr)  -> do 
                                                            let can_release = S.isSubsetOf dvars env 
                                                              in if can_release
                                                                 then do
                                                                    case expr of 
                                                                        LetExpr (v', locs', ty', rhs') -> do
                                                                            let env' = S.insert (fromVarToFreeVarsTy v') env
                                                                                new_body = LetE (v', locs', ty', rhs') (VarE v')
                                                                                env2' = M.delete (kid, dvars) env2
                                                                            pure (env', env2', eprs ++ [new_body])
                                                                        LetLocExpr loc' rhs' -> do
                                                                            let env' = S.insert (fromLocVarToFreeVarsTy loc') env
                                                                                new_body = Ext $ LetLocE loc' rhs' (VarE "")
                                                                                env2' = M.delete (kid, dvars) env2
                                                                            pure (env', env2', eprs ++ [new_body])
                                                                 else do
                                                                    pure (env, env2, eprs)
                                                        ) (envDefinedVars, envDelayedExprMap, letsToBeReleased) (M.toList envDelayedExprMap)
                            case (delayedExprMap' == envDelayedExprMap) of
                                True -> pure (definedVars'', delayedExprMap', letsToRel)
                                False -> do 
                                         (definedVars''', delayedExprMap'', letsToRel') <- releaseAllLetLocE definedVars'' delayedExprMap' letsToRel 
                                         pure (definedVars''', delayedExprMap'', letsToRel') 


freeVarsInLocExp :: LocExp -> S.Set FreeVarsTy
freeVarsInLocExp expr = case expr of
                    StartOfRegionLE _ -> S.empty
                    AfterConstantLE _ loc -> S.singleton (fromLocArgToFreeVarsTy loc)
                    AfterVariableLE v loc _ -> S.fromList [(fromVarToFreeVarsTy v), (fromLocArgToFreeVarsTy loc)]
                    InRegionLE _ -> S.empty
                    FreeLE -> S.empty
                    FromEndLE loc -> S.singleton (fromLocArgToFreeVarsTy loc)
                    GenSoALoc loc flocs -> let env = S.singleton (fromLocArgToFreeVarsTy loc)
                                               env' = S.fromList $ map (\(_, l) -> fromLocArgToFreeVarsTy l) flocs
                                             in S.union env env'
                    GetDataConLocSoA loc -> S.singleton (fromLocArgToFreeVarsTy loc)
                    GetFieldLocSoA _ loc -> S.singleton (fromLocArgToFreeVarsTy loc)
                    AssignLE loc -> S.singleton (fromLocArgToFreeVarsTy loc)


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
                              case (toLocVar loc) of 
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
                            let definedVars'' = S.union definedVars' (S.fromList (map (fromLocArgToFreeVarsTy . snd) vs))
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

        Ext (LetRegE r rhs bod) -> do
            bod' <- go bod
            pure $ Ext $ LetRegE r rhs bod'
        
        
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex
    where 
        go = ensureLocationsAreDefinedForWrite definedVars



removeDuplicateLocations :: S.Set FreeVarsTy -> Exp2 -> PassM Exp2 
removeDuplicateLocations definedLocs ex = case ex of
        LetE (v,locs,ty,rhs) bod -> do
            rhs' <- removeDuplicateLocations definedLocs rhs
            bod' <- removeDuplicateLocations definedLocs bod
            pure $ LetE (v, locs, ty, rhs') bod'
        LitE _ -> pure ex
        CharE _ -> pure ex
        FloatE{} -> pure ex
        LitSymE _ -> pure ex
        VarE _ -> pure ex
        LitSymE _ -> pure ex
        AppE f lvs ls -> AppE f lvs <$> mapM go ls
        PrimAppE p ls -> PrimAppE p <$> mapM go ls
        MkProdE ls -> MkProdE <$> mapM go ls 
        DataConE loc k ls -> DataConE loc k <$> mapM go ls
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
                            rhs' <- removeDuplicateLocations definedLocs rhs
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

        Ext (LetLocE loc rhs bod) -> do
            let alreadyExists = S.member (fromLocVarToFreeVarsTy loc) definedLocs
            let definedLocs' = if alreadyExists
                               then definedLocs
                               else S.insert (fromLocVarToFreeVarsTy loc) definedLocs
            bod' <- removeDuplicateLocations definedLocs' bod
            if alreadyExists
               then pure bod'
               else pure $ Ext $ LetLocE loc rhs bod'

        Ext (StartOfPkdCursor cur) -> pure ex

        Ext (TagCursor a _b) -> pure ex 

        Ext (FromEndE{}) -> pure ex

        Ext (AddFixed{}) -> pure ex

        Ext (RetE _ls v) -> pure ex

        Ext (BoundsCheck{}) -> pure ex

        Ext (BoundsCheckVector{}) -> pure ex

        Ext (IndirectionE tycon _ (a, _) _ _) -> pure ex 

        Ext GetCilkWorkerNum -> pure ex

        Ext (LetAvail _ bod) -> pure ex

        Ext (AllocateTagHere{}) -> pure ex

        Ext (AllocateScalarsHere{}) -> pure ex

        Ext (SSPush{}) -> pure ex

        Ext (SSPop{}) -> pure ex

        Ext (LetRegionE r sz ty bod) -> do
            let doesRegionExist = S.member (fromRegVarToFreeVarsTy (regionToVar r)) definedLocs
            let definedLocs' = if doesRegionExist 
                               then definedLocs
                               else S.insert (fromRegVarToFreeVarsTy (regionToVar r)) definedLocs
            bod' <- removeDuplicateLocations definedLocs' bod
            if doesRegionExist
            then pure bod'
            else pure $ Ext $ LetRegionE r sz ty bod'

        Ext (LetRegE r rhs bod) -> do
            let doesRegionExist = S.member (fromRegVarToFreeVarsTy (r)) definedLocs
            let definedLocs' = if doesRegionExist 
                               then definedLocs
                               else S.insert (fromRegVarToFreeVarsTy (r)) definedLocs
            bod' <- removeDuplicateLocations definedLocs' bod
            if doesRegionExist
            then pure bod'
            else pure $ Ext $ LetRegE r rhs bod'
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex
    where 
        go = removeDuplicateLocations definedLocs




fromLocArgToFreeVarsTy' :: LocArg -> Maybe FreeVarsTy
fromLocArgToFreeVarsTy' arg =
  case arg of
    Loc lrm        -> Just $ fromLocVarToFreeVarsTy $ lremLoc lrm
    EndWitness _ v -> Nothing
    Reg v _        -> Just $ fromRegVarToFreeVarsTy v
    EndOfReg _ _ v -> Nothing -- Just $ fromRegVarToFreeVarsTy v
    EndOfReg_Tagged v -> Nothing
    _ -> error "NewL2/Syntax.hs, toLocVar: unexpected case."


-- gFreeVars ++ locations ++ region variables
allFreeVars' :: Exp2 -> S.Set FreeVarsTy
allFreeVars' ex =
  case ex of
    AppE _ locs args -> S.fromList (S.catMaybes $ map (fromLocArgToFreeVarsTy') locs) `S.union` (S.unions (map allFreeVars' args))
    PrimAppE _ args -> (S.unions (map allFreeVars' args))
    LetE (v,locs,_,rhs) bod -> (S.fromList (S.catMaybes $ map (fromLocArgToFreeVarsTy') locs) `S.union` (allFreeVars' rhs) `S.union` (allFreeVars' bod))
                               `S.difference` S.singleton (fromVarToFreeVarsTy v)
    IfE a b c -> allFreeVars' a `S.union` allFreeVars' b `S.union` allFreeVars' c
    MkProdE args -> (S.unions (map allFreeVars' args))
    ProjE _ bod -> allFreeVars' bod
    CaseE scrt brs -> (allFreeVars' scrt) `S.union` (S.unions (map (\(_,vlocs,c) -> allFreeVars' c `S.difference`
                                                                                   S.fromList (map (fromVarToFreeVarsTy . fst) vlocs) `S.difference`
                                                                                   S.fromList (S.catMaybes $ map (fromLocArgToFreeVarsTy' . snd) vlocs))
                                                                  brs))
    DataConE loc _ args -> case (fromLocArgToFreeVarsTy' loc) of 
                                        Just arg -> S.singleton arg `S.union` (S.unions (map allFreeVars' args))
                                        Nothing -> S.empty
    TimeIt e _ _ -> allFreeVars' e
    WithArenaE _ e -> allFreeVars' e
    SpawnE _ locs args -> S.fromList (S.catMaybes $  map fromLocArgToFreeVarsTy' locs) `S.union` (S.unions (map allFreeVars' args))
    Ext ext ->
      case ext of
        LetRegionE r _ _ bod -> S.delete ((fromRegVarToFreeVarsTy . regionToVar) r) (allFreeVars' bod)
        LetParRegionE r _ _ bod -> S.delete ((fromRegVarToFreeVarsTy . regionToVar) r) (allFreeVars' bod)
        LetLocE loc locexp bod -> S.difference ((S.singleton . fromLocVarToFreeVarsTy) loc) (allFreeVars' bod `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars locexp))
        StartOfPkdCursor v -> S.singleton (fromVarToFreeVarsTy v)
        TagCursor a b-> S.fromList [(fromVarToFreeVarsTy a),(fromVarToFreeVarsTy b)]
        RetE locs v     -> S.insert (fromVarToFreeVarsTy v) (S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs))
        FromEndE loc    -> S.singleton ((fromLocVarToFreeVarsTy . toLocVar) loc)
        BoundsCheck _ reg cur -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) [reg, cur])
        IndirectionE _ _ (a,b) (c,d) _ -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) [a, b, c, d])
        AddFixed v _    -> S.singleton (fromVarToFreeVarsTy v)
        GetCilkWorkerNum-> S.empty
        LetAvail vs bod -> S.fromList (L.map fromVarToFreeVarsTy vs) `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars bod)
        AllocateTagHere loc _ -> S.singleton $ fromLocVarToFreeVarsTy loc
        AllocateScalarsHere loc -> S.singleton $ fromLocVarToFreeVarsTy loc
        SSPush _ a b _ -> S.fromList (map fromLocVarToFreeVarsTy [a,b])
        SSPop _ a b -> S.fromList (map fromLocVarToFreeVarsTy [a,b])
    _ -> (S.map fromVarToFreeVarsTy $ gFreeVars ex)