module Gibbon.Passes.HoistExpressions (hoistBoundsCheckProg) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable ( foldrM, foldlM)

import Gibbon.Common
import Gibbon.NewL2.Syntax as NewL2

---------------------------------------------------------------------------
-- Hoist the bounds check expression to the top of each function

-- | Map to store variables in scope
type BoundEnv = S.Set FreeVarsTy

-- | The type of expressions that can be hoisted to the top
data HoistableExpr =   BoundsCheckExpr Int LocArg LocArg 
                     | BoundsCheckVectorExpr [(Int, LocArg, LocArg)] 
                     | LetLocExpr LocVar (PreLocExp LocArg) 
                     | LetRegExpr RegVar (PreRegExp LocArg)
    deriving (Eq, Ord)

-- | Stores all the expressions that can be hoisted to the top of the function
type HoistAbleExprMap = M.Map HoistableExpr (S.Set FreeVarsTy)

mergeHoistExprMaps :: [HoistAbleExprMap] -> HoistAbleExprMap
mergeHoistExprMaps = foldr (M.unionWith S.union) M.empty

collectBoundsCheckExprs :: HoistAbleExprMap -> BoundEnv -> NewL2.Exp2 -> PassM (NewL2.Exp2, HoistAbleExprMap)
collectBoundsCheckExprs env benv ex = do
  case ex of
    AppE f applocs args -> do 
                           res <- mapM (collectBoundsCheckExprs env benv) args
                           let args' = map fst res
                           let envs = map snd res
                           let env' = mergeHoistExprMaps envs 
                           return (AppE f applocs args', env')
    LetE bnd@(v, locs, ty, rhs) bod -> do
         case rhs of
           Ext (BoundsCheck sz bound cur) -> do
                           let free_vars_in_bound_expr = S.fromList [fromLocVarToFreeVarsTy $ toLocVar cur, fromLocArgToFreeVarsTy bound]
                           if (S.isSubsetOf free_vars_in_bound_expr benv)
                           then do
                            (bod', env') <- collectBoundsCheckExprs env benv bod
                            return (LetE bnd bod', env')
                           else do 
                            let delayBind = BoundsCheckExpr sz bound cur
                            let env' = M.insert delayBind free_vars_in_bound_expr env
                            (bod', env'') <- collectBoundsCheckExprs env' benv bod
                            return (bod', env'')
           Ext (BoundsCheckVector bounds) -> do
                           let free_vars_in_bound_expr = S.fromList $ concatMap (\(_, bound, cur) -> [fromLocArgToFreeVarsTy bound, fromLocVarToFreeVarsTy $ toLocVar cur]) bounds
                           if (S.isSubsetOf free_vars_in_bound_expr benv)
                            then do
                              (bod', env') <- collectBoundsCheckExprs env benv bod
                              return (LetE bnd bod', env')
                            else do
                              let delayBind = BoundsCheckVectorExpr bounds
                              let env' = M.insert delayBind free_vars_in_bound_expr env 
                              (bod', env'') <- collectBoundsCheckExprs env' benv bod
                              return (bod', env'') 
           _ -> do
               (rhs', env') <- collectBoundsCheckExprs env benv rhs
               (bod', env'') <- collectBoundsCheckExprs env' benv bod
               return (LetE (v, locs, ty, rhs') bod', env'')

    WithArenaE v e -> do 
                      (e', env') <- collectBoundsCheckExprs env benv e
                      return (WithArenaE v e', env')
    Ext ext ->
      case ext of
        AddFixed{} -> return (ex, env)
        LetLocE loc rhs bod -> do 
                               (bod', env') <- collectBoundsCheckExprs env benv bod
                               return (Ext $ LetLocE loc rhs bod', env')
        LetRegE reg rhs bod -> do 
                               (bod', env') <- collectBoundsCheckExprs env benv bod
                               return (Ext $ LetRegE reg rhs bod', env')
        RetE{} -> return (ex, env)
        TagCursor{} -> return (ex, env)
        LetRegionE r sz ty bod -> do 
                                  (bod', env') <- collectBoundsCheckExprs env benv bod
                                  return (Ext $ LetRegionE r sz ty bod', env')
        LetParRegionE r sz ty bod -> do 
                                      (bod', env') <- collectBoundsCheckExprs env benv bod
                                      return (Ext $ LetParRegionE r sz ty bod', env')
        FromEndE{}    -> return (ex, env)
        BoundsCheck{} -> return (ex, env)
        IndirectionE{}   -> return (ex, env)
        GetCilkWorkerNum -> return (ex, env)
        LetAvail vs bod -> do 
                            (bod', env') <- collectBoundsCheckExprs env benv bod
                            return (Ext $ LetAvail vs bod', env')
        AllocateTagHere{} -> return (ex, env)
        AllocateScalarsHere{} -> pure (ex, env)
        SSPush{} -> pure (ex, env)
        SSPop{} -> pure (ex, env)
        _ -> pure (ex, env)

    -- Straightforward recursion
    VarE{}     -> return (ex, env)
    LitE{}     -> return (ex, env)
    CharE{}    -> return (ex, env)
    FloatE{}   -> return (ex, env)
    LitSymE{}  -> return (ex, env)
    PrimAppE{} -> return (ex, env)
    DataConE{} -> return (ex, env)
    ProjE i e  -> do 
                  (e', env') <- collectBoundsCheckExprs env benv e
                  return (ProjE i e', env')
    IfE a b c  -> do 
                  (a', env') <- collectBoundsCheckExprs env benv a
                  (b', env'') <- collectBoundsCheckExprs env benv b
                  (c', env''') <- collectBoundsCheckExprs env benv c
                  let env'''' = mergeHoistExprMaps [env', env'', env''']
                  return (IfE a' b' c', env'''')
    MkProdE ls -> do 
                  res <- mapM (collectBoundsCheckExprs env benv) ls
                  let ls' = map fst res
                  let env' = mergeHoistExprMaps $ map snd res
                  return (MkProdE ls', env')
    CaseE scrt mp -> do 
                     res <- mapM (\(c,args,ae) -> do 
                                     (ae', env') <- collectBoundsCheckExprs env benv ae
                                     return ((c,args,ae'), env')) mp
                     let mp' = map fst res
                     let env' = mergeHoistExprMaps $ map snd res
                     return (CaseE scrt mp', env')
    TimeIt e ty b -> do 
                     (e', env') <- collectBoundsCheckExprs env benv e
                     return (TimeIt e' ty b, env')
    SpawnE{} -> error "threadRegionsExp: Unbound SpawnE"
    SyncE    -> pure (ex, env)
    MapE{}  -> error $ "threadRegionsExp: TODO MapE"
    FoldE{} -> error $ "threadRegionsExp: TODO FoldE"


collectVarsForBoundsCheck :: FreeVarsTy -> HoistAbleExprMap -> NewL2.Exp2 -> PassM (NewL2.Exp2, HoistAbleExprMap)
collectVarsForBoundsCheck vars env ex = do
  case ex of
    AppE f applocs args -> do 
                           res <- mapM (collectVarsForBoundsCheck vars env) args
                           let args' = map fst res
                           let envs = map snd res
                           let env' = mergeHoistExprMaps envs 
                           return (AppE f applocs args', env')
    LetE (v, locs, ty, rhs) bod -> do
         case rhs of
           _ -> do
               (rhs', env') <- collectVarsForBoundsCheck vars env rhs
               (bod', env'') <- collectVarsForBoundsCheck vars env' bod
               return (LetE (v, locs, ty, rhs') bod', env'')
    WithArenaE v e -> do 
                      (e', env') <- collectVarsForBoundsCheck vars env e
                      return (WithArenaE v e', env')
    Ext ext ->
      case ext of
        AddFixed{} -> return (ex, env)
        LetLocE loc rhs bod -> do
                                if fromLocVarToFreeVarsTy loc == vars 
                                then do
                                  let delayLetBind = LetLocExpr loc rhs
                                      dependentVars = freeVarsInLocExp rhs 
                                      env' = M.insert delayLetBind dependentVars env
                                  (bod', env'') <- collectVarsForBoundsCheck vars env' bod
                                  return (bod', env'')
                                else do
                                  (bod', env') <- collectVarsForBoundsCheck vars env bod
                                  return (Ext $ LetLocE loc rhs bod', env')

        LetRegE reg rhs bod -> do 
                               if fromRegVarToFreeVarsTy reg == vars 
                               then do 
                                 let delayLetBind = LetRegExpr reg rhs
                                     dependentVars = S.empty
                                     env' = M.insert delayLetBind dependentVars env
                                 (bod', env'') <- collectVarsForBoundsCheck vars env' bod
                                 return (bod', env'')
                                 else 
                                   do
                                    (bod', env') <- collectVarsForBoundsCheck vars env bod
                                    return (Ext $ LetRegE reg rhs bod', env')
        RetE{} -> return (ex, env)
        TagCursor{} -> return (ex, env)
        LetRegionE r sz ty bod -> do 
                                  (bod', env') <- collectVarsForBoundsCheck vars env bod
                                  return (Ext $ LetRegionE r sz ty bod', env')
        LetParRegionE r sz ty bod -> do 
                                      (bod', env') <- collectVarsForBoundsCheck vars env bod
                                      return (Ext $ LetParRegionE r sz ty bod', env')
        FromEndE{}    -> return (ex, env)
        BoundsCheck{} -> return (ex, env)
        IndirectionE{}   -> return (ex, env)
        GetCilkWorkerNum -> return (ex, env)
        LetAvail vs bod -> do 
                            (bod', env') <- collectVarsForBoundsCheck vars env bod
                            return (Ext $ LetAvail vs bod', env')
        AllocateTagHere{} -> return (ex, env)
        AllocateScalarsHere{} -> pure (ex, env)
        SSPush{} -> pure (ex, env)
        SSPop{} -> pure (ex, env)
        _ -> pure (ex, env)

    -- Straightforward recursion
    VarE{}     -> return (ex, env)
    LitE{}     -> return (ex, env)
    CharE{}    -> return (ex, env)
    FloatE{}   -> return (ex, env)
    LitSymE{}  -> return (ex, env)
    PrimAppE{} -> return (ex, env)
    DataConE{} -> return (ex, env)
    ProjE i e  -> do 
                  (e', env') <- collectVarsForBoundsCheck vars env e
                  return (ProjE i e', env')
    IfE a b c  -> do 
                  (a', env') <- collectVarsForBoundsCheck vars env a
                  (b', env'') <- collectVarsForBoundsCheck vars env b
                  (c', env''') <- collectVarsForBoundsCheck vars env c
                  let env'''' = mergeHoistExprMaps [env', env'', env''']
                  return (IfE a' b' c', env'''')
    MkProdE ls -> do 
                  res <- mapM (collectVarsForBoundsCheck vars env) ls
                  let ls' = map fst res
                  let env' = mergeHoistExprMaps $ map snd res
                  return (MkProdE ls', env')
    CaseE scrt mp -> do 
                     res <- mapM (\(c,args,ae) -> do 
                                     (ae', env') <- collectVarsForBoundsCheck vars env ae
                                     return ((c,args,ae'), env')) mp
                     let mp' = map fst res
                     let env' = mergeHoistExprMaps $ map snd res
                     return (CaseE scrt mp', env')
    TimeIt e ty b -> do 
                     (e', env') <- collectVarsForBoundsCheck vars env e
                     return (TimeIt e' ty b, env')
    SyncE    -> pure (ex, env)                 
    SpawnE{} -> error "threadRegionsExp: Unbound SpawnE"
    MapE{}  -> error $ "threadRegionsExp: TODO MapE"
    FoldE{} -> error $ "threadRegionsExp: TODO FoldE"


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


hoistBoundsCheckProg :: NewL2.Prog2 -> PassM NewL2.Prog2
hoistBoundsCheckProg Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (hoistBoundsCheckFun) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> do 
                                 mn' <- hoistBoundsCheck mn S.empty
                                 return $ Just (mn', ty)
  return $ Prog ddefs fundefs' mainExp'


hoistBoundsCheckFun :: NewL2.FunDef2 -> PassM NewL2.FunDef2
hoistBoundsCheckFun f@FunDef{funTy,funBody} = do
  let initBoundEnv = S.fromList $ map (\(LRM l _ _) -> fromLocVarToFreeVarsTy l) (locVars funTy)
  funBody' <- hoistBoundsCheck funBody initBoundEnv
  return $ f {funBody = funBody'}


hoistBoundsCheckHelper :: HoistAbleExprMap -> NewL2.Exp2 -> PassM NewL2.Exp2 
hoistBoundsCheckHelper env l2exp = do
                                    let boundCheckExprs = M.toList env
                                    exp' <- foldrM (\(boundsCheck, dependentVars) expr -> do 
                                                  --recursively release all dependent vars
                                                  (expr', lets) <- foldrM (\var (exp'', letenv) -> do
                                                                                            (exp''', lets) <- collectVarsForBoundsCheck var M.empty exp''
                                                                                            let letenv' = M.union letenv lets
                                                                                            pure (exp''', letenv')
                                                                          ) (expr, M.empty) (S.toList dependentVars)
                                                  let expr'' = case boundsCheck of 
                                                                          BoundsCheckExpr i bound cur -> LetE ("_",[],MkTy2 IntTy, (Ext $ BoundsCheck i bound cur)) expr'
                                                                          BoundsCheckVectorExpr bounds -> LetE ("_",[],MkTy2 IntTy, (Ext $ BoundsCheckVector bounds)) expr'
                                                                          LetLocExpr l rhs -> Ext $ LetLocE l rhs expr'
                                                                          LetRegExpr r rhs -> Ext $ LetRegE r rhs expr'
                                                  -- release all lets 
                                                  -- call function recursively
                                                  expr''' <- hoistBoundsCheckHelper lets expr''
                                                  pure expr'''
                                         ) l2exp boundCheckExprs
                                    pure exp'


hoistBoundsCheck :: NewL2.Exp2 -> BoundEnv -> PassM NewL2.Exp2 
hoistBoundsCheck inexp benv = do 
                            (exp', m) <- collectBoundsCheckExprs M.empty benv inexp
                            exp'' <- hoistBoundsCheckHelper m exp'
                            pure exp''