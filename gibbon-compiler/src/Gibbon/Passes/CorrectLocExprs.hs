module Gibbon.Passes.CorrectLocExprs (delayExpr) where

import qualified Data.List as L
import Data.Maybe ( fromJust )
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Safe as Sf
import Data.Foldable ( foldrM )

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.NewL2.Syntax as NewL2
import Gibbon.L2.Syntax as Old

---------------------------------------------------------------------------
-- Very restrictive, only delays BoundCheck expressions for now. 
-- We would need to extend it with other expressions to make this pass more general.

type BoundEnv = S.Set FreeVarsTy
 
{- VS: We can only delay a bounds check expression, for now -} 
data DelayExpr = BoundsCheckExpr Int LocArg LocArg
    deriving (Eq, Ord)

type DelayExprMap = M.Map DelayExpr (S.Set FreeVarsTy)

mergeDelayExprMaps :: [DelayExprMap] -> DelayExprMap
mergeDelayExprMaps = foldr (M.unionWith S.union) M.empty

delayExpr :: NewL2.Prog2 -> PassM NewL2.Prog2
delayExpr Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (delayExprFun) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> do 
                                 (mn', env) <- delayExpBody M.empty S.empty mn
                                 return $ Just (mn', ty)
  return $ Prog ddefs fundefs' mainExp'


delayExprFun :: NewL2.FunDef2 -> PassM NewL2.FunDef2
delayExprFun f@FunDef{funName,funArgs,funTy,funBody} = do
  let initBoundEnv = S.fromList $ map (\(LRM l _ _) -> fromLocVarToFreeVarsTy l) (locVars funTy)
  (funBody', env) <- delayExpBody M.empty initBoundEnv funBody
  return $ f {funBody = funBody'}

delayExpBody :: DelayExprMap -> BoundEnv -> NewL2.Exp2 -> PassM (NewL2.Exp2, DelayExprMap)
delayExpBody env benv ex = do
  case ex of
    AppE f applocs args -> do 
                           res <- mapM (delayExpBody env benv) args
                           let args' = map fst res
                           let envs = map snd res
                           let env' = mergeDelayExprMaps envs 
                           return (AppE f applocs args', env')
    LetE bnd@(_, _, _, rhs) bod -> do
         case rhs of
           Ext (BoundsCheck sz bound cur) -> do
                           let free_vars_in_bound_expr = S.fromList [fromLocVarToFreeVarsTy $ toLocVar cur]
                           let delayBind = BoundsCheckExpr sz bound cur
                           let env' = M.insert delayBind free_vars_in_bound_expr env
                           (bod', env'') <- delayExpBody env' benv bod
                           return (bod', env'')
           _ -> do
               (rhs', env') <- delayExpBody env benv rhs
               (bod', env'') <- delayExpBody env benv bod
               return (LetE bnd bod', env'')
    LetE (v,locs,ty, rhs) bod -> do 
                                 (rhs', env') <- delayExpBody env benv rhs
                                 (bod', env'') <- delayExpBody env benv bod
                                 return (LetE (v,locs,ty, rhs') bod', env'')
    WithArenaE v e -> do 
                      (e', env') <- delayExpBody env benv e
                      return (WithArenaE v e', env')
    Ext ext ->
      case ext of
        AddFixed{} -> return (ex, env)
        LetLocE loc rhs bod -> do
                               let exprs_to_discharge = concatMap (\(e, vars) -> if S.isSubsetOf vars benv 
                                                                           then [e]
                                                                           else []      
                                                                  ) (M.toList env)
                               let env' = M.filterWithKey (\k vars -> not $ S.isSubsetOf vars benv) env
                               let benv' = S.insert (fromLocVarToFreeVarsTy loc) benv                                    
                               (bod', env'') <- delayExpBody env' benv' bod
                               -- Discharge all the expressions.
                               let bod'' = L.foldr (\e bod -> case e of
                                                               BoundsCheckExpr sz bound cur -> LetE ("_",[],MkTy2 IntTy, (Ext $ BoundsCheck sz bound cur)) bod
                                                               _ -> error "TODO: delayExpBody: unexpected expression\n"
                                                   ) (Ext $ LetLocE loc rhs bod') exprs_to_discharge
                               return (bod'', env'')
        LetRegE reg rhs bod -> do 
                               (bod', env') <- delayExpBody env benv bod
                               return (Ext $ LetRegE reg rhs bod', env')
        RetE locs v -> return (ex, env)
        TagCursor a b -> return (ex, env)
        LetRegionE r sz ty bod -> do 
                                  (bod', env') <- delayExpBody env benv bod
                                  return (Ext $ LetRegionE r sz ty bod', env')
        LetParRegionE r sz ty bod -> do 
                                      (bod', env') <- delayExpBody env benv bod
                                      return (Ext $ LetParRegionE r sz ty bod', env')
        FromEndE{}    -> return (ex, env)
        BoundsCheck sz _bound cur -> return (ex, env)
        IndirectionE{}   -> return (ex, env)
        GetCilkWorkerNum -> return (ex, env)
        LetAvail vs bod -> do 
                            (bod', env') <- delayExpBody env benv bod
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
                  (e', env') <- delayExpBody env benv e
                  return (ProjE i e', env')
    IfE a b c  -> do 
                  (a', env') <- delayExpBody env benv a
                  (b', env'') <- delayExpBody env benv b
                  (c', env''') <- delayExpBody env benv c
                  return (IfE a' b' c', env''')
    MkProdE ls -> do 
                  res <- mapM (delayExpBody env benv) ls
                  let ls' = map fst res
                  let env' = mergeDelayExprMaps $ map snd res
                  return (MkProdE ls', env')
    CaseE scrt mp -> do 
                     res <- mapM (\(c,args,ae) -> do 
                                     (ae', env') <- delayExpBody env benv ae
                                     return ((c,args,ae'), env')) mp
                     let mp' = map fst res
                     let env' = mergeDelayExprMaps $ map snd res
                     return (CaseE scrt mp', env')
    TimeIt e ty b -> do 
                     (e', env') <- delayExpBody env benv e
                     return (TimeIt e' ty b, env')
    SpawnE{} -> error "threadRegionsExp: Unbound SpawnE"
    SyncE    -> pure (ex, env)
    MapE{}  -> error $ "threadRegionsExp: TODO MapE"
    FoldE{} -> error $ "threadRegionsExp: TODO FoldE"