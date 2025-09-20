module Gibbon.Passes.HoistBoundsCheck (hoistBoundsCheckProg, hoistBoundsCheck) where

import Data.Foldable (foldlM)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Gibbon.Common
import Gibbon.NewL2.Syntax as NewL2

---------------------------------------------------------------------------
-- Hoist the bounds check expression to the top of each function

-- | Map to store variables in scope
type BoundEnv = S.Set FreeVarsTy

-- | The type of expressions that can be hoisted to the top
data HoistableExpr
  = BoundsCheckExpr Int LocArg LocArg
  | BoundsCheckVectorExpr [(Int, LocArg, LocArg)]
  | LetLocExpr LocVar (PreLocExp LocArg)
  | LetRegExpr RegVar (PreRegExp LocArg)
  | LetExpr (Var, [LocArg], Ty2, PreExp E2Ext LocArg Ty2)
  | LetRegionExpr Region RegionSize (Maybe RegionType)
  deriving (Eq, Ord)

-- | Stores all the expressions that can be hoisted to the top of the function
type HoistAbleExprMap = [(HoistableExpr, (S.Set FreeVarsTy))]

mergeHoistExprMaps :: [HoistAbleExprMap] -> HoistAbleExprMap
mergeHoistExprMaps = L.nub . concat

fromLocArgToFreeVarsTy' :: LocArg -> [FreeVarsTy]
fromLocArgToFreeVarsTy' arg =
  case arg of
    Loc lrm -> [fromLocVarToFreeVarsTy $ lremLoc lrm, fromRegVarToFreeVarsTy $ lremReg lrm]
    EndWitness _ v -> [fromLocVarToFreeVarsTy v]
    Reg v _ -> [fromRegVarToFreeVarsTy v]
    EndOfReg v1 _ v2 -> [fromRegVarToFreeVarsTy v1, fromRegVarToFreeVarsTy v2]
    EndOfReg_Tagged v -> [fromRegVarToFreeVarsTy v]

-- | In order to move all bounds check expressions, we store them in the env.
-- In addition, we also need to store all dependent variables the bounds check
-- depends on in the env.
-- We return the updated expression and map.
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
          let free_vars_in_bound_expr = S.fromList $ concat [fromLocArgToFreeVarsTy' cur, fromLocArgToFreeVarsTy' bound]
          if (S.isSubsetOf free_vars_in_bound_expr benv)
            then do
              (bod', env') <- collectBoundsCheckExprs env benv bod
              return (LetE bnd bod', env')
            else do
              let delayBind = BoundsCheckExpr sz bound cur
              let env' = env ++ [(delayBind, free_vars_in_bound_expr)]
              (bod', env'') <- collectBoundsCheckExprs env' benv bod
              return (bod', env'')
        Ext (BoundsCheckVector bounds) -> do
          let free_vars_in_bound_expr = S.fromList $ concatMap (\(_, bound, cur) -> concat [fromLocArgToFreeVarsTy' bound, fromLocArgToFreeVarsTy' cur]) bounds
          if (S.isSubsetOf free_vars_in_bound_expr benv)
            then do
              (bod', env') <- collectBoundsCheckExprs env benv bod
              return (LetE bnd bod', env')
            else do
              let delayBind = BoundsCheckVectorExpr bounds
              let env' = env ++ [(delayBind , free_vars_in_bound_expr)]
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
        AddFixed {} -> return (ex, env)
        LetLocE loc rhs bod -> do
          (bod', env') <- collectBoundsCheckExprs env benv bod
          return (Ext $ LetLocE loc rhs bod', env')
        LetRegE reg rhs bod -> do
          (bod', env') <- collectBoundsCheckExprs env benv bod
          return (Ext $ LetRegE reg rhs bod', env')
        RetE {} -> return (ex, env)
        TagCursor {} -> return (ex, env)
        LetRegionE r sz ty bod -> do
          (bod', env') <- collectBoundsCheckExprs env benv bod
          return (Ext $ LetRegionE r sz ty bod', env')
        LetParRegionE r sz ty bod -> do
          (bod', env') <- collectBoundsCheckExprs env benv bod
          return (Ext $ LetParRegionE r sz ty bod', env')
        FromEndE {} -> return (ex, env)
        BoundsCheck {} -> return (ex, env)
        IndirectionE {} -> return (ex, env)
        GetCilkWorkerNum -> return (ex, env)
        LetAvail vs bod -> do
          (bod', env') <- collectBoundsCheckExprs env benv bod
          return (Ext $ LetAvail vs bod', env')
        AllocateTagHere {} -> return (ex, env)
        AllocateScalarsHere {} -> pure (ex, env)
        SSPush {} -> pure (ex, env)
        SSPop {} -> pure (ex, env)
        _ -> pure (ex, env)
    -- Straightforward recursion
    VarE {} -> return (ex, env)
    LitE {} -> return (ex, env)
    CharE {} -> return (ex, env)
    FloatE {} -> return (ex, env)
    LitSymE {} -> return (ex, env)
    PrimAppE {} -> return (ex, env)
    DataConE {} -> return (ex, env)
    ProjE i e -> do
      (e', env') <- collectBoundsCheckExprs env benv e
      return (ProjE i e', env')
    IfE a b c -> do
      (a', env') <- collectBoundsCheckExprs env benv a
      (b', env'') <- collectBoundsCheckExprs env benv b
      (c', env''') <- collectBoundsCheckExprs env benv c
      let env'''' = mergeHoistExprMaps [env', env'', env''']
      return (IfE a' b' c', env'''')
    MkProdE ls -> do
      res <- mapM (collectBoundsCheckExprs env benv) ls
      let ls' = map fst res
      let env' = mergeHoistExprMaps $ (map snd res) ++ [env]
      return (MkProdE ls', env')
    CaseE scrt mp -> do
      res <-
        mapM
          ( \(c, args, ae) -> do
              (ae', env') <- collectBoundsCheckExprs env benv ae
              return ((c, args, ae'), env')
          )
          mp
      let mp' = map fst res
      let env' = mergeHoistExprMaps $ map snd res
      return (CaseE scrt mp', env')
    TimeIt e ty b -> do
      (e', env') <- collectBoundsCheckExprs env benv e
      return (TimeIt e' ty b, env')
    SpawnE {} -> error "collectBoundsCheckExprs: TODO SpawnE"
    SyncE -> pure (ex, env)
    MapE {} -> error $ "collectBoundsCheckExprs: TODO MapE"
    FoldE {} -> error $ "collectBoundsCheckExprs: TODO FoldE"

-- | store a expression that needs to be hoisted in the env.
-- We return the updated map and weather the bind was needed or not
storeHoistableExpr :: FreeVarsTy -> FreeVarsTy -> S.Set FreeVarsTy -> HoistableExpr -> HoistAbleExprMap -> (HoistAbleExprMap, Bool)
storeHoistableExpr v1 v2 dependentVars hoistableExpr env
  | v1 == v2 = (env ++ [(hoistableExpr, dependentVars)], True)
  | otherwise = (env, False)

-- | Function that stores all defined vars in the env and returns an expression without the defined variable.
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
      let (env', store) = storeHoistableExpr (fromVarToFreeVarsTy v) vars (allFreeVars rhs) (LetExpr (v, locs, ty, rhs)) env
      if store
        then do
          (bod', env'') <- collectVarsForBoundsCheck vars env' bod
          return (bod', env'')
        else do
          (rhs', env'') <- collectVarsForBoundsCheck vars env' rhs
          (bod', env''') <- collectVarsForBoundsCheck vars env'' bod
          return (LetE (v, locs, ty, rhs') bod', env''')
    WithArenaE v e -> do
      (e', env') <- collectVarsForBoundsCheck vars env e
      return (WithArenaE v e', env')
    Ext ext ->
      case ext of
        AddFixed {} -> return (ex, env)
        LetLocE loc rhs bod -> do
          let (env', store) = storeHoistableExpr (fromLocVarToFreeVarsTy loc) vars (freeVarsInLocExp rhs) (LetLocExpr loc rhs) env
          (bod', env'') <- collectVarsForBoundsCheck vars env' bod
          if store
            then do
              return (bod', env'')
            else do
              return (Ext $ LetLocE loc rhs bod', env'')
        LetRegE reg rhs bod -> do
          let (env', store) = storeHoistableExpr (fromRegVarToFreeVarsTy reg) vars S.empty (LetRegExpr reg rhs) env
          (bod', env'') <- collectVarsForBoundsCheck vars env' bod
          if store
            then do
              return (bod', env'')
            else do
              return (Ext $ LetRegE reg rhs bod', env'')
        RetE {} -> return (ex, env)
        TagCursor {} -> return (ex, env)
        LetRegionE r sz ty bod -> do
          let (env', store) = storeHoistableExpr (fromRegVarToFreeVarsTy (regionToVar r)) vars S.empty (LetRegionExpr r sz ty) env
          (bod', env'') <- collectVarsForBoundsCheck vars env' bod
          if store
            then do
              return (bod', env'')
            else do
              return (Ext $ LetRegionE r sz ty bod', env'')
        LetParRegionE r sz ty bod -> do
          (bod', env') <- collectVarsForBoundsCheck vars env bod
          return (Ext $ LetParRegionE r sz ty bod', env')
        FromEndE {} -> return (ex, env)
        BoundsCheck {} -> return (ex, env)
        IndirectionE {} -> return (ex, env)
        GetCilkWorkerNum -> return (ex, env)
        LetAvail vs bod -> do
          (bod', env') <- collectVarsForBoundsCheck vars env bod
          return (Ext $ LetAvail vs bod', env')
        AllocateTagHere {} -> return (ex, env)
        AllocateScalarsHere {} -> pure (ex, env)
        SSPush {} -> pure (ex, env)
        SSPop {} -> pure (ex, env)
        _ -> pure (ex, env)
    -- Straightforward recursion
    VarE {} -> return (ex, env)
    LitE {} -> return (ex, env)
    CharE {} -> return (ex, env)
    FloatE {} -> return (ex, env)
    LitSymE {} -> return (ex, env)
    PrimAppE {} -> return (ex, env)
    DataConE {} -> return (ex, env)
    ProjE i e -> do
      (e', env') <- collectVarsForBoundsCheck vars env e
      return (ProjE i e', env')
    IfE a b c -> do
      (a', env') <- collectVarsForBoundsCheck vars env a
      (b', env'') <- collectVarsForBoundsCheck vars env b
      (c', env''') <- collectVarsForBoundsCheck vars env c
      let env'''' = mergeHoistExprMaps [env', env'', env''']
      return (IfE a' b' c', env'''')
    MkProdE ls -> do
      res <- mapM (collectVarsForBoundsCheck vars env) ls
      let ls' = map fst res
      let env' = mergeHoistExprMaps $ (map snd res) ++ [env]
      return (MkProdE ls', env')
    CaseE scrt mp -> do
      res <-
        mapM
          ( \(c, args, ae) -> do
              (ae', env') <- collectVarsForBoundsCheck vars env ae
              return ((c, args, ae'), env')
          )
          mp
      let mp' = map fst res
      let env' = mergeHoistExprMaps $ map snd res
      return (CaseE scrt mp', env')
    TimeIt e ty b -> do
      (e', env') <- collectVarsForBoundsCheck vars env e
      return (TimeIt e' ty b, env')
    SyncE -> pure (ex, env)
    SpawnE {} -> error "collectVarsForBoundsCheck: TODO SpawnE"
    MapE {} -> error $ "collectVarsForBoundsCheck: TODO MapE"
    FoldE {} -> error $ "collectVarsForBoundsCheck: TODO FoldE"

freeVarsInLocExp :: LocExp -> S.Set FreeVarsTy
freeVarsInLocExp expr = case expr of
  StartOfRegionLE r -> S.singleton $ fromRegVarToFreeVarsTy (regionToVar r)
  AfterConstantLE _ loc -> S.fromList (fromLocArgToFreeVarsTy' loc)
  AfterVariableLE v loc _ -> S.fromList $ concat [[fromVarToFreeVarsTy v], (fromLocArgToFreeVarsTy' loc)]
  InRegionLE _ -> S.empty
  FreeLE -> S.empty
  FromEndLE loc -> S.fromList (fromLocArgToFreeVarsTy' loc)
  GenSoALoc loc flocs ->
    let env = S.fromList (fromLocArgToFreeVarsTy' loc)
        env' = S.fromList $ concatMap (\(_, l) -> fromLocArgToFreeVarsTy' l) flocs
     in S.union env env'
  GetDataConLocSoA loc -> S.fromList (fromLocArgToFreeVarsTy' loc)
  GetFieldLocSoA _ loc -> S.fromList (fromLocArgToFreeVarsTy' loc)
  AssignLE loc -> S.fromList (fromLocArgToFreeVarsTy' loc)

hoistBoundsCheckProg :: NewL2.Prog2 -> PassM NewL2.Prog2
hoistBoundsCheckProg Prog {ddefs, fundefs, mainExp} = do
  fds' <- mapM (hoistBoundsCheckFun) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f, f)) fds'
  mainExp' <- case mainExp of
    Nothing -> return Nothing
    Just (mn, ty) -> do
      mn' <- hoistBoundsCheck mn S.empty
      return $ Just (mn', ty)
  return $ Prog ddefs fundefs' mainExp'

hoistBoundsCheckFun :: NewL2.FunDef2 -> PassM NewL2.FunDef2
hoistBoundsCheckFun f@FunDef {funTy, funBody} = do
  let initBoundEnv = S.fromList $ map (\(LRM l _ _) -> fromLocVarToFreeVarsTy l) (locVars funTy)
  funBody' <- hoistBoundsCheck funBody initBoundEnv
  return $ f {funBody = funBody'}

-- | recursive function to make sure we release all dependencies for a particular hoistable expression.
-- We return the new expression and updates map (removed binds that were released)
hoistBoundsCheckHelper :: S.Set HoistableExpr -> HoistAbleExprMap -> NewL2.Exp2 -> PassM (NewL2.Exp2, S.Set HoistableExpr)
hoistBoundsCheckHelper visited env l2exp = do
  let boundCheckExprs = env
  (exp', visited') <-
    foldlM
      ( \(expr, vmap) (boundsCheck, dependentVars) -> do
          -- recursively release all dependent vars
          (expr', lets) <-
            foldlM
              ( \(exp'', letenv) var -> do
                  (exp''', lets) <- collectVarsForBoundsCheck var [] exp''
                  let letenv' = mergeHoistExprMaps [letenv, lets]
                  pure (exp''', letenv')
              )
              (expr, [])
              (S.toList dependentVars)
          let expr'' =
                if S.member boundsCheck vmap
                  then Nothing
                  else case boundsCheck of
                    BoundsCheckExpr i bound cur -> Just $ LetE ("_", [], MkTy2 IntTy, (Ext $ BoundsCheck i bound cur)) expr'
                    BoundsCheckVectorExpr bounds -> Just $ LetE ("_", [], MkTy2 IntTy, (Ext $ BoundsCheckVector bounds)) expr'
                    LetLocExpr l rhs -> Just $ Ext $ LetLocE l rhs expr'
                    LetRegExpr r rhs -> Just $ Ext $ LetRegE r rhs expr'
                    LetRegionExpr r sz ty -> Just $ Ext $ LetRegionE r sz ty expr'
                    _ -> error "hoistBoundsCheckHelper: Did not expect expression!"
          -- release all lets
          -- call function recursively
          let vmap' = S.insert boundsCheck vmap
          case expr'' of
            Nothing -> pure (expr', vmap')
            Just expression -> hoistBoundsCheckHelper vmap' lets expression
      )
      (l2exp, visited)
      boundCheckExprs
  pure (exp', visited')

hoistBoundsCheck :: NewL2.Exp2 -> BoundEnv -> PassM NewL2.Exp2
hoistBoundsCheck inexp benv = do
  (exp', m) <- collectBoundsCheckExprs [] benv inexp
  (exp'', _) <- hoistBoundsCheckHelper S.empty m exp'
  pure exp''
