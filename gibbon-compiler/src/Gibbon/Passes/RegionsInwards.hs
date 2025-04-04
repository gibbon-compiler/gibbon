module Gibbon.Passes.RegionsInwards (regionsInwards) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Data.Foldable as F
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L2.Syntax
import Data.Maybe ()
import qualified Data.Maybe as S
import Data.Text.Array (new)


data DelayedBind = DelayRegion FreeVarsTy Region RegionSize (Maybe RegionType)                                            --define data type that can be Region, Loc, LocExp to store the delayed bindings
                 | DelayLoc FreeVarsTy LocExp | DelayParRegion FreeVarsTy Region RegionSize (Maybe RegionType)
  deriving (Show, Generic)

instance Out DelayedBind

type DelayedBindEnv = M.Map (S.Set FreeVarsTy) [DelayedBind]                         --define a Map from set to the DelayedBind data type

regionsInwards :: Prog2 -> PassM Prog2
regionsInwards Prog{ddefs,fundefs,mainExp} = do
    let scopeSetMain = S.fromList $ map (fromVarToFreeVarsTy . funName) (M.elems fundefs)                --Init scopeSet with all the function names
        lambdaFreeVarsTy = L.map (\l -> fromVarToFreeVarsTy l)
        functionArgs = S.fromList $ concatMap (lambdaFreeVarsTy . funArgs) (M.elems fundefs)          --Init functionArgs with all the function arguments, concatenate into one list
        scopeSetFun  = scopeSetMain `S.union` functionArgs                       --scope set for function body is the union of function args and the function names
    fds' <- mapM (placeRegionsInwardsFunBody scopeSetFun) (M.elems fundefs)      --Delay Regions for the function body
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
        Nothing -> return Nothing
        Just (mn, ty)-> do
          let env = M.empty                                                      --Use M.empty for creating the empty env
              in Just . (,ty) <$> placeRegionInwards env scopeSetMain mn         --Delay Regions for the main function

    return $ Prog ddefs fundefs' mainExp'                                        --return new ddefs, fundefs and mainExpressions



placeRegionsInwardsFunBody :: S.Set FreeVarsTy -> FunDef2  -> PassM FunDef2
placeRegionsInwardsFunBody scopeSet f@FunDef{funBody}  = do
  let env     = M.empty                                                          --Create empty environment
  funBody' <- placeRegionInwards env scopeSet funBody                            --Recursively delay regions for function body
  return $ f {funBody = funBody'}


placeRegionInwards :: DelayedBindEnv -> S.Set FreeVarsTy -> Exp2 -> PassM Exp2          --Recursive funtion that will move the regions inwards
placeRegionInwards env scopeSet ex  =
  case ex of
    Ext ext ->
      case ext of

        LetRegionE r sz ty rhs -> do                                                   --take care of regions
          let key' = S.singleton (fromRegVarToFreeVarsTy $ regionToVar r)
              val' = [DelayRegion (fromRegVarToFreeVarsTy $ regionToVar r) r sz ty]
              env' = M.insert key' val' env
              in placeRegionInwards env' scopeSet rhs

        StartOfPkdCursor{} -> return ex
        TagCursor{} -> return ex

        LetLocE loc phs rhs -> do                                                --take care of locations
          case phs of

            StartOfRegionLE r -> do
              let keyList' = M.keys env
                  key'     = F.find (S.member (fromRegVarToFreeVarsTy $ regionToVar r)) keyList'
                  in case key' of
                    Nothing -> do
                      let key'' = S.singleton (fromLocVarToFreeVarsTy loc)
                          val' = [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          env' = M.insert key'' val' env
                       in placeRegionInwards env' scopeSet rhs
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert (fromLocVarToFreeVarsTy loc) myKey
                          valList' = valList ++ [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs         --recurse on rhs using the newenv

            AfterConstantLE _ loc' -> do                                    --In case statement, actual match = AfterConstantLE integralVal loc'
              let keyList' = M.keys env
                  key'     = F.find (S.member (fromLocVarToFreeVarsTy loc')) keyList'
                  in case key' of
                    Nothing -> do
                      let key'' = S.singleton (fromLocVarToFreeVarsTy loc)
                          val' = [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          env' = M.insert key'' val' env
                        in placeRegionInwards env' scopeSet rhs
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert (fromLocVarToFreeVarsTy loc) myKey
                          valList' = valList ++ [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs

            AfterVariableLE _ loc' _ -> do                                  --In case statement, actual match = AfterVariableLE variable loc' boolVal
              let keyList' = M.keys env
                  key'     = F.find (S.member (fromLocVarToFreeVarsTy loc')) keyList'
                  in case key' of
                    Nothing -> do
                        let key'' = S.singleton (fromLocVarToFreeVarsTy loc)
                            val' = [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                            env' = M.insert key'' val' env
                         in placeRegionInwards env' scopeSet rhs
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert (fromLocVarToFreeVarsTy loc) myKey
                          valList' = valList ++ [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs

            InRegionLE r -> do
              let keyList' = M.keys env
                  key'     = F.find (S.member (fromRegVarToFreeVarsTy $ regionToVar r) ) keyList'
                  in case key' of
                    Nothing -> error "No existing region found for this Location in case InRegionLE"
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert (fromLocVarToFreeVarsTy loc) myKey
                          valList' = valList ++ [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs

            FromEndLE loc' -> do
              let keyList' = M.keys env
                  key'     = F.find (S.member (fromLocVarToFreeVarsTy loc') ) keyList'
                  in case key' of
                    Nothing -> error "No existing variable found for this Location in case FromEndLE"
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert (fromLocVarToFreeVarsTy loc) myKey
                          valList' = valList ++ [DelayLoc (fromLocVarToFreeVarsTy loc) phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs
            
            {- VS : Implement cases for other location expressions -}

            FreeLE -> error "Free LE not implemented yet!"                       --For FreeLE we need to figure out how to handle this?

        LetParRegionE r sz ty rhs -> do                                                --Handle a parallel LetRegion
          let key' = S.singleton (fromRegVarToFreeVarsTy $ regionToVar r)
              val' = [DelayParRegion (fromRegVarToFreeVarsTy $ regionToVar r) r sz ty]
              env' = M.insert key' val' env
              in placeRegionInwards env' scopeSet rhs


        RetE locList _                                  -> do              {- Look at the locList to see which variables are alive in env and codegen them before -}
                                                            let (_, ex') = dischargeBinds' env (S.fromList (map fromLocVarToFreeVarsTy locList)) ex
                                                              in return ex'

        FromEndE _                                     -> return ex        {- Actual type is FromEndE loc, Don't need to worry about it will appear later in the pipeline, Just return the expression -}
        BoundsCheck{}                                  -> return ex        {- Actual type is BoundsCheck integer l1 l2, Don't need to worry about it will appear later in the pipeline, Just return the expression -}
        AddFixed{}                                     -> return ex        {- Actual type is AddFixed variable integer, Return the expression -}
        IndirectionE{}                                 -> return ex        {- Actual type: IndirectionE tyCon dataCon (l1,v1) (l2,v2) rhs, skip the recursion, IndirectionE doesn't appear until later in the IR language, return the expression -}
        GetCilkWorkerNum                               -> return ex                   {- Just return the expression, there is no recusrion to do here -}
        LetAvail vs e                                  -> Ext . LetAvail vs <$> go e  {- Recurse on the rhs directly -}
        AllocateTagHere{} -> return ex
        AllocateScalarsHere{} -> return ex
        SSPush{} -> return ex
        SSPop{} -> return ex

     -- Straightforward recursion ...
    VarE{}                 -> return ex        -- Just return Nothing special here
    LitE{}                 -> return ex        -- Just return Nothing special here
    CharE{}                -> return ex
    FloatE{}               -> return ex        -- Just return Nothing special here
    LitSymE{}              -> return ex        -- Just return Nothing special here
    AppE f locVars ls      -> do
                              let allKeys  =  M.keys env                                                             -- List of all keys from env
                                  keyList  = map (\variable -> F.find (S.member (fromLocVarToFreeVarsTy variable)) allKeys) locVars           -- For each var in the input set find its corresponding key
                                  keyList' = S.catMaybes keyList                                                     -- Filter all the Nothing values from the list and let only Just values in the list
                                  newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
                                  newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                  tupleList = zip newKeys newVals
                                  newEnv'   = M.fromList tupleList
                               in do ls' <- mapM (placeRegionInwards newEnv' scopeSet) ls
                                     let (_, ex') = dischargeBinds' env (S.fromList (map fromLocVarToFreeVarsTy locVars)) (AppE f locVars ls')
                                      in return ex'

    PrimAppE{}             -> return ex                                                                                   -- Just return, Nothing special here

    DataConE loc dataCons args      -> do
                                       let allKeys  =  M.keys env                                                         -- List of all keys from env
                                           freelist = map allFreeVars args 
                                           freevars = foldl (\s1 s2 -> s1 `S.union` s2) (S.empty) freelist
                                           keyList  = map (\variable -> F.find (S.member variable) allKeys) ((S.toList freevars) ++ [fromLocVarToFreeVarsTy loc])       -- For each var in the input set find its corresponding key
                                           keyList' = S.catMaybes keyList                                                 -- Filter all the Nothing values from the list and let only Just values in the list
                                           newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'   -- Filter all the Nothing values from the list and let only Just values in the list
                                           newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                           tupleList = zip newKeys newVals
                                           newEnv'   = M.fromList tupleList
                                           in do args' <- mapM (placeRegionInwards newEnv' scopeSet) args
                                                 let (_, ex') = dischargeBinds' env (freevars `S.union` (S.singleton (fromLocVarToFreeVarsTy loc))) (DataConE loc dataCons args')
                                                  in return ex'

    ProjE i e              -> ProjE i <$> go e    {- Simple recursion on e -}

    IfE a b c              -> do     -- Optimization for IF statements check the freeVariables in b and c, intersect them to avoid generating duplicate bindings at in then and else part
                                     let freeVarsLocalB  = allFreeVars b
                                         freeVarsLocalC  = allFreeVars c
                                         commonVars = freeVarsLocalB `S.intersection` freeVarsLocalC
                                         --_          = dbgTraceIt (sdoc commonVars)
                                         allKeys    = M.keys env
                                         keyList    = map (\variable -> F.find (S.member variable) allKeys) (S.toList commonVars)
                                         keyList'   = S.catMaybes keyList
                                         newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'
                                         newVals    = map (\key -> M.findWithDefault [] key env) newKeys
                                         tupleList  = zip newKeys newVals
                                         newEnv'    = M.fromList tupleList
                                     b' <- placeRegionInwards env scopeSet b       -- Recurse on b (Then part)
                                     c' <- placeRegionInwards env scopeSet c       -- Recurse on c (Else part)
                                     let (_, a') = dischargeBinds' newEnv' commonVars a
                                     return $ IfE a' b' c'                             -- Return the new IfE expression {-dbgTraceIt (sdoc (commonVars, keyList, env, newEnv'))-}

    MkProdE ls                    -> MkProdE <$> mapM go ls                            {- Recurse over all expression in the tuple in the expression ls -}

    LetE (v,locs,ty,rhs) bod      -> do
                                    let newScope = S.insert (fromVarToFreeVarsTy v) scopeSet                                                     {- The locs will be empty at this point, so just update scope set and recurse -}
                                        allKeys  =  M.keys env
                                        free_vars =   map fromLocVarToFreeVarsTy $ locsInTy ty                                                          -- List of all keys from env
                                        keyList  = map (\variable -> F.find (S.member variable) allKeys) free_vars         -- For each var in the input set find its corresponding key
                                        keyList' = S.catMaybes keyList
                                        newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
                                        newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                        tupleList = zip newKeys newVals
                                        newEnv'   = M.fromList tupleList
                                        in do ex' <- LetE . (v,locs,ty,) <$> placeRegionInwards newEnv' newScope rhs <*> placeRegionInwards newEnv' newScope bod
                                              let (_, ex'') = dischargeBinds' env (S.fromList free_vars) ex'
                                               in return ex''

    CaseE scrt brs                -> do
      brs' <- mapM
        (\(a,b,c) -> do let varList = fmap fst b                                                                       -- Get all the variables from the tuple list
                            varList' = L.map fromVarToFreeVarsTy varList
                            newScope  = scopeSet `S.union` S.fromList varList'                                          -- Make the newScope set by unioning the old one with the varList
                            allKeys   =  M.keys env
                            free_vars = (allFreeVars c) `S.union` newScope                                                 -- List of all keys from env
                            keyList   = map (\variable -> F.find (S.member variable) allKeys) (S.toList free_vars)     -- For each var in the input set find its corresponding key
                            keyList'  = S.catMaybes keyList
                            newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'               -- Filter all the Nothing values from the list and let only Just values in the list
                            newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                            tupleList = zip newKeys newVals
                            newEnv'   = M.fromList tupleList
                        c' <- placeRegionInwards env newScope c
                        let (_, c'') = dischargeBinds' newEnv' free_vars c'                                                -- Discharge the binds using the newScope and the dictionary
                         in return (a,b,c'')) brs                                                                          -- dbgTraceIt (sdoc (free_vars, keyList, env, newEnv'))

      return $ CaseE scrt brs'
    TimeIt e ty b                 -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{}                      -> pure ex
    SyncE{}                       -> pure ex
    WithArenaE v e                -> WithArenaE v <$> go e
    MapE{}                        -> return ex                        -- Is there a recursion element to this?
    FoldE{}                       -> return ex                        -- Is there a recursion element to this?
  where
    go = placeRegionInwards env scopeSet

-- This is a function to discharge binds given a dictionary, scopeSet and expression where free variables might exist
dischargeBinds :: DelayedBindEnv -> S.Set FreeVarsTy -> Exp2 -> (DelayedBindEnv, Exp2)
dischargeBinds env scopeSet exp2 =
  let free_vars_exp2   = allFreeVars exp2
      free_vars        = S.difference free_vars_exp2 scopeSet                         -- Take the difference of the scopeSet with the set that freeVar gives.
      (newEnv, newExp) = codeGen free_vars env exp2
  in  (newEnv, newExp)

-- This is a duplicate function to the one above but instead it takes a Set of LocVar to codeGen directly instead of the expression and scopeSet.
dischargeBinds' :: DelayedBindEnv -> S.Set FreeVarsTy -> Exp2 -> (DelayedBindEnv, Exp2)
dischargeBinds' env free_vars exp2 = do codeGen free_vars env exp2

-- Use this function to codegen from the env by giving a set of variables you want to codegen from
codeGen :: S.Set FreeVarsTy -> DelayedBindEnv -> Exp2 -> (DelayedBindEnv, Exp2)
codeGen set env body =
  let allKeys   =  M.keys env                                                          -- List of all keys from env
      keyList   = map (\variable -> F.find (S.member variable) allKeys ) (toList set)  -- For each var in the input set find its corresponding key
      keyList'  = S.toList $ S.fromList $ S.catMaybes keyList                          -- Filter out all the Nothing values from the list and let only Just values in the list
      valList   = concatMap (\key -> M.findWithDefault [] key env) keyList'            -- For each key in the keyList from before find the value associated with the key
      newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'     -- Filter all the Nothing values from the list and let only Just values in the list
      newVals   = map (\key -> M.findWithDefault [] key env) newKeys
      tupleList = zip newKeys newVals
      newEnv'   = M.fromList tupleList
      exps      = foldr bindDelayedBind body valList                                   -- Get all the bindings for all the expressions in the key
   in (newEnv', exps)
   -- dbgTraceIt "Print in regionsInwards: "  dbgTraceIt (sdoc (set, allKeys, env, valList, newEnv')) dbgTraceIt "End regionsInwards.\n" 

bindDelayedBind :: DelayedBind -> Exp2 -> Exp2
bindDelayedBind delayed body =
  case delayed of
    DelayRegion r r' sz ty -> Ext $ LetRegionE r' sz ty body
    DelayParRegion r r' sz ty -> Ext $ LetParRegionE r' sz ty body
    DelayLoc (FL loc) locexp -> Ext $ LetLocE loc locexp body


-- A function for use specific to this pass which gives all the possible variables and local variables that are used in a particular expression
-- This pass was made speciic because other version in gibbon don't return location variables, this version also adds location variables to the
-- returned set

-- freeVarsLocal :: Exp2 -> S.Set FreeVarsTy
-- freeVarsLocal ex = case ex of
--   Ext ext                           ->
--     case ext of
--       LetRegionE _ _ _ rhs          -> freeVarsLocal rhs
--       LetLocE _ phs rhs             ->
--         case phs of
--         StartOfRegionLE _                 -> freeVarsLocal rhs
--         AfterConstantLE _ _         -> freeVarsLocal rhs
--         AfterVariableLE{}           -> freeVarsLocal rhs
--         InRegionLE _                -> freeVarsLocal rhs
--         FromEndLE _                 -> freeVarsLocal rhs
--         _                           -> S.empty
--       _                             -> S.empty

--   LetE (_,locs, ty,rhs) bod         -> let freeVarsLocalRhs = freeVarsLocal rhs
--                                            freeVarsLocalBod = freeVarsLocal bod
--                                          in S.fromList (map fromLocVarToFreeVarsTy locs)  `S.union` S.fromList (map fromLocVarToFreeVarsTy (locsInTy ty)) `S.union` freeVarsLocalRhs `S.union` freeVarsLocalBod
--   LitE _                            -> S.empty
--   LitSymE _                         -> S.empty
--   VarE v                            -> S.singleton (fromVarToFreeVarsTy v)
--   AppE v locvarList ls              -> S.unions (L.map freeVarsLocal ls) `S.union` S.singleton (fromVarToFreeVarsTy v) `S.union` S.fromList (map fromLocVarToFreeVarsTy locvarList)
--   PrimAppE _ ls                     -> S.unions (L.map freeVarsLocal ls)
--   MkProdE ls                        -> S.unions (L.map freeVarsLocal ls)
--   DataConE locVar _ ls              -> S.singleton (fromLocVarToFreeVarsTy locVar)  `S.union`  S.unions (L.map freeVarsLocal ls)
--   ProjE _ e                         -> freeVarsLocal e
--   IfE e1 e2 e3                      -> S.unions [freeVarsLocal e1, freeVarsLocal e2, freeVarsLocal e3]
--   CaseE e ls                        -> freeVarsLocal e `S.union`
--                                         S.unions (L.map (\(_, vlocs, ee) ->
--                                            let (vars, locVars) = unzip vlocs
--                                                vars' = L.map fromVarToFreeVarsTy vars
--                                            in freeVarsLocal ee `S.union` S.fromList vars' `S.union` S.fromList (map fromLocVarToFreeVarsTy locVars)) ls)
--   _                                 -> S.empty
