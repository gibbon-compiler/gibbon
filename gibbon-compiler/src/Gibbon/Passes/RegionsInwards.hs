module Gibbon.Passes.RegionsInwards (regionsInwards) where

import GHC.Generics (Generic)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L 
import Data.Foldable as F
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L2.Syntax
import Data.Maybe ()
import qualified Data.Maybe as S
import Gibbon.Passes.InferLocations (inferExp')


data DelayedBind = DelayRegion Region                                            --define data type that can be Region, Loc, LocExp to store the delayed bindings
                 | DelayLoc LocVar LocExp | DelayParRegion Region
  deriving (Show, Generic)

instance Out DelayedBind

type DelayedBindEnv = M.Map (S.Set LocVar) [DelayedBind]                         --define a Map from set to the DelayedBind data type  

regionsInwards :: Prog2 -> PassM Prog2
regionsInwards Prog{ddefs,fundefs,mainExp} = do
    let scopeSetMain = S.fromList $ map funName (M.elems fundefs)                --Init scopeSet with all the function names
        functionArgs = S.fromList $ concatMap funArgs (M.elems fundefs)          --Init functionArgs with all the function arguments, concatenate into one list 
        scopeSetFun  = scopeSetMain `S.union` functionArgs                       --scope set for function body is the union of function args and the function names   
    fds' <- mapM (placeRegionsInwardsFunBody scopeSetFun) (M.elems fundefs)      --Delay Regions for the function body 
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
        Nothing -> return Nothing
        Just (mn, ty)-> do 
          let env = M.empty                                                      --Use M.empty for creating the empty env 
              in Just . (,ty) <$> placeRegionInwards env scopeSetMain mn         --Delay Regions for the main function

    return $ Prog ddefs fundefs' mainExp'                                        --return new ddefs, fundefs and mainExpressions



placeRegionsInwardsFunBody :: S.Set Var -> FunDef2  -> PassM FunDef2
placeRegionsInwardsFunBody scopeSet f@FunDef{funBody}  = do
  let env     = M.empty                                                          --Create empty environment
  funBody' <- placeRegionInwards env scopeSet funBody                            --Recursively delay regions for function body
  return $ f {funBody = funBody'}


placeRegionInwards :: DelayedBindEnv -> S.Set Var -> Exp2 -> PassM Exp2          --Recursive funtion that will move the regions inwards
placeRegionInwards env scopeSet ex  =
  case ex of
    Ext ext ->
      case ext of

        LetRegionE r rhs -> do                                                   --take care of regions
          let key' = S.singleton (regionToVar r)
              val' = [DelayRegion r]
              env' = M.insert key' val' env
              in placeRegionInwards env' scopeSet rhs 
  
        LetLocE loc phs rhs -> do                                                --take care of locations    
          case phs of

            StartOfLE r -> do                                                 
              let keyList' = M.keys env
                  key'     = F.find (S.member (regionToVar r)) keyList'
                  in case key' of
                    Nothing -> do
                      let key'' = S.singleton loc
                          val' = [DelayLoc loc phs]
                          env' = M.insert key'' val' env
                       in placeRegionInwards env' scopeSet rhs 
                    Just myKey -> do 
                      let valList  = M.findWithDefault [] myKey env 
                          myKey'   = S.insert loc myKey
                          valList' = valList ++ [DelayLoc loc phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs         --recurse on rhs using the newenv
            
            AfterConstantLE _ loc' -> do                                    --In case statement, actual match = AfterConstantLE integralVal loc'
              let keyList' = M.keys env
                  key'     = F.find (S.member loc') keyList'
                  in case key' of
                    Nothing -> do
                      let key'' = S.singleton loc
                          val' = [DelayLoc loc phs]
                          env' = M.insert key'' val' env
                        in placeRegionInwards env' scopeSet rhs 
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert loc myKey
                          valList' = valList ++ [DelayLoc loc phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs 
                          
            AfterVariableLE _ loc' _ -> do                                  --In case statement, actual match = AfterVariableLE variable loc' boolVal
              let keyList' = M.keys env
                  key'     = F.find (S.member loc') keyList'
                  in case key' of
                    Nothing -> do
                        let key'' = S.singleton loc
                            val' = [DelayLoc loc phs]
                            env' = M.insert key'' val' env
                         in placeRegionInwards env' scopeSet rhs 
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert loc myKey
                          valList' = valList ++ [DelayLoc loc phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs 

            InRegionLE r -> do
              let keyList' = M.keys env
                  key'     = F.find (S.member (regionToVar r) ) keyList'
                  in case key' of
                    Nothing -> error "No existing region found for this Location in case InRegionLE"
                    Just myKey -> do 
                      let valList  = M.findWithDefault [] myKey env 
                          myKey'   = S.insert loc myKey
                          valList' = valList ++ [DelayLoc loc phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs 

            FromEndLE loc' -> do
              let keyList' = M.keys env
                  key'     = F.find (S.member loc') keyList'
                  in case key' of
                    Nothing -> error "No existing variable found for this Location in case FromEndLE"
                    Just myKey -> do
                      let valList  = M.findWithDefault [] myKey env
                          myKey'   = S.insert loc myKey
                          valList' = valList ++ [DelayLoc loc phs]
                          tempDict = M.delete myKey env
                          newEnv   = M.insert myKey' valList' tempDict
                          in placeRegionInwards newEnv scopeSet rhs 

            FreeLE -> error "Free LE not implemented yet!"                       --For FreeLE we need to figure out how to handle this
         
        LetParRegionE r rhs -> do                                                --Handle a parallel LetRegion
          let key' = S.singleton (regionToVar r)
              val' = [DelayParRegion r]
              env' = M.insert key' val' env
              in placeRegionInwards env' scopeSet rhs 


        RetE locList _                                  -> do  {-Actual type is RetE locList variable, here you can't just return the expression, look at the locList to see which variables are alive in env and codegen them before-}
                                                            let (_, ex') = dischargeBinds' env (S.fromList locList) ex
                                                              in return ex'

        FromEndE _                                     -> return ex {-Actual type is FromEndE loc, Don't need to worry about it will appear later in the pipeline, Just return the expression-}
        BoundsCheck{}                                  -> return ex {-Actual type is BoundsCheck integer l1 l2, Don't need to worry about it will appear later in the pipeline, Just return the expression-}
        AddFixed{}                                     -> return ex {-Actual type is AddFixed variable integer, Return the expression-}
        IndirectionE{}                                 -> return ex {-Actual type: IndirectionE tyCon dataCon (l1,v1) (l2,v2) rhs, skip the recursion, IndirectionE doesn't appear until later in the IR language, return the expression-}
        GetCilkWorkerNum                               -> return ex {-Just return the expression, there is no recusrion to do here-}
        LetAvail vs e                                  -> Ext . LetAvail vs <$> go e  {-Recurse on the rhs directly-}
        

     -- Straightforward recursion ...
    VarE{}                 -> return ex --Just return Nothing special here 
    LitE{}                 -> return ex --Just return Nothing special here 
    FloatE{}               -> return ex --Just return Nothing special here 
    LitSymE{}              -> return ex --Just return Nothing special here 
    AppE f locVars ls      -> do
                              let allKeys  =  M.keys env                                                            -- List of all keys from env
                                  keyList  = map (\variable -> F.find (S.member variable) allKeys) locVars          -- For each var in the input set find its corresponding key
                                  keyList' = S.catMaybes keyList                                                    -- Filter all the Nothing values from the list and let only Just values in the list
                                  newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
                                  newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                  tupleList = zipWith (\x y -> (x, y)) newKeys newVals
                                  newEnv'   = M.fromList tupleList
                               in do ls' <- mapM (placeRegionInwards newEnv' scopeSet) ls
                                     let (_, ex') = dischargeBinds' env (S.fromList locVars) (AppE f locVars ls')
                                      in return ex'

      --Just return Nothing special here 
    PrimAppE{}             -> return ex --Just return Nothing special here 

    DataConE loc dataCons args      -> do
                                       let allKeys  =  M.keys env                                                        -- List of all keys from env
                                           keyList  = map (\variable -> F.find (S.member variable) allKeys) [loc]        -- For each var in the input set find its corresponding key
                                           keyList' = S.catMaybes keyList                                                -- Filter all the Nothing values from the list and let only Just values in the list
                                           newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'  -- Filter all the Nothing values from the list and let only Just values in the list
                                           newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                           tupleList = zipWith (\x y -> (x, y)) newKeys newVals
                                           newEnv'   = M.fromList tupleList
                                           in do args' <- mapM (placeRegionInwards newEnv' scopeSet) args
                                                 let (_, ex') = dischargeBinds' env (S.singleton loc) (DataConE loc dataCons args')
                                                  in return ex'                        
                                                  
    ProjE i e              -> ProjE i <$> go e {-Simple recursion on e-}

    IfE a b c              -> do  {-Check if there are freeVariables in the condition a, if the set has any freeVars from "a" then codegen all the locations and regions before the IfE-}
                                     let (d, a') =  {-dbgTraceIt "Starting binding from IfE"-} (dischargeBinds env scopeSet a) --If there are freeVariables in a then codgen bindings for those in a
                                     b' <- placeRegionInwards d scopeSet b        --Recurse on b (Then part) 
                                     c' <- placeRegionInwards d scopeSet c        --Recurse on c (Else part)
                                     return $ IfE a' b' c' --dbgTraceIt "End IfE"                        --Return the new IfE expression

    MkProdE ls                    -> MkProdE <$> mapM go ls {-Recurse over all expression in the tuple in the expression ls-}

    LetE (v,locs,ty,rhs) bod      -> do
                                    let newScope = S.insert v scopeSet                                                              {-The locs will be empty at this point, so just update scope set and recurse-}
                                        allKeys  =  M.keys env
                                        free_vars =   locsInTy ty                                                                  -- List of all keys from env
                                        keyList  = map (\variable -> F.find (S.member variable) allKeys) free_vars  -- For each var in the input set find its corresponding key
                                        keyList' = S.catMaybes keyList 
                                        newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
                                        newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                                        tupleList = zipWith (\x y -> (x, y)) newKeys newVals
                                        newEnv'   = M.fromList tupleList
                                        in do ex' <- LetE . (v,locs,ty,) <$> placeRegionInwards newEnv' newScope rhs <*> placeRegionInwards newEnv' newScope bod
                                              let (_, ex'') = dischargeBinds' env (S.fromList free_vars) ex'
                                               in {-dbgTraceIt "\nPrint info in LetE: (v, locs, ty rhs)\n" dbgTraceIt (sdoc (v, locs, ty, rhs, env, newEnv',ex'')) dbgTraceIt (sdoc (keyList, ex', free_vars, newVals, tupleList)) dbgTraceIt "End of LetE\n"-} return ex''
                                          
                                      -- in dbgTraceIt "\nPrint info in LetE: (v, locs, ty rhs)\n" dbgTraceIt (sdoc (v, locs, ty, rhs)) dbgTraceIt "End of LetE\n"  {-dbgTraceIt "\nThis is what the LetE expression look like in L2 at this point\n" dbgTraceIt (sdoc ex) dbgTraceIt "\nEnd of LetE\n"-}   
    CaseE scrt brs                -> do      
      brs' <- mapM 
        (\(a,b,c) -> do let varList = fmap fst b                                                                       --Get all the variables from the tuple list
                            newScope  = scopeSet `S.union` S.fromList varList                                          -- Make the newScope set by unioning the old one with the varList
                            allKeys   =  M.keys env
                            free_vars = freeVars c `S.union` newScope                                                                     -- List of all keys from env
                            keyList   = map (\variable -> F.find (S.member variable) allKeys) (S.toList free_vars)   -- For each var in the input set find its corresponding key
                            keyList'  = S.catMaybes keyList
                            newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
                            newVals   = map (\key -> M.findWithDefault [] key env) newKeys
                            tupleList = zipWith (\x y -> (x, y)) newKeys newVals
                            newEnv'   = M.fromList tupleList
                        c' <- placeRegionInwards newEnv' newScope c
                        let (_, c'') = {-dbgTraceIt "Starting binding from CaseE"-} dischargeBinds' env free_vars c'          -- Discharge the binds using the newScope and the dictionary
                         in {-dbgTraceIt "Print (c, c' c'') in CaseE\n" dbgTraceIt (sdoc c) dbgTraceIt "1\n" dbgTraceIt (sdoc c') dbgTraceIt "2\n" dbgTraceIt (sdoc c'') dbgTraceIt "3\n" dbgTraceIt (sdoc (env,free_vars, newEnv', keyList, keyList')) dbgTraceIt "End CaseE\n"-} (return (a,b,c''))) brs
                        {-dbgTraceIt "Print the env that is passed Initially\n" dbgTraceIt (sdoc env) dbgTraceIt "\nPrint Parts of the CaseE statement\n" dbgTraceIt (sdoc (a, b, c)) dbgTraceIt "\nEnd of CaseE a, b, c\n" -}                              --dbgTraceIt (sdoc (c,c'))
      return $ CaseE scrt brs'
    TimeIt e ty b                 -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{}                      -> pure ex   
    SyncE{}                       -> pure ex
    WithArenaE v e                -> WithArenaE v <$> go e
    MapE{}                        -> return ex --Is there a recursion element to this?
    FoldE{}                       -> return ex --Is there a recursion element to this?
  where 
    go = placeRegionInwards env scopeSet

    --Cases for which checking the local variables might be important
    --AppE
    --DataConE
    --IfE
    --LetE
    --CaseE
    --SpawnE

{-

foo x y = x

bar x y = y

initial inScope for main expression = (names of all top level functions)
initial inScope for functions = (names of all top level functions) + (arguments to functions)

-- lots of passes track Env2

-- allFreeVars :: Exp2 -> [Var]

main =
  let a = foo 1 2 in -- inScope = {foo, bar}
  let b = bar 2 3 in -- inScope = {foo, bar, a}
  (a,b)              -- inScope = {foo, bar, a, b}

letregion r bod -> inScope doesn't grow here

grow for:
- let expressions
- bound variables in pattern matches for case

-}

--This is a function to discharge binds given a dictionary, scopeSet and expression where free variables might exist
dischargeBinds :: DelayedBindEnv -> S.Set Var -> Exp2 -> (DelayedBindEnv, Exp2)
dischargeBinds env scopeSet exp2 =
  let free_vars        = S.difference (freeVars exp2) scopeSet   --Take the difference of the scopeSet with the set that freeVar gives.
      (newEnv, newExp) = codeGen free_vars env exp2
  in {-dbgTraceIt "\nPrint info in discharge binds (env, freevars, newEnv, newExp)\n" dbgTraceIt (sdoc (env, free_vars, newEnv, newExp, scopeSet)) dbgTraceIt "\nEnd\n"-} (newEnv, newExp)

--This is a duplicate function to the one above but instead it takes a Set of LocVar to codeGen directly instead of the expression and scopeSet.
dischargeBinds' :: DelayedBindEnv -> S.Set LocVar -> Exp2 -> (DelayedBindEnv, Exp2)
dischargeBinds' env free_vars exp2 = do codeGen free_vars env exp2  

{-

--Use this function to recursively create Maybe Exp2, it terminates when you reach [] or the variable you are doing codeGen for
buildExp2 :: [DelayedBind] -> LocVar -> Bool -> (Maybe Exp2 , Bool)
buildExp2 valList var terminate = case (valList, var, terminate) of
  ([], _ , _)              -> (Nothing, True)
  (_ , _ , True)           -> (Nothing, True) 
  (x : xs, locVar, False)  -> case x of
    DelayRegion region     -> if region == locVar 
                                then LetRegionE region (buildExp2 xs locVar True)
                                else LetRegionE region (buildExp2 xs locVar False)
    DelayLoc variable locExp -> if variable == locVar 
                                then LetLocE variable locExp (buildExp2 xs locVar True)
                                else LetLocE variable locExp (buildExp2 xs locVar False)
    DelayParRegion region  -> if region == locVar 
                                then LetParRegionE region (buildExp2 xs locVar True)
                                else LetParRegionE region (buildExp2 xs locVar False) 
                                
-}

-- Use this function to codegen from the env by giving a set of variables you want to codegen from
codeGen :: S.Set LocVar -> DelayedBindEnv -> Exp2 -> (DelayedBindEnv, Exp2)
codeGen set env body =
  let allKeys   =  M.keys env                                                          --List of all keys from env
      keyList   = map (\variable -> F.find (S.member variable) allKeys ) (toList set)  -- For each var in the input set find its corresponding key
      keyList'  = S.toList $ S.fromList $ S.catMaybes keyList                          -- Filter out all the Nothing values from the list and let only Just values in the list
      valList   = concatMap (\key -> M.findWithDefault [] key env) keyList'            -- For each key in the keyList from before find the value associated with the key
      newKeys   = S.toList $ S.fromList allKeys `S.difference` S.fromList keyList'       -- Filter all the Nothing values from the list and let only Just values in the list
      newVals   = map (\key -> M.findWithDefault [] key env) newKeys
      tupleList = zipWith (\x y -> (x, y)) newKeys newVals
      newEnv'   = M.fromList tupleList
      exps      = foldr bindDelayedBind body valList                                   -- Get all the bindings for all the expressions in the key  
   in {-dbgTraceIt "Print info codeGen (keys, vals, delete, newEnv)\n" dbgTraceIt ( sdoc (keyList', valList, newEnv, newEnv') ) dbgTraceIt "End: codegen\n"-} (newEnv', exps) -- dbgTraceIt (sdoc (set,env,body)) -- This was for printing : dbgTraceIt (sdoc (set,env,body))

bindDelayedBind :: DelayedBind -> Exp2 -> Exp2
bindDelayedBind delayed body =
  case delayed of
    DelayRegion r -> Ext $ LetRegionE r body
    DelayParRegion r -> Ext $ LetParRegionE r body
    DelayLoc loc locexp -> Ext $ LetLocE loc locexp body

-- convertFromMaybe :: Maybe a -> a
-- convertFromMaybe maybeA = case maybeA of
--   Nothing -> null
--   Just a  -> a 


--A function for use specific to this pass which gives all the possible variables and local variables that are used in a particular expression
freeVars :: Exp2 -> S.Set Var
freeVars ex = case ex of
  Ext ext                           ->
    case ext of
      LetRegionE _ rhs              -> freeVars rhs
      LetLocE loc phs rhs           -> 
        case phs of
        StartOfLE r                 -> freeVars rhs 
        AfterConstantLE _ loc'      -> freeVars rhs
        AfterVariableLE var loc' _  -> freeVars rhs
        InRegionLE r                -> freeVars rhs
        FromEndLE loc'              -> freeVars rhs
        _                           -> S.empty
      _                             -> S.empty
  
  LetE (_,locs, ty,rhs) bod         -> (S.fromList locs)  `S.union` (S.fromList (locsInTy ty)) `S.union` (freeVars rhs) `S.union` (freeVars bod)
  LitE _                            -> S.empty
  LitSymE _                         -> S.empty
  VarE v                            -> S.singleton v
  AppE v locvarList ls              -> S.unions (L.map freeVars ls) `S.union` (S.singleton v) `S.union` (S.fromList locvarList)
  PrimAppE _ ls                     -> S.unions (L.map freeVars ls) 
  MkProdE ls                        -> S.unions (L.map freeVars ls)
  DataConE locVar _ ls              -> S.singleton locVar  `S.union`  S.unions (L.map freeVars ls)
  ProjE _ e                         -> freeVars e
  IfE e1 e2 e3                      -> S.unions [freeVars e1, freeVars e2, freeVars e3]
  CaseE e ls                        -> freeVars e `S.union`
                                        S.unions (L.map (\(_, vlocs, ee) ->
                                           let (vars, locVars) = unzip vlocs
                                           in freeVars ee `S.union` S.fromList vars `S.union` S.fromList locVars) ls)
  _                                 -> S.empty


{-

free variables
----------------------

let x = 1 in
let y = 2 in
(x,y)

freeVars (x,y) = {x,y}
freeVars (let y = 2 in (x,y)) = {x}

LetE (v,locs,ty,rhs) bod -> freeVars rhs `S.difference` (S.singleton v)

(if loc is free ty then loc is always free rhs.)

duplicating bindings
------------------------

letregion r1 in
letloc l1 = startof r1 in
if X
  then ....allocate to l1....
  else ....allocate to l1....

==> 

if X
then letregion r1 in
     letloc l1 = startof r1 in
     ... allocate to l1 ...
else letregion r1 in
     letloc l1 = startof r1 in
     ... allocate to l1 ...

=== implementation ===

IfE a b c -> do 
             let free_b = allFreeVars b
             let free_c = allFreeVars c
             let common = free_b `S.intersect` free_c -- all regions and locations 
                                                      -- used in both branches
             let keys_to_delete = blah common
             b' <- placeRegionsInwards (env - keys_to_delete) scopeSet b
             c' <- placeRegionsInwards (env - keys_to_delete) scopeSet c
             dischargeBinds' env common ex'


old version
-------------------------

letregion r1 in
letloc l1 = startof r1 in
(if X
  then ....allocate to l1....
  else ....allocate to l1....)

when we process the if expression, it returns the regions and locations it generated
bindings for. 

LetLocE loc locexp bod -> do (bod',X) recurse env in_scope bod
                             -- X tells us if loc is bound in bod
                             if (loc is bound in bod)
                               then bod
                               else LetLocE loc locexp bod

=====>
 


State monad:
----------------------------

C:

map_t my_map = XX;

int foo(expr_t ex) {
  // update + use my_map
}

Hs:

foo :: Map x y -> a
foo env = ...

typedef PassM x y a = State (Map x y) a

return, bind;

-}