{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# HLINT ignore "Use tuple-section" #-}
module Gibbon.Passes.OptimizeADTLayout
  ( shuffleDataCon,
  )
where

-- Gibbon imports

import Control.Exception (evaluate)
import Data.List as L

import           Data.Graph                     as G
import           Control.Monad

import Data.Set as S
-- Haskell imports
import Data.Map as M
import Data.Maybe as Maybe
import Data.Time.Clock
  ( diffUTCTime,
    getCurrentTime,
  )
import Gibbon.Common
import Gibbon.Language
import Gibbon.Language.Syntax
import Gibbon.L1.Syntax as L1
import Gibbon.Passes.AccessPatternsAnalysis
  ( DataConAccessMap,
    FieldMap,
    generateAccessGraphs,
  )
import Gibbon.Passes.CallGraph
  ( ProducersMap (..),
    generateProducerGraph,
  )
import Gibbon.Passes.ControlFlowGraph (getFunctionCFG)
import Gibbon.Passes.DefinitionUseChains
  ( DefUseChainsFunctionMap (..),
    generateDefUseChainsFunction,
    progToVEnv,
    getDefinitionsReachingLetExp,
    UseDefChainsFunctionMap (..)
  )
import Gibbon.Passes.SolveLayoutConstrs (solveConstrs)
import Gibbon.Pretty
import System.CPUTime
import System.IO.Unsafe as U
import System.TimeIt
import Text.PrettyPrint.GenericPretty
import Prelude as P
import Data.Data (Data)
import qualified Gibbon.L2.Syntax as L1

-- | Data structure to store output from ILP solver.
-- | Maps DataCon to bijection of new indices -> fields of datacon
type FieldOrder = M.Map DataCon [Integer]

-- TODO: Make FieldOrder an argument passed to shuffleDataCon function.
shuffleDataCon ::
  Prog1 ->
  PassM Prog1
shuffleDataCon prg@Prog{ddefs, fundefs, mainExp} =
  do
    let list_pair_func_dcon =
          concatMap ( \fn@(FunDef {funName, funMeta = FunMeta {funOptLayout = layout}}) ->
                  case layout of
                    Single dcon -> [(fromVar funName, dcon)]
                    -- only handles optimizing a single dcon for a function right now.
                    -- its okay for the current examples
                    -- but should be extended
                    _ -> []
              ) (M.elems fundefs)
    -- If a total ordering is defined for a function (by the user), then we should just use that instead.
    -- The total ordering defined by the user should just override
    -- get the function for which the total ordering is defined and get the corresponding total ordering.
    -- Tuple (funcName, map) map : map from data constructor to the user defined ordering.
    let userConstraints =
          concatMap ( \fn@( FunDef
                        { funName,
                          funMeta = FunMeta {userConstraintsDataCon = totalOrdering}
                        }
                      ) ->
                    case totalOrdering of
                      Nothing -> []
                      Just m -> [(fromVar funName, m)]
              ) (M.elems fundefs)
    -- pure prg
    case userConstraints of
      [] ->
        case list_pair_func_dcon of
          [] -> pure prg
          --TODO: handle for more than one function
          (funcName, dcon) : xs -> do
            let [fundef] =
                  P.concatMap
                    ( \fn@(FunDef {funName}) ->
                        ([fn | fromVar funName == funcName])
                    )
                    (M.elems fundefs)
            let (ddefs', fundef', fieldorder) =
                  optimizeFunctionWRTDataCon ddefs fundef dcon
            let fundefs' = M.delete (toVar funcName) fundefs
            let fundefs'' = M.insert (toVar funcName) fundef' fundefs'
            let venv = progToVEnv prg
            let pmap = generateProducerGraph prg
            let p = prg {ddefs = ddefs', fundefs = fundefs'', mainExp = mainExp}
            let prg' =
                  genNewProducersAndRewriteProgram
                    (toVar funcName)
                    (dcon ++ "tmp")
                    fieldorder
                    venv
                    pmap
                    p
            generateCopyFunctionsForFunctionsThatUseOptimizedVariable (toVar funcName) (dcon ++ "tmp") fieldorder prg'
      _ -> error "OptimizeFieldOrder: handle use constraints"


generateCopyFunctionsForFunctionsThatUseOptimizedVariable :: Var -> DataCon -> FieldOrder -> Prog1 -> PassM Prog1
generateCopyFunctionsForFunctionsThatUseOptimizedVariable funcName newDconName fieldOrder prg@Prog{ddefs, fundefs, mainExp} = case mainExp of
                                                                                                                                      Nothing -> error "no main exp in generateCopyFunctionsForFunctionsThatUseOptimizedVariable."
                                                                                                                                      Just (expr, ty) -> let generatedVars = S.toList $ S.fromList $ getGeneratedVariable expr
                                                                                                                                                          in case generatedVars of
                                                                                                                                                                    [v] -> do  let funcsUsingVar = findFunctionsUsingVar v expr
                                                                                                                                                                               fundefs' <- makeFunctionCopies funcsUsingVar ddefs fundefs
                                                                                                                                                                               let exp' = P.foldr (\func ex -> replaceFunctionName func (toVar (fromVar func ++ "_new")) ex ) expr funcsUsingVar
                                                                                                                                                                               pure prg {ddefs = ddefs, fundefs = fundefs', mainExp = Just (exp', ty)}
                                                                                                                                                                    [] -> error "generateCopyFunctionsForFunctionsThatUseOptimizedVariable: no variables found"
                                                                                                                                                                    _ -> error "generateCopyFunctionsForFunctionsThatUseOptimizedVariable: handle multiple produced variables"
  where
    getGeneratedVariable exp = case exp of
          DataConE loc dcon args -> P.concatMap getGeneratedVariable args
          VarE {} -> []
          LitE {} -> []
          CharE {} -> []
          FloatE {} -> []
          LitSymE {} -> []
          AppE f locs args -> P.concatMap getGeneratedVariable args
          PrimAppE f args -> P.concatMap getGeneratedVariable args
          LetE (v, loc, ty, rhs) bod -> case rhs of
                                              AppE f' _ _ -> if f' == funcName then [v] ++ getGeneratedVariable rhs ++ getGeneratedVariable bod
                                                             else getGeneratedVariable rhs ++ getGeneratedVariable bod
                                              _ -> getGeneratedVariable rhs ++ getGeneratedVariable bod
          CaseE scrt mp -> P.concatMap (\(_, _, c) -> getGeneratedVariable c ) mp
          IfE a b c -> getGeneratedVariable a ++ getGeneratedVariable b ++ getGeneratedVariable c
          MkProdE xs -> P.concatMap getGeneratedVariable xs
          ProjE i e -> error "getGeneratedVariable: TODO ProjE"
          TimeIt e ty b -> error "getGeneratedVariable: TODO TimeIt"
          WithArenaE v e -> error "getGeneratedVariable: TODO WithArenaE"
          SpawnE f locs args -> error "getGeneratedVariable: TODO SpawnE"
          SyncE -> error "getGeneratedVariable: TODO SyncE"
          Ext _ -> error "getGeneratedVariable: TODO Ext"
          MapE {} -> error "getGeneratedVariable: TODO MapE"
          FoldE {} -> error "getGeneratedVariable: TODO FoldE"

    replaceFunctionName oldName newName expr = case expr of
          DataConE loc dcon args -> DataConE loc dcon $ P.map (replaceFunctionName oldName newName) args
          VarE {} -> expr
          LitE {} -> expr
          CharE {} -> expr
          FloatE {} -> expr
          LitSymE {} -> expr
          AppE f locs args -> if f == oldName then AppE newName locs $ P.map (replaceFunctionName oldName newName) args
                              else AppE f locs $ P.map (replaceFunctionName oldName newName) args
          PrimAppE f args -> PrimAppE f $ P.map (replaceFunctionName oldName newName) args
          LetE (v, loc, ty, rhs) bod -> LetE (v, loc, ty, replaceFunctionName oldName newName rhs) (replaceFunctionName oldName newName bod)
          CaseE scrt mp -> let mp' = P.map (\(a, b, c) -> (a, b, replaceFunctionName oldName newName c)) mp
                             in CaseE scrt mp'
          IfE a b c -> IfE (replaceFunctionName oldName newName a) (replaceFunctionName oldName newName b) (replaceFunctionName oldName newName c)
          MkProdE xs -> MkProdE $ P.map (replaceFunctionName oldName newName) xs
          ProjE i e -> error "replaceFunctionName: TODO ProjE"
          TimeIt e ty b -> error "replaceFunctionName: TODO TimeIt"
          WithArenaE v e -> error "replaceFunctionName: TODO WithArenaE"
          SpawnE f locs args -> error "replaceFunctionName: TODO SpawnE"
          SyncE -> error "replaceFunctionName: TODO SyncE"
          Ext _ -> error "replaceFunctionName: TODO Ext"
          MapE {} -> error "replaceFunctionName: TODO MapE"
          FoldE {} -> error "replaceFunctionName: TODO FoldE"

    findFunctionsUsingVar var expr = case expr of
          DataConE loc dcon args -> P.concatMap (findFunctionsUsingVar var) args
          VarE {} -> []
          LitE {} -> []
          CharE {} -> []
          FloatE {} -> []
          LitSymE {} -> []
          AppE f locs args -> let freeVars = S.unions $ P.map gFreeVars args
                               in if S.member var freeVars
                                  then f : P.concatMap (findFunctionsUsingVar var) args
                                  else P.concatMap (findFunctionsUsingVar var) args
          PrimAppE f args -> P.concatMap (findFunctionsUsingVar var) args
          LetE (v, loc, ty, rhs) bod -> findFunctionsUsingVar var rhs ++ findFunctionsUsingVar var bod
          CaseE scrt mp -> P.concatMap (\(_, _, c) -> findFunctionsUsingVar var c) mp
          IfE a b c -> findFunctionsUsingVar var a ++  findFunctionsUsingVar var b ++ findFunctionsUsingVar var c
          MkProdE xs -> P.concatMap (findFunctionsUsingVar var) xs
          ProjE i e -> error "findFunctionsUsingVar: TODO ProjE"
          TimeIt e ty b -> error "findFunctionsUsingVar: TODO TimeIt"
          WithArenaE v e -> error "findFunctionsUsingVar: TODO WithArenaE"
          SpawnE f locs args -> error "findFunctionsUsingVar: TODO SpawnE"
          SyncE -> error "findFunctionsUsingVar: TODO SyncE"
          Ext _ -> error "findFunctionsUsingVar: TODO Ext"
          MapE {} -> error "findFunctionsUsingVar: TODO MapE"
          FoldE {} -> error "findFunctionsUsingVar: TODO FoldE"

    makeFunctionCopies funcList ddefs' fdefs = case funcList of
                                                  [] -> pure fdefs
                                                  x:xs -> if not $ isInfixOf "_print" (fromVar x)
                                                          then
                                                            let newFunctionName = toVar (fromVar x ++ "_new")
                                                                oldFunctionBody = M.lookup x fdefs
                                                              in case oldFunctionBody of
                                                                        Just body -> let newFunctionBody = shuffleDataConFunBody fieldOrder body newDconName
                                                                                         newFunctionBody' = changeCallNameInRecFunction newFunctionName newFunctionBody
                                                                                         var_order = getVarsBoundByDconInOrder' newDconName newFunctionBody' -- Get Variables bound by DataCon so that we release let bings in the right order. 
                                                                                         --TODO: fix this is not right
                                                                                         -- I would say better to remove all let binds
                                                                                         -- use gFreeVars to release binds. 
                                                                                         var_order' = P.map Just var_order
                                                                                         var_order'' = P.zip var_order' var_order
                                                                                         newFunctionBody''@FunDef{funName} = P.foldl (\fundef (insertPosition, var') -> reOrderLetExp insertPosition var' fundef) newFunctionBody' var_order''
                                                                                         fdefs' = M.insert funName newFunctionBody'' fdefs
                                                                                       in makeFunctionCopies xs ddefs' fdefs'
                                                                        Nothing -> error ""
                                                          else
                                                            do 
                                                              let flds = snd $ lkp ddefs' newDconName  
                                                              newPrintCase <- genPrintFnCase flds
                                                              let fn = M.lookup x fdefs 
                                                              case fn of 
                                                                  Just ff@FunDef{funName, funBody, funTy, funArgs, funMeta} -> let exp' = addCaseForNewDataConInPrintFn [newPrintCase] funBody
                                                                                                                                   fn'  = FunDef{funName=funName, funBody=exp', funTy=funTy, funArgs=funArgs, funMeta=funMeta} 
                                                                                                                                   newFunctionName = toVar (fromVar x ++ "_new")
                                                                                                                                   newFunctionBody' = changeCallNameInRecFunction newFunctionName fn'
                                                                                                                                   fdefs' = M.insert newFunctionName newFunctionBody' fdefs 
                                                                                                                                  in makeFunctionCopies xs ddefs' fdefs'

                                                                                                                           
                                                                  Nothing -> error ""  
                                                              
                                                              

    addCaseForNewDataConInPrintFn newCase expr = case expr of 
          DataConE loc dcon args -> DataConE loc dcon $ P.map (addCaseForNewDataConInPrintFn newCase) args  
          VarE {} -> expr 
          LitE {} -> expr 
          CharE {} -> expr
          FloatE {} -> expr
          LitSymE {} -> expr
          AppE f locs args -> AppE f locs $ P.map (addCaseForNewDataConInPrintFn newCase) args
          PrimAppE f args -> PrimAppE f $ P.map (addCaseForNewDataConInPrintFn newCase) args
          LetE (v, loc, ty, rhs) bod -> let rhs' = addCaseForNewDataConInPrintFn newCase rhs 
                                            bod' = addCaseForNewDataConInPrintFn newCase bod 
                                          in LetE (v, loc, ty, rhs') bod'
          CaseE scrt mp -> let mp' = mp ++ newCase
                            in CaseE scrt mp'
          IfE a b c -> IfE (addCaseForNewDataConInPrintFn newCase a) (addCaseForNewDataConInPrintFn newCase b) (addCaseForNewDataConInPrintFn newCase c)  
          MkProdE xs -> MkProdE $ P.map (addCaseForNewDataConInPrintFn newCase) xs
          ProjE i e -> error "findFunctionsUsingVar: TODO ProjE"
          TimeIt e ty b -> error "findFunctionsUsingVar: TODO TimeIt"
          WithArenaE v e -> error "findFunctionsUsingVar: TODO WithArenaE"
          SpawnE f locs args -> error "findFunctionsUsingVar: TODO SpawnE"
          SyncE -> error "findFunctionsUsingVar: TODO SyncE"
          Ext _ -> error "findFunctionsUsingVar: TODO Ext"
          MapE {} -> error "findFunctionsUsingVar: TODO MapE"
          FoldE {} -> error "findFunctionsUsingVar: TODO FoldE"





optimizeFunctionWRTDataCon ::
  DDefs1 ->
  FunDef1 ->
  DataCon ->
  (DDefs1, FunDef1, FieldOrder)
optimizeFunctionWRTDataCon
  ddefs
  fundef@FunDef
    { funName,
      funBody,
      funTy,
      funArgs
    }
  datacon =
    let cfg = getFunctionCFG fundef
        fieldMap = generateAccessGraphs cfg M.empty fundef [datacon]
        field_len = P.length $ snd . snd $ lkp' ddefs datacon
        fieldorder =
          optimizeDataConOrderFunc
            fieldMap
            M.empty
            fundef
            [(datacon, field_len)]
            M.empty
        -- make a function to generate a new data con as a value instead of changing the order of fields in the original one.
        [(dcon, order)] = M.toList fieldorder
        (newDDefs, newDcon) = optimizeDataCon (dcon, order) ddefs
        fundef' = shuffleDataConFunBody fieldorder fundef newDcon
     in (newDDefs, fundef', fieldorder)

changeCallNameInRecFunction ::
  Var -> FunDef1 -> FunDef1
changeCallNameInRecFunction
  newFunName
  f@FunDef
    { funName,
      funArgs,
      funTy,
      funBody,
      funMeta
    } =
    case funMeta of
      FunMeta {funRec} ->
        case funRec of
          Rec ->
            f
              { funName = newFunName,
                funArgs = funArgs,
                funTy = funTy,
                funBody = fixExp funBody,
                funMeta
              }
          _ ->
            f
              { funName = newFunName,
                funArgs = funArgs,
                funTy = funTy,
                funBody = funBody,
                funMeta
              }
    where
      fixExp funBody =
        case funBody of
          DataConE loc dcon args -> DataConE loc dcon (P.map fixExp args)
          VarE {} -> funBody
          LitE {} -> funBody
          CharE {} -> funBody
          FloatE {} -> funBody
          LitSymE {} -> funBody
          AppE f locs args ->
            if f == funName
              then AppE newFunName locs (P.map fixExp args)
              else AppE f locs (P.map fixExp args)
          PrimAppE f args -> PrimAppE f (P.map fixExp args)
          LetE (v, loc, ty, rhs) bod ->
            let rhs' = fixExp rhs
                bod' = fixExp bod
             in LetE (v, loc, ty, rhs') bod'
          CaseE scrt mp ->
            let mp' = P.map (\(a, b, c) -> (a, b, fixExp c)) mp
             in CaseE scrt mp'
          IfE a b c -> IfE (fixExp a) (fixExp b) (fixExp c)
          MkProdE xs -> MkProdE (P.map fixExp xs)
          ProjE i e -> error "getExpTyEnv: TODO ProjE"
          TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
          WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
          SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
          SyncE -> error "getExpTyEnv: TODO SyncE"
          Ext _ -> error "getExpTyEnv: TODO Ext"
          MapE {} -> error "getExpTyEnv: TODO MapE"
          FoldE {} -> error "getExpTyEnv: TODO FoldE"

genNewProducersAndRewriteProgram ::
  Var ->
  DataCon ->
  FieldOrder ->
  Env2 Ty1 ->
  ProducersMap Exp1 ->
  Prog Exp1 ->
  Prog Exp1
genNewProducersAndRewriteProgram
  funName
  newDataConName
  newdataConOrder
  venv
  pmap
  prg@Prog
    { ddefs,
      fundefs,
      mainExp
    } =
    case mainExp of
      Nothing ->
        error "genNewProducersAndRewriteProgram : Program has no main expression."
      Just (mexp, ty) ->
        let variablesAndProducers = getVariableAndProducer funName pmap venv ddefs newDataConName mexp
         in case variablesAndProducers of
              [] -> error "no variable and producers found to modify"
              [(var, producer)] ->
                let newProducerName = toVar (fromVar producer ++ "_new")
                    oldProducerBody = M.lookup producer fundefs
                 in case oldProducerBody of
                      Just body ->
                        let newProducerBody@FunDef
                              { funName,
                                funBody,
                                funTy,
                                funArgs
                              } =
                                shuffleDataConFunBody
                                  newdataConOrder
                                  body
                                  newDataConName
                            newProducerBody' =
                              changeCallNameInRecFunction
                                newProducerName
                                newProducerBody
                            var_order = getVarsBoundByDconInOrder' newDataConName newProducerBody' -- Get Variables bound by DataCon so that we release let bings in the right order. 
                            var_order' = P.map Just var_order
                            var_order'' = P.zip var_order' var_order
                            newProducerBody'' = P.foldl (\fundef (insertPosition, var') -> reOrderLetExp insertPosition var' fundef) newProducerBody' var_order''
                            fundefs' =
                              M.insert newProducerName newProducerBody'' fundefs
                            newMainExp =
                              callNewProducerForVarInMain
                                var
                                False
                                producer
                                newProducerName
                                mexp
                         in prg
                              { ddefs = ddefs,
                                fundefs = fundefs',
                                mainExp = Just (newMainExp, ty)
                              }
                      _ -> error ""
              x : xs -> error "more than one variable and producer not handled yet."

-- Function to find the the variable/s that have the type that's being optimized for the given function f
-- Also return the producer of those variable/s
-- Arguments
-- Var -> Name of the function being optimized
-- pmap -> variable to producer map
-- (PreExp e l d) -> expression to search over
-- Return
-- [(Var, Producer)]
getVariableAndProducer ::
  Var ->
  ProducersMap Exp1 ->
  Env2 Ty1 ->
  DDefs1 ->
  DataCon ->
  Exp1 ->
  [(Var, Var)]
getVariableAndProducer funName pMap venv@Env2{vEnv, fEnv} ddefs dconName exp =
  case exp of
    DataConE loc dcon args ->
      P.concatMap (getVariableAndProducer funName pMap venv ddefs dconName) args
    VarE {} -> []
    LitE {} -> []
    CharE {} -> []
    FloatE {} -> []
    LitSymE {} -> []
    AppE f locs args ->
      P.concatMap (getVariableAndProducer funName pMap venv ddefs dconName) args
    PrimAppE f args ->
      P.concatMap (getVariableAndProducer funName pMap venv ddefs dconName) args
    LetE (v, loc, ty, rhs) bod ->
      let varOf =
            case rhs of
              AppE f locs args ->
                if f == funName
                  then
                    let potentialVarsOfTy =
                          P.map
                            ( \exp ->
                                case exp of
                                  VarE v ->
                                    case lookupVEnv' v venv of
                                      Just e -> let tyCon = getTyOfDataCon ddefs dconName
                                                    urtyTyCon = PackedTy tyCon ()
                                                  in if e == urtyTyCon then Just v
                                                     else Nothing
                                      Nothing -> Nothing
                                  _ -> Nothing
                            )
                            args
                        justVariables = Maybe.catMaybes potentialVarsOfTy
                     in if P.null justVariables
                          then error "getVariableAndProducer: no variables of Ty to optimize found!"
                          else
                            if P.length justVariables > 1
                              then error "getVariableAndProducer: More than one variable of the type being optimized is passed to function call. Not implemented yet!"
                              else Just (P.head justVariables)
                  else Nothing
              _ -> Nothing
          producers =
            getVariableAndProducer funName pMap venv ddefs dconName rhs
              ++ getVariableAndProducer funName pMap venv ddefs dconName bod
       in case varOf of
            Just var ->
              let varType = lookupVEnv' var venv
               in case varType of
                    Just ty ->
                      let producerExp = M.lookup (var, ty) pMap
                       in case producerExp of
                            Just (AppE f locs args) -> (var, f) : producers
                            _ ->
                              error
                                "getVariableAndProducer: producer other than a function call not expected."
                    Nothing -> []
            Nothing -> producers
    -- a == DataCon
    -- b == [(Var, loc)]
    -- c == Case Body
    CaseE scrt mp ->
      P.concatMap (\(a, b, c) -> getVariableAndProducer funName pMap venv ddefs dconName c) mp
    IfE a b c ->
      let producersA = getVariableAndProducer funName pMap venv ddefs dconName a
          producersB = getVariableAndProducer funName pMap venv ddefs dconName b
          producersC = getVariableAndProducer funName pMap venv ddefs dconName c
       in producersA ++ producersB ++ producersC
    MkProdE xs -> P.concatMap (getVariableAndProducer funName pMap venv ddefs dconName) xs
    ProjE i e -> error "getExpTyEnv: TODO ProjE"
    TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
    WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
    SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
    SyncE -> error "getExpTyEnv: TODO SyncE"
    Ext _ -> error "getExpTyEnv: TODO Ext"
    MapE {} -> error "getExpTyEnv: TODO MapE"
    FoldE {} -> error "getExpTyEnv: TODO FoldE"

-- For a variable that's produced change the old producer to the new producer.
-- Args
-- Var  -> Variable whose producer needs to be changed
-- Bool -> a switch for modifying the call or not.
-- Var  -> Name of the old producer
-- Var  -> Name of the new producer
-- (PreExp e l d) -> Main Expression
-- Return value
-- (PreExp e l d) -> New Main Expression
callNewProducerForVarInMain ::
  Var -> Bool -> Var -> Var -> Exp1 -> Exp1
callNewProducerForVarInMain var boolModify oldProducer newProducer mainExp =
  case mainExp of
    DataConE loc dcon args ->
      let args' =
            P.map
              ( callNewProducerForVarInMain
                  var
                  boolModify
                  oldProducer
                  newProducer
              )
              args
       in DataConE loc dcon args'
    VarE {} -> mainExp
    LitE {} -> mainExp
    CharE {} -> mainExp
    FloatE {} -> mainExp
    LitSymE {} -> mainExp
    AppE f locs args ->
      let args' =
            P.map
              ( callNewProducerForVarInMain
                  var
                  boolModify
                  oldProducer
                  newProducer
              )
              args
       in if f == oldProducer && boolModify
            then AppE newProducer locs args'
            else AppE f locs args'
    PrimAppE f args ->
      let args' =
            P.map
              ( callNewProducerForVarInMain
                  var
                  boolModify
                  oldProducer
                  newProducer
              )
              args
       in PrimAppE f args'
    LetE (v, loc, ty, rhs) bod ->
      let rhs' =
            if v == var
              then
                callNewProducerForVarInMain
                  var
                  True
                  oldProducer
                  newProducer
                  rhs
              else
                callNewProducerForVarInMain
                  var
                  False
                  oldProducer
                  newProducer
                  rhs
          bod' =
            callNewProducerForVarInMain
              var
              boolModify
              oldProducer
              newProducer
              bod
       in LetE (v, loc, ty, rhs') bod'
    -- a == DataCon
    -- b == [(Var, loc)]
    -- c == Case Body
    CaseE scrt mp ->
      let mp' =
            P.map
              ( \(a, b, c) ->
                  let c' =
                        callNewProducerForVarInMain
                          var
                          boolModify
                          oldProducer
                          newProducer
                          c
                   in (a, b, c')
              )
              mp
       in CaseE scrt mp'
    IfE a b c ->
      let a' =
            callNewProducerForVarInMain var boolModify oldProducer newProducer a
          b' =
            callNewProducerForVarInMain var boolModify oldProducer newProducer b
          c' =
            callNewProducerForVarInMain var boolModify oldProducer newProducer c
       in IfE a' b' c'
    MkProdE xs ->
      let xs' =
            P.map
              ( callNewProducerForVarInMain
                  var
                  boolModify
                  oldProducer
                  newProducer
              )
              xs
       in MkProdE xs'
    ProjE i e -> error "getExpTyEnv: TODO ProjE"
    TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
    WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
    SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
    SyncE -> error "getExpTyEnv: TODO SyncE"
    Ext _ -> error "getExpTyEnv: TODO Ext"
    MapE {} -> error "getExpTyEnv: TODO MapE"
    FoldE {} -> error "getExpTyEnv: TODO FoldE"

genEdgesFromTotalOrdering ::
  [(String, DataConMap)] -> [FunDef1] -> FieldMap -> FieldMap
genEdgesFromTotalOrdering lstTotalOrdering fundefs mapIn =
  case lstTotalOrdering of
    [] -> mapIn
    x : xs ->
      let (funcName, map) = x
          [fundef@(FunDef {funName})] =
            concatMap ( \fn@(FunDef {funName}) ->
                    ([fn | fromVar funName == funcName])
                ) fundefs
          dconOrderings = M.toList map
          dconOrderings' =
            P.map
              ( \(dcon, strongOrderings) ->
                  let edges =
                        P.map
                          ( \(Strong a b) -> ((a, b), P.toInteger (100 :: Integer))
                          )
                          strongOrderings
                   in (dcon, edges)
              )
              dconOrderings
          orderMap = M.fromList dconOrderings'
          newMap = M.insert funName orderMap mapIn
          newMap' = genEdgesFromTotalOrdering xs fundefs newMap
       in newMap'

existsTuple :: [(String, a)] -> String -> Bool
existsTuple lst name =
  case lst of
    [] -> False
    (x, y) : xs ->
      x == name || existsTuple xs name

-- This just goes through the function we are locally optimizing
-- Since this problem is to locally optimize for a particular function right now we are not concerned with finding the best
-- optimal layout for the complete program.
locallyOptimizeFieldOrdering ::
  FieldMap ->
  [DataCon] ->
  [FunDef1] ->
  String ->
  Int ->
  FieldOrder ->
  Int ->
  FieldOrder
locallyOptimizeFieldOrdering fieldMap dcons fundefs funcName field_len orderIn mode =
  case fundefs of
    [] -> orderIn
    x : xs ->
      let map' =
            generateLocallyOptimalOrderings
              fieldMap
              dcons
              x
              funcName
              field_len
              orderIn
              mode
          map'' =
            locallyOptimizeFieldOrdering
              fieldMap
              dcons
              xs
              funcName
              field_len
              map'
              mode
       in map''


genUserConstrs :: [UserOrdering] -> [Constr]
genUserConstrs userOrdering =
  case userOrdering of
    (Strong a b) : xs -> Absolute (a, b) : genUserConstrs xs
    (Immediate a b) : xs -> Imm (a, b) : genUserConstrs xs
    [] -> []

-- Takes in Field access map
-- Takes in user constraints for data con for that function
-- takes in the function def for the function
-- Takes in [(DataCon, Int)], ie, data con name, and number of fields for data constructors that need to be optimized
-- Returns optimal order of fields of a data constructor.

-- Timing for filtering the blogs based on a keyword
timeSolver ::
  (IO [(Int, Int)] -> [(Int, Int)]) ->
  IO [(Int, Int)] ->
  IO ([(Int, Int)], Double)
timeSolver f f' = do
  t1 <- getCurrentTime
  a <- evaluate (f f')
  t2 <- getCurrentTime
  let delt = fromRational (toRational (diffUTCTime t2 t1))
  --putStrLn ("iter time: " ++ show delt)
  return (a, delt)

optimizeDataConOrderFunc ::
  FieldMap ->
  DataConMap ->
  FunDef1 ->
  [(DataCon, Int)] ->
  FieldOrder ->
  FieldOrder
optimizeDataConOrderFunc
  dconAccessMap
  dconUserConstr
  fundef@FunDef
    { funName,
      funBody,
      funTy,
      funArgs
    }
  datacons
  orderIn =
    let lstDconEdges = M.findWithDefault M.empty funName dconAccessMap
     in case datacons of
          [] -> orderIn
          [(x, field_len)] ->
            let softEdges = M.findWithDefault [] x lstDconEdges
                softConstrs = P.map Soft softEdges
                userOrdering = M.findWithDefault [] x dconUserConstr
                userConstrs = genUserConstrs userOrdering
                allConstrs = softConstrs ++ userConstrs
             in -- field_len    = P.length $ snd . snd $ lkp ddefs x
                case allConstrs of
                  [] -> orderIn
                  _ ->
                    let (layout, t) =
                          U.unsafePerformIO $
                            timeSolver U.unsafePerformIO (solveConstrs allConstrs)
                        -- In case we don't get orderings for some of the fields in the data con
                        -- to be safe we should complete the layout orderings of the missing fields.
                        fix_missing =
                          if P.length layout < field_len
                            then
                              let indices = [0 .. (field_len - 1)]
                                  minuslist = makeneg field_len
                                  partial = fillList minuslist layout
                                  avail = P.map fst layout
                                  navail = deleteMany avail indices
                                  new = fillminus1 partial navail
                               in new
                            else
                              let layout' = L.sort layout
                               in P.map snd layout'
                        fieldorder = M.insert x (integerList fix_missing) orderIn
                     in fieldorder
          _ ->
            error
              "OptimizeFieldOrder: optimizeDataConOrderFunc more that one data constructor per function not implemented yet."

-- for the function for which we are locally optimizing for, find the optimal layout of the data constructors that we care about.
-- "Locally optimizing for the function"
generateLocallyOptimalOrderings ::
  FieldMap ->
  [DataCon] ->
  FunDef1 ->
  String ->
  Int ->
  FieldOrder ->
  Int ->
  FieldOrder
generateLocallyOptimalOrderings
  fieldMap
  datacons
  fundef@FunDef
    { funName,
      funBody,
      funTy,
      funArgs
    }
  funcName
  field_len
  orderIn
  mode =
    if fromVar funName == funcName
      then
        let lstDconEdges = M.findWithDefault M.empty funName fieldMap
         in case datacons of
              [] -> orderIn
              x : xs ->
                let dconEdges = M.findWithDefault [] x lstDconEdges
                    dconEdges' = P.map Soft dconEdges
                 in case dconEdges' of
                      [] -> orderIn
                      _ ->
                        let layout =
                              U.unsafePerformIO (solveConstrs dconEdges')
                            -- In case we don't get orderings for some of the fields in the data con
                            -- to be safe we should complete the layout orderings of the missing fields.
                            fix_missing =
                              if P.length layout < field_len
                                then
                                  let indices = [0 .. (field_len - 1)]
                                      minuslist = makeneg field_len
                                      partial = fillList minuslist layout
                                      avail = P.map fst layout
                                      navail = deleteMany avail indices
                                      new = fillminus1 partial navail
                                   in new
                                else
                                  let layout' = L.sort layout
                                   in P.map snd layout'
                            fieldorder =
                              M.insert x (integerList fix_missing) orderIn
                            fieldorder' =
                              generateLocallyOptimalOrderings
                                fieldMap
                                xs
                                fundef
                                funcName
                                field_len
                                fieldorder
                                mode
                         in fieldorder'
      else orderIn

makeneg :: Int -> [Int]
makeneg len =
  if len <= 0
    then []
    else makeneg (len - 1) ++ [-1]

integerList :: [Int] -> [Integer]
integerList lst =
  case lst of
    [] -> []
    x : xs -> P.toInteger x : integerList xs

fillList :: [Int] -> [(Int, Int)] -> [Int]
fillList old vals =
  case vals of
    [] -> old
    x : xs ->
      let (a, b) = x
          edited = L.take b old ++ [a] ++ L.drop (b + 1) old
       in fillList edited xs

-- https://www.reddit.com/r/haskell/comments/u841av/trying_to_remove_all_the_elements_that_occur_in/
deleteOne :: (Eq a) => a -> [a] -> [a]
deleteOne _ [] = [] -- Nothing to delete
deleteOne x (y : ys)
  | x == y = ys -- Drop exactly one matching item
deleteOne x (y : ys) = y : deleteOne x ys -- Drop one, but not this one (doesn't match).

deleteMany :: (Eq a) => [a] -> [a] -> [a]
deleteMany [] = id -- Nothing to delete
deleteMany (x : xs) = deleteMany xs . deleteOne x -- Delete one, then the rest.

fillminus1 :: [Int] -> [Int] -> [Int]
fillminus1 lst indices =
  case lst of
    [] -> []
    x : xs ->
      case indices of
        [] -> lst
        y : ys ->
          if x == -1
            then y : fillminus1 xs ys
            else x : fillminus1 xs indices

shuffleDataConFunBody ::
  FieldOrder -> FunDef1 -> DataCon -> FunDef1
shuffleDataConFunBody fieldorder f@FunDef {funBody} newDataCon =
  let funBody' = shuffleDataConExp fieldorder newDataCon funBody
   in f {funBody = funBody'}

shuffleDataConExp :: FieldOrder -> DataCon -> Exp1 -> Exp1
shuffleDataConExp fieldorder newDataCon ex =
  case ex of
    DataConE loc dcon args ->
      let args' = shuffleDataConArgs fieldorder dcon args
          newCon =
            if M.member dcon fieldorder
              then newDataCon
              else dcon
       in DataConE loc newCon args'
    VarE {} -> ex
    LitE {} -> ex
    CharE {} -> ex
    FloatE {} -> ex
    LitSymE {} -> ex
    AppE f locs args ->
      AppE f locs (P.map (shuffleDataConExp fieldorder newDataCon) args)
    PrimAppE f args ->
      PrimAppE f (P.map (shuffleDataConExp fieldorder newDataCon) args)
    LetE (v, loc, ty, rhs) bod ->
      let rhs' = shuffleDataConExp fieldorder newDataCon rhs
          bod' = shuffleDataConExp fieldorder newDataCon bod
       in LetE (v, loc, ty, rhs') bod'
    IfE a b c ->
      let a' = shuffleDataConExp fieldorder newDataCon a
          b' = shuffleDataConExp fieldorder newDataCon b
          c' = shuffleDataConExp fieldorder newDataCon c
       in IfE a' b' c'
    MkProdE xs -> MkProdE (P.map (shuffleDataConExp fieldorder newDataCon) xs)
    ProjE i e -> ProjE i (shuffleDataConExp fieldorder newDataCon e)
    CaseE scrt mp ->
      let mp' =
            P.map
              ( \(a, b, c) ->
                  let b' = shuffleDataConCase fieldorder a b
                      c' = shuffleDataConExp fieldorder newDataCon c
                      a' =
                        if M.member a fieldorder
                          then newDataCon
                          else a
                   in (a', b', c')
              )
              mp
       in CaseE scrt mp'
    TimeIt e ty b ->
      let e' = shuffleDataConExp fieldorder newDataCon e
       in TimeIt e' ty b
    WithArenaE v e ->
      let e' = shuffleDataConExp fieldorder newDataCon e
       in WithArenaE v e'
    SpawnE f locs args ->
      SpawnE f locs (P.map (shuffleDataConExp fieldorder newDataCon) args)
    SyncE -> SyncE
    Ext _ -> ex
    MapE {} -> error "shuffleFieldOrdering: TODO MapE"
    FoldE {} -> error "shuffleFieldOrdering: TODO FoldE"

shuffleDataConArgs ::
  FieldOrder -> DataCon -> [Exp1] -> [Exp1]
shuffleDataConArgs fieldorder dcon exps =
  if M.member dcon fieldorder
    then permute (findWithDefault [] dcon fieldorder) exps
    else exps

shuffleDataConCase :: FieldOrder -> DataCon -> [(Var, loc)] -> [(Var, loc)]
shuffleDataConCase fieldorder dcon vs =
  if M.member dcon fieldorder
    then permute (findWithDefault [] dcon fieldorder) vs
    else vs


optimizeDataCon ::
  (DataCon, [Integer]) ->
  DDefs1 ->
  (DDefs1, DataCon)
optimizeDataCon (dcon, newindices) ddefs =
  let (tycon, (_, fields)) = lkp' ddefs dcon
      newFields = permute newindices fields
      newDcon = dcon ++ "tmp" -- TODO: Change this to use gensym
      DDef {tyName, tyArgs, dataCons} = lookupDDef' ddefs (fromVar tycon)
      newDDef =
        DDef
          { tyName = tyName,
            tyArgs = tyArgs,
            dataCons = dataCons ++ [(newDcon, newFields)]
          }
      ddefs' = M.delete tycon ddefs
      ddefs'' = insertDD newDDef ddefs'
   in (ddefs'', newDcon)

-- | Lookup a Datacon.  Return (TyCon, (DataCon, [flds]))
lkp' ::
  DDefs1 ->
  DataCon ->
  (Var, (DataCon, [(IsBoxed, UrTy())]))
lkp' dds con =
  -- Here we try to lookup in ALL datatypes, assuming unique datacons:
  case [ (tycon, variant)
         | (tycon, DDef {dataCons}) <- M.toList dds,
           variant <- L.filter ((== con) . fst) dataCons
       ] of
    [] ->
      error "OptimizeFieldOrder -> lookupDataCon: could not find constructor!"
    [hit] -> hit
    _ ->
      error "OptimizeFieldOrder -> lookupDataCon: found multiple occurences of constructor!"

-- | Lookup a ddef in its entirety
lookupDDef' ::
  DDefs1 -> TyCon -> DDef1
lookupDDef' mp tycon =
  case M.lookup (toVar tycon) mp of
    Just x -> x
    Nothing -> error "OptimizeFieldOrder: lookupDDef' failed!"

permute :: [Integer] -> [a] -> [a]
permute indices list =
  case indices of
    [] -> []
    x : xs -> (list !! P.fromInteger x) : permute xs list



getVarsBoundByDconInOrder' :: DataCon -> FunDef1 -> [Var]
getVarsBoundByDconInOrder' datacon f@FunDef{funName, funBody, funTy, funArgs, funMeta} = getVarsBoundByDconInOrder datacon funBody

-- Only works assuming you have just one data constructor in the function body.  
getVarsBoundByDconInOrder :: DataCon -> Exp1 -> [Var]
getVarsBoundByDconInOrder datacon expr = case expr of
          DataConE _ dcon args -> if dcon == datacon then
                                                       P.concatMap (\expr' -> case expr' of
                                                                                VarE v -> [v]
                                                                                LitSymE v -> [v]
                                                                                _ -> []
                                                                   ) args
                                    else []
          VarE {} -> []
          LitE {} -> []
          CharE {} -> []
          FloatE {} -> []
          LitSymE {} -> []
          AppE _ _ args -> P.concatMap (getVarsBoundByDconInOrder datacon) args
          PrimAppE _ args -> P.concatMap (getVarsBoundByDconInOrder datacon) args
          LetE (v, loc, ty, rhs) bod -> let vars  = getVarsBoundByDconInOrder datacon rhs
                                            vars' = getVarsBoundByDconInOrder datacon bod
                                          in vars ++ vars'
          CaseE scrt mp -> P.concatMap (\(a, b, c) -> getVarsBoundByDconInOrder datacon c) mp
          IfE a b c -> let varsa = getVarsBoundByDconInOrder datacon a
                           varsb = getVarsBoundByDconInOrder datacon b
                           varsc = getVarsBoundByDconInOrder datacon c
                         in varsa ++ varsb ++ varsc
          MkProdE xs -> P.concatMap (getVarsBoundByDconInOrder datacon) xs
          ProjE i e -> error "getExpTyEnv: TODO ProjE"
          TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
          WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
          SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
          SyncE -> error "getExpTyEnv: TODO SyncE"
          Ext _ -> error "getExpTyEnv: TODO Ext"
          MapE {} -> error "getExpTyEnv: TODO MapE"
          FoldE {} -> error "getExpTyEnv: TODO FoldE"



reOrderLetExp :: Maybe Var -> Var -> FunDef1 -> FunDef1
reOrderLetExp after curr f@FunDef{funName, funBody, funTy, funArgs, funMeta} = let (m :: UseDefChainsFunctionMap Exp1) = getDefinitionsReachingLetExp f
                                                                                 in case M.lookup funName m of
                                                                                  Just (graph, getNode, getVertex) -> let lambda = (\var -> let vertex = getVertex var
                                                                                                                                        in case vertex of
                                                                                                                                                Just v -> let ((vv, ex, ty), key, successors::[Var]) = getNode v
                                                                                                                                                            in (successors, Just ex)
                                                                                                                                                Nothing -> ([], Nothing)                                                                                                                                       )
                                                                                                                          lambda' = (\varList -> case varList of
                                                                                                                                                [] -> []
                                                                                                                                                x:xs -> let (successors, ex) = lambda x
                                                                                                                                                            recurseSucc = lambda' successors
                                                                                                                                                            recurseRst  = lambda' xs
                                                                                                                                                         in case ex of
                                                                                                                                                                Just ex' -> recurseSucc ++ recurseRst ++ [ex']
                                                                                                                                                                Nothing  -> recurseSucc ++ recurseRst
                                                                                                                                        )
                                                                                                                          letExpOrder = lambda' [curr]
                                                                                                                          funBody' =  P.foldr delLetBinding funBody letExpOrder
                                                                                                                          funBody'' = reOrderLetExpHelper after letExpOrder funBody'
                                                                                                                        in FunDef{funName=funName, funBody=funBody'', funTy=funTy, funArgs=funArgs, funMeta=funMeta}
                                                                                  Nothing -> error "reOrderLetExp: could not find data flow relation for let expressions."


reOrderLetExpHelper :: Maybe Var -> [Exp1] -> Exp1 -> Exp1
reOrderLetExpHelper Nothing letExpOrder expr = case letExpOrder of
  [] -> expr
  x:xs -> case x of
            LetE (v, loc, ty, rhs) _ -> let exp' = LetE (v, loc, ty, rhs) $ reOrderLetExpHelper Nothing xs expr
                                          in exp'
            _ -> error "reOrderLetExpHelper: did not expect expressions other than LetE."

-- reOrderLetExpHelper Nothing letExpOrder expr = let 

--   case expr of
--           DataConE loc dcon args -> 
--           VarE {} -> 
--           LitE {} -> 
--           CharE {} -> 
--           FloatE {} -> 
--           LitSymE {} -> 
--           AppE f locs args -> 
--           PrimAppE f args -> 
--           LetE (v, loc, ty, rhs) bod -> 
--           CaseE scrt mp -> 
--           IfE a b c -> 
--           MkProdE xs -> 
--           ProjE {} -> error "reOrderLetExpHelper: TODO ProjE"
--           TimeIt {} -> error "reOrderLetExpHelper: TODO TimeIt"
--           WithArenaE {} -> error "reOrderLetExpHelper: TODO WithArenaE"
--           SpawnE {} -> error "reOrderLetExpHelper: TODO SpawnE"
--           SyncE -> error "reOrderLetExpHelper: TODO SyncE"
--           Ext {} -> error "reOrderLetExpHelper: TODO Ext"
--           MapE {} -> error "reOrderLetExpHelper: TODO MapE"
--           FoldE {} -> error "reOrderLetExpHelper: TODO FoldE"

-- reOrderLetExpHelper insertAfter@(Just var) letExpOrder expr = case expr of
--           DataConE loc dcon args -> DataConE loc dcon $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           VarE {} -> expr
--           LitE {} -> expr
--           CharE {} -> expr
--           FloatE {} -> expr
--           LitSymE {} -> expr
--           AppE f locs args -> AppE f locs $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           PrimAppE f args -> PrimAppE f $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           LetE (v, loc, ty, rhs) bod -> if v == var
--                                         then
--                                           let lambda = (\l ex -> case l of
--                                                                           LetE (v', loc', ty', rhs') _ -> LetE (v', loc', ty', rhs') ex
--                                                                           _ -> error "reOrderLetExpHelper: did not expect expressions other than LetE.")
--                                               exp' = P.foldr lambda bod letExpOrder
--                                             in LetE (v, loc, ty, rhs) exp'
--                                         else
--                                           LetE (v, loc, ty, reOrderLetExpHelper insertAfter letExpOrder rhs) (reOrderLetExpHelper insertAfter letExpOrder bod)
--           CaseE scrt mp -> CaseE scrt $ P.map (\(a, b, c) -> (a, b, reOrderLetExpHelper insertAfter letExpOrder c)) mp
--           IfE a b c -> IfE (reOrderLetExpHelper insertAfter letExpOrder a) (reOrderLetExpHelper insertAfter letExpOrder b) (reOrderLetExpHelper insertAfter letExpOrder c)
--           MkProdE xs -> MkProdE $ P.map (reOrderLetExpHelper insertAfter letExpOrder) xs
--           ProjE {} -> error "reOrderLetExpHelper: TODO ProjE"
--           TimeIt {} -> error "reOrderLetExpHelper: TODO TimeIt"
--           WithArenaE {} -> error "reOrderLetExpHelper: TODO WithArenaE"
--           SpawnE {} -> error "reOrderLetExpHelper: TODO SpawnE"
--           SyncE -> error "reOrderLetExpHelper: TODO SyncE"
--           Ext {} -> error "reOrderLetExpHelper: TODO Ext"
--           MapE {} -> error "reOrderLetExpHelper: TODO MapE"
--           FoldE {} -> error "reOrderLetExpHelper: TODO FoldE"

-- TODO: This will release bindings multiple times for variables use everywhere, whreas we want to just prioritize for first use. 
-- Simple solution is to refactor this into a new function and return a bool when the binds have been released.  
-- check if binds have been released, if pass [] as let binds. 
-- reOrderLetExpHelper insertAfter@(Just var) letExpOrder expr = case expr of
--           DataConE loc dcon args -> DataConE loc dcon $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           VarE vv -> if vv == var
--                      then
--                       let lambda = (\l ex -> case l of
--                                                 LetE (v', loc', ty', rhs') _ -> LetE (v', loc', ty', rhs') ex
--                                                 _ -> error "reOrderLetExpHelper: did not expect expressions other than LetE.")
--                           exp' = P.foldr lambda expr letExpOrder
--                         in exp'
--                      else
--                       expr
--           LitE {} -> expr
--           CharE {} -> expr
--           FloatE {} -> expr
--           LitSymE {} -> expr
--           AppE f locs args -> AppE f locs $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           PrimAppE f args -> PrimAppE f $ P.map (reOrderLetExpHelper insertAfter letExpOrder) args
--           LetE (v, loc, ty, rhs) bod -> LetE (v, loc, ty, reOrderLetExpHelper insertAfter letExpOrder rhs) (reOrderLetExpHelper insertAfter letExpOrder bod)
--           CaseE scrt mp -> CaseE scrt $ P.map (\(a, b, c) -> (a, b, reOrderLetExpHelper insertAfter letExpOrder c)) mp
--           IfE a b c -> IfE (reOrderLetExpHelper insertAfter letExpOrder a) (reOrderLetExpHelper insertAfter letExpOrder b) (reOrderLetExpHelper insertAfter letExpOrder c)
--           MkProdE xs -> MkProdE $ P.map (reOrderLetExpHelper insertAfter letExpOrder) xs
--           ProjE {} -> error "reOrderLetExpHelper: TODO ProjE"
--           TimeIt {} -> error "reOrderLetExpHelper: TODO TimeIt"
--           WithArenaE {} -> error "reOrderLetExpHelper: TODO WithArenaE"
--           SpawnE {} -> error "reOrderLetExpHelper: TODO SpawnE"
--           SyncE -> error "reOrderLetExpHelper: TODO SyncE"
--           Ext {} -> error "reOrderLetExpHelper: TODO Ext"
--           MapE {} -> error "reOrderLetExpHelper: TODO MapE"
--           FoldE {} -> error "reOrderLetExpHelper: TODO FoldE"

reOrderLetExpHelper bindsForVar@(Just var) letExpOrder expr = fst $ run letExpOrder expr
  where
  lambdaHandleExpList expList letExpOrder' = case expList of
                                        [] -> ([], False)
                                        x:xs -> let (exp', releasedBinds) = run letExpOrder' x
                                                  in if releasedBinds
                                                     then (exp' : xs, releasedBinds)
                                                     else
                                                       let (exp'', val) = lambdaHandleExpList xs letExpOrder'
                                                         in (exp' : exp'', releasedBinds || val)

  lambdaAppendLets = \l ex -> case l of
                                LetE (v', loc', ty', rhs') _ -> LetE (v', loc', ty', rhs') ex
                                _ -> error "reOrderLetExpHelper(run): did not expect expressions other than LetE."

  run letExpOrder' expr' = case expr' of
          DataConE loc dcon args -> let (newArgs :: [PreExp E1Ext () Ty1], releasedBinds) = lambdaHandleExpList args letExpOrder'
                                      in (DataConE loc dcon newArgs, releasedBinds)
          VarE vv -> if vv == var
                     then
                        let exp' = P.foldr lambdaAppendLets expr' letExpOrder'
                          in (exp', True)
                     else
                      (expr', False)
          LitE {} -> (expr', False)
          CharE {} -> (expr', False)
          FloatE {} -> (expr', False)
          LitSymE {} -> (expr', False)
          AppE f locs args -> let (newArgs, releasedBinds) = lambdaHandleExpList args letExpOrder'
                               in (AppE f locs newArgs, releasedBinds)
          PrimAppE f args -> let (newArgs, releasedBinds) = lambdaHandleExpList args letExpOrder'
                               in (PrimAppE f newArgs, releasedBinds)
          LetE (v, loc, ty, rhs) bod -> let (rhs', relRhs) = run letExpOrder' rhs
                                            (bod', relBod) = if relRhs then (bod, relRhs) else run letExpOrder' bod
                                          in
                                            (LetE (v, loc, ty, rhs') bod' , relRhs || relBod)
          --TODO: if it exits in more than one case then lift releasing bindings on top of case.                                  
          CaseE scrt mp -> let lambdaCase = (\(a, b, c) -> let (c' , released') = run letExpOrder' c
                                                             in ((a, b, c'), released')
                                            )
                               newExps = P.map lambdaCase mp
                               mp' = P.map fst newExps
                               released = any snd newExps
                             in (CaseE scrt mp', released)
          -- IfE a b c -> let (a', rela) = run letExpOrder' a
          --                  (b', relb) = if rela then (b, rela) else run letExpOrder' b 
          --                  (c', relc) = if rela || relb then (c, rela || relb) else run letExpOrder' c 
          --                in (IfE a' b' c', rela || relb || relc)
          IfE a b c -> let freeVarsA = gFreeVars a
                           freeVarsB = gFreeVars b
                           freeVarsC = gFreeVars c
                          in if S.member var freeVarsA || S.member var freeVarsC && S.member var freeVarsB
                             then (P.foldr lambdaAppendLets expr' letExpOrder', True)
                             else if S.member var freeVarsB && S.notMember var freeVarsC
                             then let b' = fst $ run letExpOrder' b
                                   in (IfE a b' c, True)
                             else if S.member var freeVarsC && S.notMember var freeVarsB
                             then let c' = fst $ run letExpOrder' c
                                    in (IfE a b c', True)
                             else
                                (expr', False)
          MkProdE xs -> let (xs', releasedBinds) = lambdaHandleExpList xs letExpOrder'
                          in (MkProdE xs', releasedBinds)
          ProjE {} -> error "reOrderLetExpHelper: TODO ProjE"
          TimeIt {} -> error "reOrderLetExpHelper: TODO TimeIt"
          WithArenaE {} -> error "reOrderLetExpHelper: TODO WithArenaE"
          SpawnE {} -> error "reOrderLetExpHelper: TODO SpawnE"
          SyncE -> error "reOrderLetExpHelper: TODO SyncE"
          Ext {} -> error "reOrderLetExpHelper: TODO Ext"
          MapE {} -> error "reOrderLetExpHelper: TODO MapE"
          FoldE {} -> error "reOrderLetExpHelper: TODO FoldE"

delLetBinding :: Exp1 -> Exp1 -> Exp1
delLetBinding letBind expr = case expr of
          DataConE loc dcon args -> DataConE loc dcon $ P.map (delLetBinding letBind) args
          VarE {} -> expr
          LitE {} -> expr
          CharE {} -> expr
          FloatE {} -> expr
          LitSymE {} -> expr
          AppE f locs args -> AppE f locs $ P.map (delLetBinding letBind) args
          PrimAppE f args -> PrimAppE f $ P.map (delLetBinding letBind) args
          LetE (v, loc, ty, rhs) bod -> case letBind of
                                              LetE (v', _, _, _) _ -> if v == v' then bod
                                                                              else LetE (v, loc, ty, delLetBinding letBind rhs) $ delLetBinding letBind bod
                                              _ -> error "delLetBinding: did not expect an expression other than let."
          CaseE scrt mp -> CaseE scrt $ P.map (\(a, b, c) -> (a, b, delLetBinding letBind c)) mp
          IfE a b c -> IfE (delLetBinding letBind a) (delLetBinding letBind b) (delLetBinding letBind c)
          MkProdE xs -> MkProdE $ P.map (delLetBinding letBind) xs
          ProjE {} -> error "delLetBinding: TODO ProjE"
          TimeIt {} -> error "delLetBinding: TODO TimeIt"
          WithArenaE {} -> error "delLetBinding: TODO WithArenaE"
          SpawnE {} -> error "delLetBinding: TODO SpawnE"
          SyncE -> error "delLetBinding: TODO SyncE"
          Ext{} -> error "delLetBinding: TODO Ext"
          MapE {} -> error "delLetBinding: TODO MapE"
          FoldE {} -> error "delLetBinding: TODO FoldE"
















-- reorderExpByVariablesBoundByDataCon :: DataCon -> FunDef1 -> [[Exp1]]
-- reorderExpByVariablesBoundByDataCon dcon fundef@FunDef{funName,funBody,funTy,funArgs} initialEnv = let 
--                                                                                                      dconVars = getVarsBoundByDconInOrder dcon funBody 
--                                                                                                      exps     = P.map (\var -> getBoundExpsVar var funBody []) dconVars
--                                                                                                     in exps   



-- getBoundExpsVar :: Var -> Exp1 -> S.Set Exp1 -> [Exp1]
-- getBoundExpsVar var exp liveExpressions = case exp of 
--           DataConE loc dcon args -> P.concatMap (\ex -> getBoundExpsVar var ex liveExpressions) args
--           VarE {} -> []
--           LitE {} -> []
--           CharE {} -> []
--           FloatE {} -> []
--           LitSymE {} -> []
--           AppE f locs args -> P.concatMap (\ex -> getBoundExpsVar var ex liveExpressions) args
--           PrimAppE f args -> P.concatMap (\ex -> getBoundExpsVar var ex liveExpressions) args
--           LetE (v, loc, ty, rhs) bod -> if v == var 
--                                         then let freeExprs = gFreeVars rhs 
--                                                  releaseBinds = P.map (\var -> P.map (\exp -> case exp of 
--                                                                                                     LetE (v', _, _, _) b -> if v' == var then [exp]
--                                                                                                                             else []
--                                                                                      ) S.toList liveExpressions
--                                                                       ) S.toList freeExprs

--           CaseE scrt mp -> 
--           IfE a b c -> 
--           MkProdE xs -> 
--           ProjE i e -> error "getExpTyEnv: TODO ProjE"
--           TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
--           WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
--           SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
--           SyncE -> error "getExpTyEnv: TODO SyncE"
--           Ext _ -> error "getExpTyEnv: TODO Ext"
--           MapE {} -> error "getExpTyEnv: TODO MapE"
--           FoldE {} -> error "getExpTyEnv: TODO FoldE"


genPrintFnCase ::  (DataCon, [(IsBoxed, Ty1)]) -> PassM (DataCon, [(Var, ())], PreExp E1Ext () Ty1)
genPrintFnCase (dcon, tys) = do
      xs <- mapM (\_ -> gensym "x") tys
      ys <- mapM (\_ -> gensym "y") tys
      let bnds =
            P.foldr
              (\(ty, x, y) acc ->
                 case ty of
                   IntTy -> (y, [], ProdTy [], PrimAppE PrintInt [VarE x]) : acc
                   FloatTy ->
                     (y, [], ProdTy [], PrimAppE PrintFloat [VarE x]) : acc
                   SymTy ->
                     (y, [], ProdTy [], PrimAppE PrintSym [VarE x]) : acc
                   BoolTy ->
                     (y, [], ProdTy [], PrimAppE PrintBool [VarE x]) : acc
                   PackedTy tycon _ ->
                     (y, [], ProdTy [], AppE (mkPrinterName tycon) [] [VarE x]) :
                     acc
                   SymDictTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "SymDict")]) :
                     acc
                   VectorTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "Vector")]) :
                     acc
                   PDictTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "PDict")]) :
                     acc
                   ListTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "List")]) :
                     acc
                   ArenaTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "Arena")]) :
                     acc
                   SymSetTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "SymSet")]) :
                     acc
                   SymHashTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "SymHash")]) :
                     acc
                   IntHashTy {} ->
                     ( y
                     , []
                     , ProdTy []
                     , PrimAppE PrintSym [LitSymE (toVar "IntHash")]) :
                     acc
                   _ -> acc)
              []
              (zip3 (P.map snd tys) xs ys)
      w1 <- gensym "wildcard"
      w2 <- gensym "wildcard"
      let add_spaces ::
               [(Var, [()], Ty1, PreExp E1Ext () Ty1)]
            -> PassM [(Var, [()], Ty1, PreExp E1Ext () Ty1)]
          add_spaces [] = pure []
          add_spaces [z] = pure [z]
          add_spaces (z:zs) = do
            zs' <- add_spaces zs
            wi <- gensym "wildcard"
            pure $
              z :
              (wi, [], ProdTy [], PrimAppE PrintSym [(LitSymE (toVar " "))]) :
              zs'
      bnds'' <-
        add_spaces $
        [ ( w1
          , []
          , ProdTy []
          , PrimAppE PrintSym [(LitSymE (toVar ("(" ++ dcon)))])
        ] ++
        bnds
      let bnds' =
            bnds'' ++
            [(w2, [], ProdTy [], PrimAppE PrintSym [(LitSymE (toVar ")"))])]
          bod = mkLets' bnds' (MkProdE [])
      return (dcon, P.map (\x -> (x, ())) xs, bod)

mkLets' ::
     [(Var, [()], Ty1, PreExp E1Ext () Ty1)]
  -> Exp1
  -> Exp1
mkLets' [] bod     = bod
mkLets' (b:bs) bod = LetE b (mkLets' bs bod)