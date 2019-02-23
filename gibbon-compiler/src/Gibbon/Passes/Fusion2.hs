{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-all #-}

module Gibbon.Passes.Fusion2 (fusion2) where
import Prelude hiding (exp)

import Control.Exception
import Data.Loc
import qualified Data.Map as M
import qualified Data.List as L
import qualified  Data.Set as S
import qualified Data.Vector as V
import Data.Symbol
import Data.Char ( toLower )
import Gibbon.L1.Syntax as L1
import Debug.Trace
import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Gibbon.Common
import Data.Tuple.All
import Data.Vector as V
import Control.Monad

-- this can be made faster --- we are rushing though
removeCommonExpressions::  L Exp1->  L Exp1
removeCommonExpressions exp = rec  exp 
   where 
    rec exp  = case (getExp exp) of
      LetE (v, ls, t, bind) body ->
        let oldExp = bind
            newExp = l $ VarE v
            body' = substE oldExp newExp body --`debug` ("removing duplicates of "L.++ (show oldExp))
        in l$ LetE (v, ls, t, bind) (rec body') 

      IfE cond thenBody elseBody -> 
        l $ IfE (rec cond) (rec thenBody) (rec elseBody)
      
      CaseE e ls      -> let ls' = L.map (\(x, y, exp) -> (x, y, rec exp)) ls
          in  l$ CaseE e ls'    
       
      TimeIt exp x y  ->l $   TimeIt (rec exp) x y 
      x       -> l $x
        

replaceLeafWithBind:: L Exp1-> Var -> Ty1 -> L Exp1 -> L Exp1
replaceLeafWithBind exp newVar varType tailExp =
  rec exp 
   where 
     rec ex = case (getExp ex) of 
          L1.LetE (v,ls,t, e1) e2 -> l $ L1.LetE (v,ls,t, e1)  (rec e2)
          x ->   l $L1.LetE (newVar,[],varType, l (x)) tailExp
  
freshExp :: [(Var,Var)] -> L Exp1 -> PassM (L L1.Exp1)
freshExp vs (L sloc exp) = fmap (L sloc) $
    case exp of
        L1.Ext _     -> return exp
        L1.LitE i    -> return $ L1.LitE i
        L1.LitSymE v -> return $ L1.LitSymE v
        L1.VarE v ->case lookup v vs of
            Nothing -> return $ L1.VarE v
            Just v' -> return $ L1.VarE v'

        L1.AppE v ls e -> assert ([] == ls) $ do
            e' <- freshExp vs e
            return $ L1.AppE (cleanFunName v) [] e'

        L1.PrimAppE p es -> do
            es' <- Prelude.mapM (freshExp vs) es
            return $ L1.PrimAppE p es'

        L1.LetE (v,ls,t, e1) e2 -> assert ([]==ls) $ do
            e1' <- freshExp vs e1
            v'  <- gensym v
            e2' <- freshExp ((v,v'):vs) e2
            return $ L1.LetE (v',[],t,e1') e2'

        L1.IfE e1 e2 e3 -> do
            e1' <- freshExp vs e1
            e2' <- freshExp vs e2
            e3' <- freshExp vs e3
            return $ L1.IfE e1' e2' e3'

        L1.ProjE i e -> do
            e' <- freshExp vs e
            return $ L1.ProjE i e'

        L1.MkProdE es -> do
            es' <- Prelude.mapM (freshExp vs) es
            return $ L1.MkProdE es'

        L1.CaseE e mp -> do
            e' <- freshExp vs e
            -- Here we freshen locations:
            mp' <- Prelude.mapM (\(c,prs,ae) ->
                  let (args,_) = Prelude.unzip prs in
                      do
                        args' <- Prelude.mapM gensym args
                        let vs' = (Prelude.zip args args') L.++ vs
                        ae' <- freshExp vs' ae
                        return (c, L.map (,( )) args', ae')) mp
            return $ L1.CaseE e' mp'

        L1.DataConE () c es -> do
            es' <- Prelude.mapM (freshExp vs) es
            return $ L1.DataConE () c es'

        L1.TimeIt e t b -> do
            e' <- freshExp vs e
            return $ L1.TimeIt e' t b

        L1.MapE (v,t,b) e -> do
            b' <- freshExp vs b
            e' <- freshExp vs e
            return $ L1.MapE (v,t,b') e'

        L1.FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
            e1' <- freshExp vs e1
            e2' <- freshExp vs e2
            e3' <- freshExp vs e3
            return $ L1.FoldE (v1,t1,e1') (v2,t2,e2') e3'

debug = flip trace
getExp:: L Exp1-> Exp1 
getExp  (L  _ exp) = exp

data DefTableEntry = DefTableEntry 
  { def :: !Exp1 -- ^ defining expression 
{- each entry consist of
    1)The function application expression.
    2)The index at which the definition  appears at in the argument list.  
    3)The defined symbol, if the the consuming expression of the form let x=App.
-}
  , fun_uses :: ![(Exp1,Int,Maybe Symbol)] 
  , all_use_count:: !Int -- ^ total number of uses (calls and not calls)
  } deriving (Show , Generic)
  
type DefTable = M.Map Symbol DefTableEntry 
type PotentialPair = (Symbol, Symbol)
type PotentialsList = [DefTableEntry] 

{- 
This functions collect the following information for each defined variable: 
  1) The defining expression. (stored in DefTableEntry::def)
  2) The consumer of the definition that are candidates for fusion;the function
  is consumed in the first argument. (stored in DefTableEntry::fun_uses)
  not: uses mutual exclusive paths are counted by adding them (each is 
  considered  a use).
  3) Total number of uses (references) of the defined variable.
-} 
buildDefTable:: Exp1 -> DefTable
buildDefTable ex  = rec ex Nothing M.empty 
 where 
  rec ex definingSymbol table = case (ex) of
    VarE (Var sym) ->  M.update incrUses sym table     
    
    LetE ((Var symLet),_,_,bind) body ->
      let table' = M.insert symLet (DefTableEntry {def=(getExp bind),
                    fun_uses=[], all_use_count = 0} ) table
          table'' = rec (getExp bind) (Just symLet) table'
      in rec (getExp body) definingSymbol table''

    callExp@( AppE fName _ args) -> 
      -- add function uses of interest
      --[functions calls traversing tree in first argument]
      let table' = case (getExp args) of 
            VarE (Var sym) ->  M.update (addFunctionUse (callExp,-1,
                   definingSymbol)) sym table
            MkProdE ((L _ (VarE (Var sym) )):tail) -> M.update (addFunctionUse
             (callExp, 0, definingSymbol)) sym table
            _   -> table
            
      in rec (getExp args) Nothing table'  
       where 
        addFunctionUse newUse ( DefTableEntry  def fun_uses c )=  
          Just $ DefTableEntry def (newUse:fun_uses) (c) 
    
    MkProdE argsList -> buildDefTable_args  argsList table
        where
          buildDefTable_args [] tb  = tb
          buildDefTable_args  (h:tail)  table  = buildDefTable_args
            tail (rec (getExp h) Nothing table)

    PrimAppE _ ls ->  L.foldl f table ls
            where  f tbl exp = rec (getExp exp) Nothing tbl
 
    IfE cond thenBody elseBody      -> let table' = rec (getExp cond) Nothing table 
        in let table'' = rec ( getExp thenBody) definingSymbol table'
        in rec (getExp elseBody) definingSymbol table''
    
    CaseE e ls      ->
        let table' = rec (getExp e) Nothing table 
        in L.foldl f table' ls
      where
        f tbl (_, _, exp) = rec (getExp exp) definingSymbol tbl
   
    DataConE _ _ ls -> L.foldl f table ls
     where 
       f tbl exp = rec (getExp exp) Nothing tbl
    TimeIt exp _ _  -> rec (getExp exp) definingSymbol table   
    ProjE index exp -> rec (getExp exp) Nothing table 
    LitE _ -> table
    x       -> table `debug`( "\nPlease handle:" L.++ ( show x) L.++ "in buildDefTable\n")
   where 
      incrUses (DefTableEntry  def fun_uses c) = Just $
          DefTableEntry def fun_uses (c+1)

extractAppNameFromLet ::  Exp1 -> Var
extractAppNameFromLet (LetE ((Var symLet),_,_,L _ (AppE var _ _ )) _)  = var

extractLetSymbolFromLet ::  Exp1 -> Symbol
extractLetSymbolFromLet (LetE ((Var symLet),_,_,L _ (AppE var _ _ )) _)  = symLet

extractAppEName ::  Exp1 -> Var
extractAppEName (AppE var _ _ ) = var
extractAppEName  x = error(show x)


-- returns ((innerFun, outerFun), symbol defined by the outer)
findPotential :: DefTable -> [(Var, Var)] -> Maybe ((Var, Var), Maybe Symbol)
findPotential table skipList = 
  ( case (L.find predicate  (M.toList table)) of
    Nothing       -> Nothing --`debug`  (show skipList) 
    Just (_, (DefTableEntry def fun_uses use_count ) ) -> 
        Just ( ( (extractAppEName def),
                 (extractAppEName(sel1 (L.head fun_uses)))), 
                   (sel3 (L.head fun_uses)) ) )
   where 
    predicate (_,DefTableEntry def fun_uses use_count )  = case (def) of 
      AppE var _ _  -> (L.length fun_uses >= 1) && (L.notElem (extractAppEName
         def, extractAppEName(sel1 (L.head fun_uses))) skipList) 
      _ -> False
      
      
isPotential :: DefTable -> Maybe Symbol -> [(Var, Var)] -> Bool
isPotential table symbol skipList =
  case symbol of 
    Nothing -> False
    Just symb ->  
      case (  table  M.!? symb) of
         Nothing       -> False --`debug`  (show skipList) 
         Just (DefTableEntry def fun_uses use_count)  ->
             (L.length fun_uses == 1) && (L.notElem  ((extractAppEName def),
                (extractAppEName(sel1 (L.head fun_uses))) ) skipList )
 
{-Note** The type of the new function is defined as the following :
let innerType = TreeX Args1...RetType1
let outerType = RetType Args2 RetType2

inlinedType = fusedType = ProdTy[ TreeX Args1 Args2] -> RetType2 
-}
inline :: FunDef1 -> FunDef1 -> Int  ->  PassM FunDef1
inline inlined_fun outer_fun arg_pos  =  do 
  newArgVar <- gensym(toVar("inputTree"))

  let argType_outer = fst (funTy outer_fun)
      retType_outer = snd (funTy outer_fun)
      argVar_outer = funArg outer_fun
      argType_inlined= fst (funTy inlined_fun)
      argVar_inlined = funArg inlined_fun

  -- get it as item in list
  let traversedTypeInner = case (argType_inlined) of
        ProdTy (h:_) -> h:[]
        exp@(PackedTy _ _) -> exp:[]
        _ -> error ("not expected type")

  let sideArgsTypesInlined = getSideArgsTypes argType_outer
      sidArgsTypesOuter    = getSideArgsTypes argType_inlined
  
  let newType = (ProdTy (traversedTypeInner L.++ sideArgsTypesInlined L.++ 
        sidArgsTypesOuter), retType_outer)
  let inlinedFunBody = case (argType_inlined) of
        PackedTy _ _ -> let oldExp  = l $ VarE argVar_inlined
                            newExp  = l $ ProjE 0 (l (VarE newArgVar) )
                    in substE oldExp newExp (funBody inlined_fun) 
        ProdTy ls  ->
           let argsLength = L.length ls
           in loop 0 argsLength (funBody inlined_fun)
            where loop i n exp =  if(i==n)
                    then 
                      exp
                    else
                     loop (i+1) n (replaceProj i argVar_inlined i newArgVar exp) 
  let outerFunBody = case(argType_outer) of
        PackedTy _ _ -> funBody outer_fun
        ProdTy ls  ->
           let argsLength =  L.length ls
               shift' = L.length (getSideArgsTypes (argType_inlined))
           in loop 1 argsLength (funBody outer_fun) shift'
            where loop i n exp shift = if(i==n)
                   then 
                     exp 
                   else
                     loop (i+1) n (replaceProj i argVar_outer (i+shift)
                         newArgVar exp) shift     
  let newBody = 
        let oldExp = l $ case (argType_outer) of 
              ProdTy _    ->  ProjE 0 (l (VarE argVar_outer) )
              _             ->  VarE argVar_outer
        in substE oldExp inlinedFunBody outerFunBody

  return outer_fun { funArg  = newArgVar, 
                     funTy = newType,
                     funBody = newBody
                    }
 where
  getSideArgsTypes (ProdTy (h:tail)) = tail
  getSideArgsTypes _  = []
  replaceProj i1 argVar1 i2 argvar2 exp= 
    let oldExp = l $ ProjE i1 (l (VarE argVar1))
        newExp = l $ ProjE i2 (l (VarE argvar2))
    in substE oldExp newExp exp
  
inlineArgumentProjections :: FunDef1 -> FunDef1
inlineArgumentProjections function = case (fst(funTy function)) of
    ProdTy _->   function {funBody = rec (funBody function)}
      where 
        rec (L l ex)  = case  ex of
          LetE (v,loc,t,rhs) body -> 
              case (getExp rhs) of
                proj@(ProjE i (L _ (VarE v1))) -> 
                  if (v1 == (funArg function))
                    then 
                      let oldEx  =  L l $ VarE v
                          newExp =  L l $ proj
                      in substE oldEx newExp (rec body)
                    else
                     L l $ LetE (v,loc,t,(rec rhs)) (rec body)
                _ -> 
                    L l $LetE (v,loc,t,(rec rhs)) (rec body)
          CaseE e1 ls1  -> 
               L l$ CaseE e1 (L.map f ls1) 
             where 
               f (dataCon, x, exp) = (dataCon, x, rec exp)
          AppE v loc e             ->  L l $ AppE v loc $ rec e
          IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)
          TimeIt e d b             ->  L l $ TimeIt ( rec e) d b 
          _                        -> L l ex

    _ -> function

simplifyCases :: FunDef1 -> FunDef1
simplifyCases function = function {funBody = rec ( funBody function) }
  where
    rec (L l ex)  = case  ex of

      CaseE e1@(L l (CaseE e2 ls2)) ls1 -> rec $ L l $ CaseE e2 (L.map f ls2)
        where 
          f oldItem = (upd3 newMember oldItem)  
            where 
              newMember = L l (CaseE (sel3 oldItem) ls1)
                  
      CaseE e1@(L l (DataConE loc k ls)) ls1 -> 
        let newBody = L.find predicate ls1 
             where 
              predicate item = if(sel1 item == k) then True else False
              in case newBody of 
                Nothing -> error "unmatched construcotor!"
                Just (k, vars, exp)  -> rec $case_subst ls vars exp
                  where 
                    case_subst (x1:l1) (x2:l2) exp = subst (fst x2) 
                      ( x1)(case_subst l1 l2 exp)
                    case_subst [] [] exp = exp
        
      CaseE (L l' (IfE e1 e2 e3) ) ls          -> rec $ 
        L l (IfE e1 ( L l' $CaseE e2 ls) ( L l' $CaseE e3 ls) )         
      CaseE e1@(L l' (LetE bind body )  ) ls1  -> L l' $ 
        LetE bind (rec $ L l $ CaseE body (ls1) )
      CaseE e1 ls1                              ->  L l$ CaseE e1 (L.map f ls1) 
        where 
          f item = (upd3 (rec (sel3 item)) item)   
      LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (rec rhs)) (rec bod)  
      AppE v loc e             ->  L l $ AppE v loc $ rec e
      IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)
      TimeIt e d b             ->  L l $ TimeIt ( rec e) d b 
      _                        -> L l ex


foldFusedCalls_f :: (Var, Var, Int, Var) -> FunDef1 -> FunDef1
foldFusedCalls_f rule function = function{funBody= 
  foldFusedCalls rule (funBody function)}

-- check note** just above the inline function 
foldFusedCalls :: (Var, Var, Int,Var ) -> L Exp1  ->(L Exp1) 
foldFusedCalls rule@(outerName, innerName, argPos, newName) body = 
  let defTable = buildDefTable (getExp body)  
  in let rec (L l ex ) = case (ex) of 
          AppE fName loc argList -> 
            let notFolded = L l $ AppE fName loc (rec argList) 
            in if(fName ==  outerName) 
                then 
                  case (getExp argList ) of 
                    VarE (Var symInner) -> 
                      if(innerName == getDefiningFunction symInner defTable)  
                        then 
                            let innerArgs = getArgs  symInner defTable
                            in let outerArgs =   [argList]
                               in let newCallArgs= L l (MkProdE (innerArgs 
                                        L.++ (L.drop 1 outerArgs)))
                                  in L l  $AppE  newName loc newCallArgs
                        else notFolded 
                   
                    MkProdE ls@(L _ (VarE (Var sym)):tail)->  
                      if(innerName == getDefiningFunction sym defTable)  
                        then 
                          let innerArgs = getArgs sym defTable
                          in let outerArgs =  ls
                              in let newCallArgs= L l( MkProdE (innerArgs 
                                             L.++ (L.drop 1 outerArgs)))
                                 in L l  $AppE  newName loc newCallArgs
                        else notFolded 
                    _ -> notFolded 
             
                else
                  notFolded 
             
                      
          LetE (v,loc,t,lhs) bod   ->  L l $ LetE (v,loc,t, (rec lhs)) (rec bod) 
          IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)     
          CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1)
            where
              f (dataCon,x,exp) = (dataCon, x, (rec exp)) 
          TimeIt e d b             ->  L l $ TimeIt ( rec e) d b
          DataConE loc datacons ls ->  L l $ DataConE loc datacons 
            (L.map (\x-> rec x) ls)
          otherwise -> L l ex 

  in rec body
      where
        getDefiningFunction x defTable = case (M.lookup x defTable) of
            Nothing    -> (toVar "-1not-used-vars")
            Just entry -> case (def  entry) of 
                  AppE v _ _   -> v
                  _            -> (toVar "-1not-used-var") 
        getArgs x defTable = case (M.lookup x defTable) of
             Nothing    -> error  "error in foldFusedCalls"
             Just entry -> case (def  entry) of 
                  AppE _ _ args-> case ( getExp (args)) of
                      MkProdE ls -> ls
                      x          -> [l x]              
                  _            -> error  ("ops" L.++ (show(def  entry)))

-- foldTupledFunctions_f :: ( FunDef1) ->[Var] ->PassM (FunDef1)
-- foldTupledFunctions_f funDef ls =
--   do 
--     body <- (foldTupledFunctions (funBody funDef ) funDef ls )
--     return funDef {funBody =body}

foldTupledFunctions ::   L Exp1 -> (FunDef1) -> [Exp1] -> Exp1 -> PassM (L Exp1)
foldTupledFunctions body newFun oldCalls firstCall = 
  do
     newVar <- gensym (toVar ("tupled_output"))
     x <- (rec  body  newVar) 
     return x 
  where
    rec (L l ex) newVar =  do
      case (ex) of 
        LetE (Var y, loc, t, rhs) body ->
          do
            case (L.elemIndex (getExp rhs) oldCalls) of 
              Nothing ->
                do 
                  rhs' <- (rec rhs newVar)
                  body' <- (rec body newVar)
                  return ( L l $ LetE (Var y, loc, t, rhs')  body' )
              Just i ->  
              
                do
                  if (firstCall == (getExp rhs))
                    then
                      do
                        body' <- rec body newVar
                        let args = L.foldl f [] oldCalls
                             where 
                              f ls1 exp = ls1 L.++ (extractArgs exp)
                              extractArgs exp = case exp of
                                 AppE _ _  args-> 
                                    case (getExp args) of
                                       MkProdE (h:tail) -> tail 
                        let args' = L l $ MkProdE ((getFirstArg rhs):args)
                             where 
                              getFirstArg (L _ ( AppE _ _ (L _  (MkProdE (h:_)))))= h

                        let rhs' = L l $AppE (funName newFun) [] args'
                        let bindType = (outTy (funTy newFun))
                        let rhs'' =  L l $ ProjE i (L l $ VarE newVar)
                        let body'' =  L l $ LetE (Var y, loc, t, rhs'') body'
                        return ( L l $LetE (newVar, [], bindType, rhs') body'') 
                    else
                      do
                        body' <- ( rec body newVar) --`debug` ("\nhere\n")
                        let rhs' =  L l $ ProjE i (L l $ VarE newVar)
                        return( L l $ LetE (Var y, loc, t, rhs') body')

        AppE name loc e          -> do
             e'<- (rec e newVar)
             return $ L l $ AppE name loc   e'
        PrimAppE x ls            -> do 
            ls' <- (Prelude.mapM (\item -> (rec item newVar)) ls)
            return $ L l $ PrimAppE x ls'
       
        LetE (v,loc,t,rhs) bod   -> do 
            body' <- (rec bod newVar)
            rhs' <- (rec rhs newVar)
            return $L l $LetE (v,loc,t, rhs') body'  
        IfE e1 e2 e3             -> do 
          e1' <- (rec e1 newVar)
          e2' <- (rec e2 newVar)
          e3' <- (rec e3 newVar)
          return$ L l $ IfE e1' e2' e3'
       
        MkProdE ls               -> do 
          ls' <- (Prelude.mapM (\item -> (rec item newVar)) ls)
          return $  L l $ MkProdE ls' 
        ProjE index exp          -> do 
          exp' <- (rec exp newVar)
          return $ L l $ ProjE index exp' 
        CaseE e1 ls1 ->  do
          e1' <- ( rec e1  newVar)
          ls' <- (Prelude.mapM (\(dataCon,x,exp)->
            do 
              exp' <- (rec exp newVar)
              return (dataCon, x, exp')  
              ) ls1)
          return  $ L l $ CaseE e1'  ls'
         
               
        DataConE loc datacons ls -> do
          ls' <- (Prelude.mapM (\x-> (rec x newVar)) ls)
          return $ L l $ DataConE loc datacons ls'
        TimeIt e d b             -> do 
          e'<-  rec e newVar
          return $L l $ TimeIt e'  d b 
        otherwise                -> do 
          return $ L l ex
      
removeUnusedDefs :: FunDef1 -> FunDef1
removeUnusedDefs f = f{funBody = removeUnusedDefs_exp (funBody f)}

removeUnusedDefs_exp :: L Exp1 ->  L Exp1 
removeUnusedDefs_exp exp =
  let defTable = buildDefTable (getExp exp)  
  in rec exp defTable
    where
      rec (L l ex) dTable = case ex of 
        LetE (Var s,loc,t,rhs) bod   -> case (M.lookup s dTable ) of
          Nothing ->L l $ LetE (Var s,loc,t, (rec rhs dTable)) (rec bod dTable)  
          Just ( DefTableEntry _ _ 0) -> (rec bod dTable) 
          Just _  -> L l $ LetE (Var s,loc,t, (rec rhs dTable)) (rec bod dTable) 
        IfE e1 e2 e3             ->  L l $ 
          IfE (rec e1 dTable) ( rec e2 dTable) ( rec e3 dTable)
        CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1) 
          where
            f (dataCon,x,exp) = (dataCon, x, (rec exp dTable))  
        AppE v loc e             ->  L l $ AppE v loc $ rec e dTable
        TimeIt exp a b           ->  L l $ TimeIt (rec exp dTable) a b 
        otherwise -> L l ex 
                    
-- need to convert this to monand PassM and generate unique variable names later.
tupleListOfFunctions :: DDefs Ty1 -> [FunDef1] ->Var -> PassM(FunDef1)
tupleListOfFunctions  ddefs funcList newName = do
  ls <- Prelude.mapM freshBody  funcList
                                            
  let lsVector    = V.fromList ls 
      retTypes    = V.map (\f -> (outTy (funTy f))) lsVector
      newRetType  = ProdTy (V.toList retTypes)  
      newFuncInputType = ProdTy (V.ifoldl f [] lsVector)
        where 
          f ls i fdef = 
            case (inTy (funTy fdef)) of 
              ProdTy (h:tail)-> 
                if (i==0) 
                  then 
                    (ls L.++ (h:tail)) 
                  else 
                    (ls L.++ tail)
  
  let traversedType = case (newFuncInputType) of (ProdTy (h:tail))-> h
  newArgVar <- gensym (toVar "input")
  
  let functionsBodies = toList (V.imap getBody lsVector) 
       where 
          getBody i func = 
            let getArgsLength f = case  (funTy f) of
                  (ProdTy x,_) -> L.length x
                body1 = funBody func
                argsLength  = getArgsLength func
                oldArgVar   = funArg func
                shift = V.ifoldl computeShift 0 lsVector
                  where 
                    computeShift sum j fdef = 
                      if(j<i )
                        then  if (j==0) 
                                  then  sum + (getArgsLength fdef)
                                  else   sum + (getArgsLength fdef) -1

                        else 0 
                      
            in let body2 = loop 1 argsLength body1 
                    where
                      loop i n exp  = if(i==n) 
                        then  exp 
                        else  loop (i+1) n (replaceProj i oldArgVar (i+shift) 
                          newArgVar exp)                     
            in  replaceProj 0 oldArgVar 0 newArgVar body2                              
      
  let step2 = L.foldl mapAndSplit M.empty functionsBodies  
        where 
          mapAndSplit mp (L _(CaseE e lsCase))  = L.foldl f mp lsCase
            where f mp2 (dataCons, vars, exp)  = 
                    let exp' = subsVars exp
                    in case (M.lookup dataCons mp2) of
                         Nothing -> M.insert dataCons [ exp' ] mp2 
                         Just x -> M.insert dataCons (x L.++[exp' ]) mp2 
                    where 
                       subsVars ex = V.ifoldr subsVar ex (V.fromList vars) 
                       subsVar index v ex   = 
                          let oldExp = l $ VarE (fst v) 
                              newExp = l (VarE (toVar (L.map toLower
                                 (dataCons L.++ (show index)))))
                          in substE  oldExp newExp ex

  let inputDef = lookupDDef ddefs typeStr 
        where 
          typeStr = case traversedType of
              (PackedTy typeStr _) -> typeStr
              x -> error "not expected "`debug`  (show x )
      createOutVar index =  (toVar ("f" L.++(show index)L.++"out" )) 
 
  let tailExpr = MkProdE $( V.toList ( V.imap (\index _ ->l (VarE
       (createOutVar index))) lsVector ))

  let topLevelExpr = (CaseE (l (ProjE 0 (l (VarE newArgVar))))[])
  let extendedCase = L.foldr addConstructorBody topLevelExpr (dataCons inputDef) 
        where
          addConstructorBody (dataCons, varls) (CaseE e1 caseList) =         
            let newVarsList = V.toList( V.imap (\index _ -> ( toVar (L.map 
                  toLower (dataCons L.++ (show index))) ,() ) )(V.fromList varls) ) 
                combinedBodies  =  V.ifoldl f (l tailExpr) (V.fromList (L.reverse 
                  (step2 M.! dataCons)))
                 where 
                  f tailExp index exp  = 
                    let newVar     = createOutVar ((V.length lsVector)-index-1) 
                        newVarType =outTy (funTy (lsVector V.! 
                          ((V.length lsVector)-index-1))) -- the return type of function at index 
                    in (replaceLeafWithBind exp newVar newVarType tailExp)                     
            in (CaseE e1 ((dataCons, newVarsList, combinedBodies):caseList)) 
            
  return (FunDef newName newArgVar (newFuncInputType,newRetType) (l extendedCase))
 where 
  replaceProj i1 argVar1 i2 argvar2 exp= 
    let oldExp = l $ ProjE i1 (l (VarE argVar1))
        newExp = l $ ProjE i2 (l (VarE argvar2))
    in substE oldExp newExp exp

  freshBody func = do 
      b' <- freshExp [] (funBody func)
      return (func{funBody =b'})
renameFunction :: FunDef1 -> Var -> FunDef1
renameFunction function newName =
   function{funName=newName, funBody = rec (funBody function)}
    where 
     rec (L l ex) = 
      let oldName = funName function in 
        case ex of 
          AppE name loc e          ->  L l $ 
            AppE (if name==oldName then newName else name) loc (rec e) 
          PrimAppE x ls            ->  L l $ PrimAppE x (L.map f ls) 
            where f item = (rec item)--`debug`  ("so2") 
          LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (rec rhs)) (rec bod)
          MkProdE ls               ->  L l $ MkProdE (L.map (\x-> rec x) ls)
          ProjE index exp          ->  L l $ ProjE index (rec exp)
          CaseE e1 ls1             ->  L l $ CaseE (rec e1)  (L.map f ls1) 
            where f (dataCon,x,exp) = (dataCon, x, (rec exp)) 
          DataConE loc datacons ls ->  L l $
            DataConE loc datacons(L.map (\x-> rec x) ls)
          TimeIt e d b             ->  L l $ TimeIt ( rec e) d b
          otherwise                ->  L l ex

{- Output of this is no longer from a variable to its uses we want to search for 
the following:
  f1 (x1, v1,v2 ...vn) 
  f2 (x1, k1,k2 ...kn)
 such that
body (f1) = case (x1) of {}
body (f2) = case (x1) of {}  
this function will look for the first condition and another function will filer 
out the results based on the second condition , Var in the resulted map is X1 
in the above example, this only works this way because we know how we perform the
tupling previously.
-}
buildTupleCandidatesTable::   FunDefs1 -> L Exp1 -> Maybe Var -> M.Map Var [Exp1]
buildTupleCandidatesTable fDefs ex traversedTree = 
  rec  ex (M.fromList []) 
 where
  rec (L l ex) tb = case ex of 
      AppE _ _ _               -> tb 
      PrimAppE _ _             -> tb  
      LetE (v,_,_,rhs) body    -> 
        let t1 =rec rhs t1 
            t2= rec body tb
        in case (getExp rhs) of
            callExp@(AppE fName _ argList) ->  
                case (getExp argList) of
                    MkProdE ((L _ (VarE inputTree)):tail) -> 
                        if((isTupleable (fDefs M.! fName)) &&
                            (haveIndependentArgs tail traversedTree)) 
                          then
                            let f Nothing   = Just [callExp]
                                f (Just ls) = Just (L.nub (callExp:ls))
                            in   (M.alter f inputTree (rec body tb)) 

                          else t2 
                    otherwise   -> t2   
            otherwise -> t2
      
      
      IfE e1 e2 e3             -> let t1 = rec e1 tb 
                                      t2 = rec e2 t1
                                  in rec e3 t2 
      MkProdE ls               -> tb 
      ProjE index exp          -> tb
      CaseE e1 ls1             ->  
          let t1 = rec e1 tb in 
          L.foldl f t1 ls1 
         where 
          f table (_ ,_ ,exp) = rec exp table
      DataConE loc datacons ls -> L.foldl f tb ls where f table exp = rec exp table 
      TimeIt exp _ _           -> rec exp tb  
      otherwise                -> tb 
   where 
    isTupleable f = case (getExp (funBody f)) of 
      ---add a check that there is no nested case (maybe)
        CaseE e _ -> case (getExp e) of
            ProjE 0 (L l (VarE v))-> if(v == (funArg f)) then True else False
            _ -> False --`debug` "\n5\n"
        _ -> False --`debug` "\n7\n"

    haveIndependentArgs args  traversedTree= L.foldl f True args 
     where 
      f b arg  = b && 
         (case (getExp arg) of
             LitE _ -> True
             ProjE i (L l (VarE v)) -> case (traversedTree) of
                Nothing -> False 
                Just inputVar ->  if(v==inputVar)  then True else False
             x -> False )


tuple :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> Maybe Var -> [(Var, Var, Int, Var)] 
 ->  PassM (L Exp1,  FunDefs1)
tuple ddefs fdefs oldExpIn traversedTree fusedFunctions  = do

  let candidates1 = L.filter f ( M.toList (buildTupleCandidatesTable 
       fdefs oldExpIn traversedTree) )
       where f (_, ls) = (L.length ls)> 1

   -- a list of [(fName, CallExpressions)]
  let candidates2 = L.map 
        (\(traversedVar, ls) -> 
          let firstCall = case (ls) of (h:tail) -> h
              sortedCalls = L.sortOn f ls
                 where f exp@(AppE fName _ _) = (fName,exp)
           in (constructName sortedCalls, sortedCalls, firstCall) 
        ) candidates1 
       where 
          constructName ls = toVar( "_TUP_" L.++ (L.foldl  appendName "" ls) 
            L.++  "_TUP_" )
          appendName str (AppE fName _ _) = (str  L.++ "_t_" L.++ (fromVar fName))  
         
  (oldExp, fdefs) <- Control.Monad.foldM f  (oldExpIn, fdefs)  candidates2 
 
  return $(oldExp,fdefs) --`debug`("tuple candidates" L.++ (show candidates1))
 where
    f (exp, fdefs) (tupledFName, callExpressions, firstCall) = do 
      case (M.lookup tupledFName fdefs) of
          Just fdef -> do 
           exp' <-foldTupledFunctions exp fdef callExpressions firstCall 
           return (exp', fdefs)

          Nothing -> do 
            let functionsToTuple = L.map getCalledFunDef  callExpressions
                  where
                    getCalledFunDef callExpr = case (callExpr) of
                        (AppE fName _ _) -> case (M.lookup fName fdefs) of
                             Just fdef -> fdef
            tupledFunction <- tupleListOfFunctions ddefs  functionsToTuple
               tupledFName

            let tupledFunction' = L.foldr f tupledFunction fusedFunctions
                 where
                   f entry fdef = foldFusedCalls_f entry fdef 

            let fdefs' = M.insert tupledFName tupledFunction'  fdefs
              
            (recTupledBody, newDefs) <- tuple ddefs fdefs' (funBody tupledFunction') 
                (Just (funArg tupledFunction')) fusedFunctions 
                  --`debug`("\ntupling:" L.++ (show tupledFName))
            
            let tupledFunction'' =tupledFunction'{funBody=recTupledBody } 
            let tupledFunction''' =tupledFunction''{funBody= removeCommonExpressions(funBody tupledFunction'') } 

            let fdefs'' = M.insert tupledFName tupledFunction''' newDefs

            exp' <- foldTupledFunctions exp  tupledFunction callExpressions
               firstCall
            return (exp', fdefs'')

fuse :: DDefs Ty1 -> FunDefs1 -> Var -> Var -> [(Var, Var, Int, Var)]
 -> PassM  (Bool, Var,  FunDefs1)
fuse ddefs fdefs  innerVar  outerVar fusedFunctions_ = do
  let innerFunc =  inlineArgumentProjections (fdefs M.! innerVar)
      outerFunc =  inlineArgumentProjections (fdefs M.! outerVar)
      newVar    = toVar ("_FUS_f_" L.++ (fromVar outerVar) L.++
         "_f_" L.++(fromVar innerVar ) L.++ "_FUS_")
  --newName   <-  gensym_tag (newVar) "inline" 
  let newName  = newVar
  innerFreshBody <- freshExp []  (funBody innerFunc) 
  outerFreshBody <- freshExp []  (funBody outerFunc)
  setp1 <- inline innerFunc{funBody =innerFreshBody}
               outerFunc{funBody = outerFreshBody}  (-1)
  let step2 =  (simplifyCases setp1 ){funName = newName}
      step3 =  foldFusedCalls_f (outerVar, innerVar, -1, newName)  step2
      -- fold upper level fused functions
      step4 = L.foldl (\f e -> foldFusedCalls_f e f ) step3 
       fusedFunctions_

      step5 =  removeUnusedDefs step4 
  return $(True, newName, M.insert  newName step5 fdefs ); 

violateRestrictions :: FunDefs1 -> Var -> Var -> Bool
violateRestrictions fdefs inner outer =
  do
    let innerDef = case (M.lookup inner fdefs) of (Just  v) ->v
        outerDef = case (M.lookup outer fdefs) of (Just v) ->v
        p1 = case (fst (funTy innerDef) ) of
            (PackedTy _ _ ) -> False 
            (ProdTy ( (PackedTy _ _ ):_)) -> False
            x  -> True --`debug` ("ops "L.++ (show x))
        p2 = case (fst (funTy outerDef) ) of
            (PackedTy _ _) -> False 
            (ProdTy ( (PackedTy _ _ ):_)) -> False
            x  -> True --`debug` ("ops "L.++ (show x))
    (p1 || p2)

transform :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> Maybe Var->  [(Var, Var, Int, Var)] -> 
  Bool -> [(Var, Var)] ->  PassM (L Exp1,  FunDefs1, [(Var, Var, Int, Var)])
transform  ddefs funDefs  exp traversedTree fusedFunctions_ doTupling processedCandidates= do
  rec exp processedCandidates funDefs fusedFunctions_
 where
  rec (L l body) processed fdefs  fusedFunctions = do
    let defTable = buildDefTable body  
        potential = findPotential defTable processed --`debug`(show defTable)
    case (potential) of
      Nothing -> do 
        -- final clean and tuple
        let final_clean = removeUnusedDefs_exp (L l body)
        -- let (tupledBody, tupleDefs) = (final_clean, M.empty)
        (tupledBody, tupleDefs) <- do
          if (doTupling)
            then tuple ddefs fdefs  final_clean traversedTree fusedFunctions
            else return (final_clean, M.empty)
        return $(tupledBody, M.union fdefs tupleDefs, fusedFunctions) 

      Just ((inner,outer), outerDefVarSymbol) -> 
        if( violateRestrictions fdefs inner outer) 
          then rec (L l body)  ((inner,outer):processed) fdefs fusedFunctions-- `debug` ("here" L.++ (show(inner,outer) ))
          else do
             -- fuse
            (validFused, fNew, fusedDefs) <-  (fuse  ddefs fdefs inner outer 
               fusedFunctions_ )  
            let fused_function = fusedDefs M.! fNew 
            let newFusedEntry = (outer,inner, -1, fNew)
           
            (recAppBody, recAppDefs, retFusedFunctions) <- transform
              ddefs fusedDefs (funBody fused_function) (Just (funArg fused_function))
                (newFusedEntry : fusedFunctions) (not (isPotential defTable
                   outerDefVarSymbol ((inner,outer):processed)) ) 
                     ((inner,outer):processed)
            --clean 
            let newFusedFunctions =  (newFusedEntry : fusedFunctions) L.++ retFusedFunctions
            let cleaned_function = removeUnusedDefs fused_function{funBody = recAppBody} 
                fdefs_tmp2       = M.union fusedDefs recAppDefs 
                fdefs_tmp3       = M.insert  fNew cleaned_function fdefs_tmp2
            -- tuple
            let (tupledBody, tupleDefs) = (funBody cleaned_function, M.empty)
        
            let tupled_function = cleaned_function{funBody = tupledBody}
                fdefs_tmp4      = M.union   fdefs_tmp3 tupleDefs 
                fdefs_tmp5      = M.insert  fNew tupled_function fdefs_tmp4
                valid = validFused
                newDefs = fdefs_tmp5
            if ( valid==True )
              then let body' = removeUnusedDefs_exp (foldFusedCalls
                         (outer,inner, -1, fNew) (L l body) )
                   in rec body' ((inner,outer):processed)
                        (M.union fdefs newDefs) newFusedFunctions
              else  rec (L l body)  ((inner,outer):processed) fdefs fusedFunctions

fusion2 :: Prog1 -> PassM Prog1
fusion2 (L1.Prog defs funs main) = do
    (main', funs') <- case main of 
        Nothing   -> return $ (Nothing, funs)
        Just (m, ty)    -> do
            (m', newDefs, _) <- (transform defs funs m Nothing [] True [])
            return (Just (m',ty), M.union funs newDefs)
    return $ L1.Prog defs funs' main'
