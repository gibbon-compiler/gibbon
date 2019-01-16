
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}

module Gibbon.Passes.Fusion2 (fusion2) where
import Prelude hiding (exp)

import Control.Exception
import Data.Loc
import qualified Data.Map as M
import qualified Data.List as L
import qualified  Data.Set as S
import qualified Data.Vector as V
import Data.Symbol
import Gibbon.L1.Syntax as L1
import Debug.Trace
import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Gibbon.Common
import Data.Tuple.All
import Data.Vector as V

                                                
 

freshExp :: [(Var,Var)] -> L Exp1 -> PassM (L L1.Exp1)
freshExp vs (L sloc exp) = fmap (L sloc) $
            case exp of
              L1.Ext _     -> return exp
              L1.LitE i    -> return $ L1.LitE i
              L1.LitSymE v -> return $ L1.LitSymE v

              L1.VarE v ->
                case lookup v vs of
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


-- Helper Functions
debug = flip trace
getExp:: L Exp1-> Exp1 
getExp  (L  _ exp) = exp


-- Types
data DefTableEntry = DefTableEntry {def::Exp1, fun_uses :: [(Exp1,Int)], all_use_count:: Int  } deriving (Show , Generic, NFData)
type DefTable = M.Map Symbol DefTableEntry 
type PotentialPair = (Symbol, Symbol)
type PotentialsList = [DefTableEntry] 


--Rewrite this using a case .. will look nicer i think!

buildDefTable:: Exp1 -> DefTable
buildDefTable ex  = 
  rec ex M.empty where 
    rec ex table= 
      case (ex) of
          VarE (Var sym) ->  M.update f sym table 
                       where f (DefTableEntry  def fun_uses c) = Just ( DefTableEntry def fun_uses (c+1))          
 
          callExp@(AppE _ _ (L _  (MkProdE argsList))) ->
                       buildDefTable_args  callExp argsList table 0
                       where  buildDefTable_args _ [] table _ = table
                              buildDefTable_args callExp (h:tail)  table index=
                               case getExp h  of 
                                  VarE (Var sym)    -> buildDefTable_args callExp tail (M.update f sym table) (index+1)
                                               where f (DefTableEntry  def fun_uses c) = Just ( DefTableEntry def ((callExp,index):fun_uses) (c+1)) 
                                  _                 -> buildDefTable_args callExp tail  table (index+1)

          callExp@(AppE _ _ (L _  (VarE (Var sym ))))  ->
                       M.update f sym table 
                       where f (DefTableEntry  def fun_uses c) = Just ( DefTableEntry def ((callExp,-1):fun_uses) (c+1)) -- -1 means there is no ProdE ( only one argument)

          PrimAppE _ ls ->  L.foldl f table ls
                      where f tbl exp = rec (getExp exp) tbl

          LetE ((Var sym),_,_,bind) body ->
                      let table' =  (rec (getExp bind) table) 
                      in let table'' =  case (getExp bind) of
                                          AppE _ _ _     ->  M.insert sym (DefTableEntry {def=(getExp bind), fun_uses=[], all_use_count = 0} ) table'
                                          _              ->  table' 
          
                      in rec (getExp body) table''
     

          IfE cond thenBody elseBody      ->
                      let table' = rec (getExp cond) table 
                      in let table'' = rec ( getExp thenBody) table'
                      in   rec (getExp elseBody) table''


          CaseE e ls      -> let table' = rec ( getExp e) table 
                       in L.foldl f table' ls
                       where f tbl (_, _, exp ) = rec (getExp exp) tbl
    
          DataConE _ _ ls -> L.foldl f table ls where f tbl exp = rec (getExp exp) tbl

          TimeIt exp _ _  -> rec (getExp exp) table
         
          ProjE index exp -> rec (getExp exp) table

          _                -> table ------`debug`  ("Defualt" L.++ show a) 

extractAppEName ::  Exp1 -> Var
extractAppEName (AppE var _ _ ) = var


-- isInList :: (Var, Var) -> [(Var, Var)] ->Bool
-- isInList (outer, inner ) [] = False;
-- isInList (outer, inner) ((outer',inner'):xs) = 
--   ((fromVar outer)==(fromVar outer') &&
--    (fromVar inner) ==(fromVar inner))||
--   ( isInList (outer, inner ) xs)`debug` (show (fromVar outer)L.++(fromVar outer')L.++ (fromVar inner)L.++(fromVar inner') )  

findPotential :: DefTable -> [(Var, Var)] -> Maybe (Var, Var)
findPotential table skipList = 
  case (L.find predicate (M.toList table) ) of
    Nothing       -> Nothing --`debug`  (show skipList) 
    Just (_, (DefTableEntry def fun_uses use_count ) ) -> Just ((extractAppEName def),(extractAppEName(fst (L.head fun_uses))) ) --`debug`  (show (isInList  ((extractAppEName def),(extractAppEName(fst (L.head fun_uses))) ) skipList ) ) 

  where  predicate (_,DefTableEntry def fun_uses use_count )  =
                   (L.length fun_uses >= 1) &&
                   (L.notElem  ((extractAppEName def),(extractAppEName(fst (L.head fun_uses))) ) skipList ) 
  
                 

inline :: FunDef1 -> FunDef1 -> Int  ->  FunDef1
inline inlined_fun outer_fun arg_pos  =  
  -- right now i am only handling when the outer function have one argument which is the tree prodcued by the inlined function 
  -- in the future i shoul allow multiple arguments ...
  -- why dont we always make the type prod for simplification !

  -- also right now we assume that the inlined fuction takes one argument which is the input tree
  let old_exp  = l $ case (fst (funTy outer_fun)) of
                    ProdTy _      ->  error "not handled yet" --ProjE arg_pos (l (VarE (fst (funArg outer_fun) )) )
                    _             ->  VarE (funArg outer_fun)


  in let newFunArg =  let argType_outer= fst (funTy outer_fun)
                          argVar_outer = funArg outer_fun
                          argType_inlined= fst (funTy inlined_fun)
                          argVar_inlined = funArg inlined_fun

                      in case  argType_outer  of 
                              ProdTy ls -> error "not supported yet" -- (argVar, ProdTy (take arg_pos ls  L.++ drop (1 + arg_pos) ls) )
                              _         -> case  argType_inlined  of 
                                                 ProdTy ls -> error "not supported yet" -- (argVar, ProdTy (take arg_pos ls  L.++ drop (1 + arg_pos) ls) )
                                                 _         ->  funArg inlined_fun

  in outer_fun { funArg  = newFunArg ,
                 funBody = substE old_exp (funBody inlined_fun) (funBody outer_fun) }


--  THERE IS AN ASSUMPTION THAT DataConstE takes only list of variable references ( no nested pattern matching) 
simplifyCases :: FunDef1 -> FunDef1
simplifyCases function = 
  function {funBody = rec ( funBody function) }
  where rec ( L l ex)  = case  ex of
                 

                  CaseE e1@(L l (CaseE e2 ls2)) ls1          -> -- TODO : USE MAP INSTEAD OF FOLD HERE !!
                               rec $ L l $ CaseE e2 (L.map f ls2)
                               where f oldItem = (upd3 newMember oldItem)  where newMember = L l (CaseE (sel3 oldItem) ls1)
                  
                  CaseE e1@(L l (DataConE loc k ls)) ls1     -> 
                                let newBody = L.find predicate ls1 where predicate item = if(sel1 item == k) then True else False
                                in case newBody of 
                                   Nothing -> error "unmatched construcotor!"
                                   Just (k, vars, exp)  -> rec $case_subst ls vars exp
                                   where case_subst (x1:l1) (x2:l2) exp =
                                            subst (fst x2) ( x1) (case_subst l1 l2 exp)
                                         case_subst [] [] exp = exp
                  
                  CaseE (L l' (IfE e1 e2 e3) ) ls ->
                                 rec $ (L l (IfE e1 ( L l' $CaseE e2 ls) ( L l' $CaseE e3 ls) ))            
                  CaseE e1@(L l' (LetE bind body )  ) ls1    ->
                                 L l' $ LetE bind (rec $ L l $ CaseE body (ls1) )

                  CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1) where f item = (upd3 (rec (sel3 item)) item)   
                  LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (rec rhs)) (rec bod)  
                  AppE v loc e             ->  L l $ AppE v loc $ rec e
                  IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)
                  TimeIt e d b             ->  L l $ TimeIt ( rec e) d b 

                  _            -> L l ex


-- this one as well assumes that one arg  (outer and inner )
-- it also assumes that there is no variables shadowing "imprtant!! " --> can be chnaged not to by carrying the deftable around 

-- we have a probelem here and its that 
foldFusedCalls_f :: (Var, Var, Int, Var) -> FunDef1 -> FunDef1
foldFusedCalls_f rule function = function{funBody= foldFusedCalls rule (funBody function)}

foldFusedCalls :: (Var, Var, Int,Var ) -> L Exp1  ->(L Exp1) 
foldFusedCalls rule@(outerName, innerName, argPos,newName ) body =
 let defTable = buildDefTable (getExp body)  
 in let rec (L l ex ) = case (ex) of 
                          AppE v loc argList -> 
                              let ignore = L l $ AppE v loc (rec argList) 
                                 in if(v ==  outerName)  then 
                                      case (getExp argList ) of 
                                          VarE (Var sym) ->  if( innerName == getDefiningFuntion sym)  
                                                      then
                                                             L l  $AppE  newName loc (getArgs sym)--`debug` ((show outerName) L.++ (show innerName) L.++ (show newName)L.++(show (AppE  newName loc (getArgs sym))) L.++ "here2 apply")
                                                                                        
                                                      else
                                                         ignore--`debug` ("here1")   -- the outer has only one argument which is the tree itself so 
                                          
                                           where getDefiningFuntion x = case (M.lookup x defTable) of
                                                                                  Nothing    ->  (toVar "")--`debug`  ("defined by constructor !!!")
                                                                                  Just entry -> case (def  entry) of 
                                                                                                AppE v _ _   -> v
                                                                                                _            -> error  ("ops" L.++ (show(def  entry)))
                                                 getArgs x  = case (M.lookup x defTable) of
                                                                                               Nothing    -> error  "error in foldFusedCalls"
                                                                                               Just entry -> case (def  entry) of 
                                                                                                                AppE _ _ args   -> args
                                                                                                                _               -> error  ("ops" L.++ (show(def  entry)))

                                                     
                                    else
                                                        ignore`debug`  ("outer" L.++ (show newName) L.++ "here2 ignore " L.++ (show v) )   

                          LetE (v,loc,t,lhs) bod   ->  L l $ LetE (v,loc,t, (rec lhs)) (rec bod)--`debug`  ("here3  ") 
                          IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)     --`debug` ("here4  ") 
                          CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1) where f (dataCon,x,exp) = (dataCon, x, (rec exp)) --`debug`  ("here5  ") 
                          TimeIt e d b             ->  L l $ TimeIt ( rec e) d b--`debug`  ("here10  ") 
                          DataConE loc datacons ls ->  L l $ DataConE loc datacons (L.map (\x-> rec x) ls)

                          otherwise -> L l ex --`debug` ("here6  ") 
  in rec body

foldTupledFunctions_f :: ( FunDef1) ->[Var] ->( FunDef1)
foldTupledFunctions_f funDef ls = funDef{funBody = (foldTupledFunctions (funBody funDef ) funDef ls )}

foldTupledFunctions ::   L Exp1 -> ( FunDef1) -> [Var] -> L Exp1
foldTupledFunctions body newFun oldCalls = 
    (rec  body  M.empty)  where
       rec (L l ex) mp = 
              case (ex) of 
                    p@(LetE (Var y, loc, t,rhs@(L _ (AppE f _ (L l (VarE x) )) )) body) ->
                          case (L.elemIndex f oldCalls ) of 
                                   Nothing -> L l $ LetE (Var y, loc, t, (rec rhs mp))  (rec body mp) 
                                   Just i  -> case (M.lookup x mp) of
                                             Nothing  -> let newVar =toVar ((fromVar x) L.++ "_unq_") in 
                                                           let newMp = M.insert x newVar mp in
                                                              L l $ LetE (newVar, [], (outTy (funTy newFun)), (L l  (AppE  (funName newFun) [] ( L l (VarE x) )))) (rec (L l p) newMp) 
                                             
                                             Just k   ->  L l $ LetE (Var y, loc, t, (L l (ProjE i  (L l $ VarE k)))) ( rec body mp)

                    AppE name loc e          ->  L l $ AppE name loc (rec e mp)  
                    PrimAppE x ls            ->  L l $ PrimAppE x (L.map f ls) where f item = (rec item mp)
                    LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (rec rhs mp)) (rec bod mp) 
                    IfE e1 e2 e3             ->  L l $ IfE (rec e1 mp) ( rec e2 mp) ( rec e3 mp)
                    MkProdE ls               ->  L l $ MkProdE (L.map (\x-> (rec x mp)) ls) 
                    ProjE index exp          ->  L l $ ProjE index (rec exp mp)
                    CaseE e1 ls1             ->  L l $ CaseE ( rec e1  mp) (L.map f ls1) where f (dataCon,x,exp) = (dataCon, x, (rec exp mp))  
                    DataConE loc datacons ls ->  L l $ DataConE loc datacons (L.map (\x-> (rec x mp)) ls)
                    TimeIt e d b             ->  L l $ TimeIt ( rec e mp) d b 
                    otherwise                -> L l ex


removeUnusedDefs :: FunDef1 -> FunDef1
removeUnusedDefs f = f{funBody = removeUnusedDefs_exp (funBody f)}


removeUnusedDefs_exp :: L Exp1 ->  L Exp1 
removeUnusedDefs_exp exp =
 let defTable = buildDefTable (getExp exp)  
  in rec exp defTable where
     rec (L l ex) dTable = 
       case ex of 
                    LetE (Var s,loc,t,rhs) bod   -> case (M.lookup s dTable ) of
                                                      Nothing ->L l $ LetE (Var s,loc,t, (rec rhs dTable))  (rec bod dTable)  --error  ("error in removeUnusedDefs" L.++ show s)
                                                      Just ( DefTableEntry _ _ 0) -> (rec bod dTable) 
                                                      Just _  -> L l $ LetE (Var s,loc,t, (rec rhs dTable))  (rec bod dTable) 
                    IfE e1 e2 e3             ->  L l $ IfE (rec e1 dTable) ( rec e2 dTable) ( rec e3 dTable)
                    CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1) where f (dataCon,x,exp) = (dataCon, x, (rec exp dTable))  
                    AppE v loc e             ->  L l $ AppE v loc $ rec e dTable
                    TimeIt exp a b           ->  L l $ TimeIt (rec exp dTable) a b 

                    otherwise -> L l ex 
                    
-- need to convert this to monand PassM and generate unique variable names later.
tupleListOfFunctions :: DDefs Ty1 -> [FunDef1] ->   (FunDef1, [Var] )
tupleListOfFunctions  ddefs ls = do
  let newName = L.foldl  appendName "" ls where appendName tmp function = (tmp  L.++ (fromVar (funName function)))  
  -- we want to prepare the body of each function seperatly now
  let lsVector    = V.fromList ls 
  let retTypes    = V.map (\f -> (outTy (funTy f))) lsVector
  let newRetType  = ProdTy (V.toList retTypes)  

  let newArgVar = toVar "input"
  let traversedType = inTy (funTy (L.head ls))
  let newArgs = newArgVar
  let step1 = L.map getBody ls where getBody fun = substE  (l (VarE (funArg( L.head ls))) ) (l (VarE newArgVar)) (funBody fun)  

  let step2 = L.map mapAndSplit step1  
                      where mapAndSplit (L _(CaseE e ls)) = L.foldr f M.empty ls 
                              where f (dataCons, varls, exp) mp = M.insert dataCons (subsVars exp) mp
                                      where subsVars ex = V.ifoldr subsVar ex (V.fromList varls) 
  
                                             where subsVar index v ex   = substE  (l (VarE (fst v) )) (l (VarE (toVar (dataCons L.++ (show index))))) ex  
 

  let inputDef = lookupDDef ddefs ( case  traversedType of (PackedTy typeStr _) -> (toVar typeStr)) --`debug`  (show traversedType L.++ (show ls)) 
  let dataConsList = dataCons inputDef
  let createOutVar index =  (toVar ("f" L.++(show index)L.++"out" )) 

  let outPart = l ( MkProdE  genL  )
         where genL = V.toList (  V.imap  (\index _ ->l (VarE ( createOutVar index) ) ) (V.fromList ls))

  let retAllExp = MkProdE (V.toList ( V.imap (\index _ ->l (VarE (createOutVar index))) lsVector ) )
  let reduceStep = L.foldr reduce (CaseE (l (VarE newArgVar))[]) dataConsList where
                              reduce (dataCons, varls) (CaseE ex ls ) = CaseE ex ((consBody):ls)
                                       where consBody = (dataCons, newVarsList, combinedBodies) where 
                                              newVarsList     =  V.toList( V.imap (\index _ -> ( toVar (dataCons L.++ (show index)) ,() ) ) (V.fromList varls) ) where 
                                              combinedBodies  =  V.ifoldr (\index body res  -> l (LetE ((createOutVar index),[],(unsafeIndex retTypes index),body) res )) (l retAllExp) (V.fromList partialList)
                                                                  where partialList =  L.map (\m -> case ( M.lookup dataCons m) of 
                                                                                                        (Just a ) -> a 
                                                                                                        (Nothing) ->error "ooopsa1")  step2 

  let funNames = L.map (\f -> funName f ) ls                                                                                          
  (FunDef (toVar ("tupled__" L.++ newName) ) newArgs (traversedType, newRetType) (l reduceStep) , funNames)

renameFunction :: FunDef1 -> Var -> FunDef1
renameFunction function newName = 
  function{funName=newName, funBody = rec (funBody function)} where 
    rec (L l ex) = 
      let oldName = funName function in 
            case ex of 
                  AppE name loc e          ->  L l $ AppE (if name==oldName then newName else name) loc (rec e) --`debug`  ("so1") 
                  PrimAppE x ls            ->  L l $ PrimAppE x (L.map f ls) where f item = (rec item)--`debug`  ("so2") 
                  LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (rec rhs)) (rec bod) --`debug`  ("so3") 
                  IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)--`debug`  ("so4") 
                  MkProdE ls               ->  L l $ MkProdE (L.map (\x-> rec x) ls)--`debug`  ("so5") 
                  ProjE index exp          ->  L l $ ProjE index (rec exp)--`debug`  ("so6") 
                  CaseE e1 ls1             ->  L l $ CaseE (rec e1)  (L.map f ls1) where f (dataCon,x,exp) = (dataCon, x, (rec exp))  ----`debug`  ("so7") 
                  DataConE loc datacons ls ->  L l $ DataConE loc datacons (L.map (\x-> rec x) ls)--`debug`  (("so8") L.++ (show newName))
                  TimeIt e d b             ->  L l $ TimeIt ( rec e) d b--`debug`  ("so9") 
                  otherwise                ->  L l ex--`debug`  (("so10") L.++ (show ex))



buildUseTable::   L Exp1 -> M.Map Var [(Var, Exp1)]
buildUseTable ex  = rec  ex (M.fromList []) where
  rec (L l ex) tb = case ex of 
      AppE _ _ _               -> tb 
      PrimAppE _ _             -> tb
      LetE (v,_,_,(L _ callexp@(AppE _ _ (L _ (VarE par )) ) )) body ->  
          M.alter f par (rec body tb) 
         where --add a check to make sure that the call exp represent a traversal and is not a simple functions call
           f Nothing   = Just [(v,callexp)]
           f (Just ls) = Just ((v,callexp):ls) 
      LetE (v,_,_,rhs) body    -> let t1 = rec rhs tb in rec body t1  
      IfE e1 e2 e3             -> let t1 = rec e1 tb 
                                      t2 = rec e2 t1
                                  in rec e3 t2 
      MkProdE ls               -> tb 
      ProjE index exp          -> tb
      CaseE e1 ls1             ->  
          let t1 = rec e1 tb in 
          L.foldl f t1 ls1 
         where 
          f table (_ ,_ ,exp) = rec exp tb 
      DataConE loc datacons ls -> L.foldl f tb ls where f table exp = rec exp tb 
      TimeIt exp _ _           -> rec exp tb  
      otherwise                -> tb

-- in each set of a functions to be tupled we want them to all start with a case on the input tree .
--or all start with an If such that e1 is the same for all of them !
check2 :: [FunDef1] ->Bool
check2 []     = False
check2 (x:[]) = False
check2 (x:(y:xs)) = (hasCommonIfBody (funArg x) (funArg y)(funBody x)(funBody y))
 || (hasCommonCaseBody (funArg x) (funArg y)  (funBody x)(funBody y))
 where
    hasCommonIfBody in1 in2 (L _ (IfE e1 _ _ )) (L _ (IfE e2 _ _ )) = 
      if (subst in1 (l (VarE (toVar "input"))) e1 ) 
          == (subst in2 (l (VarE (toVar "input"))) e2 ) 
        then  True
        else False
  
    hasCommonIfBody _ _ _ _ = False 
    hasCommonCaseBody in1 in2 (L _ (CaseE (L _ (VarE in1_) ) _ ) ) 
      (L _ (CaseE (L _ (VarE in2_) ) _ ) ) = (in1==in1_) && (in2==in2_)
    hasCommonCaseBody _ _ _ _ = False

tuple :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> [(Var, Var, Int, Var)] -> PassM (L Exp1,  FunDefs1)
tuple ddefs fdefs oldExp fusedFunctions = do
  let useTable         = buildUseTable oldExp
      useTableFiltered = M.filter check1 useTable 
                        where 
                         check1 entry = (L.length entry == 2)  -- need to be extended and checked on a case where length>2 
      candidates = L.nub (L.map proccessEntry (M.toList useTableFiltered) ) 
                where  
                  proccessEntry (_, ls) = L.sort (L.map extractFuncName ls) 
                  extractFuncName (_,(AppE fName _ _ )) = fName
      functionsToTuple = L.map (\ls -> L.map getFunDef ls) candidates 
                        where
                         getFunDef fName  = case ( M.lookup fName fdefs ) of 
                           Nothing     ->error ("not expected" L.++ (show fName))
                           Just funDef -> funDef
      freshBody f = do 
        b' <- freshExp [] (funBody f)
        return f{funBody =b'}
        
  functionsToTuple <- Prelude.mapM ( \ls->  (Prelude.mapM freshBody  ls))  
                        functionsToTuple   --L.filter check2 functionsToMerge
  
  let unfoldedTupledFunctions = L.map (tupleListOfFunctions ddefs) functionsToTuple
      -- for each tupled function fold the previously fused calls in it
      foldedTupledFunctions   = L.map ( \(funDef,ls) ->
        ((L.foldr (\entry fdef -> foldFusedCalls_f entry fdef) funDef 
          fusedFunctions),ls))  unfoldedTupledFunctions    
      foldedTupledFunctions2   = L.map ( \(funDef,ls) ->
        ((foldTupledFunctions_f funDef ls) ,ls) )  foldedTupledFunctions

      newExp = L.foldr (\(funDef, ls) ex' ->
        ( foldTupledFunctions ex' funDef ls)) oldExp  foldedTupledFunctions2
      newDefs = L.foldr (\(funDef,_) mp -> M.insert (funName funDef) funDef mp )  
                  M.empty foldedTupledFunctions2
  return (newExp, newDefs)

fuse :: DDefs Ty1 -> FunDefs1 -> Var -> Var-> PassM  (Bool, Var,  FunDefs1)
fuse ddefs fdefs  innerVar  outerVar = do
  let innerFunc =  fdefs M.! innerVar
      outerFunc =  fdefs M.! outerVar
      newVar    = toVar ( (fromVar outerVar) L.++ "_" L.++(fromVar innerVar ))
  newName   <-  gensym_tag (newVar) "inline" 
  let setp1 = inline innerFunc outerFunc (-1)
      step2 =  (simplifyCases setp1 ){funName = newName}
      step3 =  foldFusedCalls_f (outerVar, innerVar, -1, newName)  step2
      step4 =  removeUnusedDefs step3
  return $(True, newName, M.insert  newName step4 fdefs ); 

violateRestrictions :: FunDefs1 -> Var -> Var -> Bool
violateRestrictions fdefs inner outer =
  do
    let innerDef = case (M.lookup inner fdefs) of (Just  v) ->v
        outerDef = case (M.lookup outer fdefs) of (Just v) ->v
        p1 = case (fst (funTy innerDef) ) of
            (PackedTy _ _ ) -> False 
            otherwise  -> True
        p2 = case (fst (funTy outerDef) ) of
            (PackedTy _ _) -> False 
            otherwise  -> True
    (p1 || p2)

transform :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> [(Var, Var, Int, Var)] -> 
  PassM (L Exp1,  FunDefs1, [(Var, Var, Int, Var)])
transform  ddefs funDefs  exp fusedFunctions_= do
  rec exp [] funDefs fusedFunctions_
 where
  rec (L l body) processed fdefs  fusedFunctions = do
    let defTable = buildDefTable body  
        potential = findPotential defTable processed 
    case (potential) of
      Nothing -> do 
        -- final clean and tuple
        let final_clean = removeUnusedDefs_exp (L l body) 
        (tupledBody, tupleDefs) <- tuple ddefs fdefs  final_clean  fusedFunctions
        return $(tupledBody, M.union   fdefs tupleDefs, fusedFunctions)

      Just (inner,outer ) -> 
        if( violateRestrictions fdefs inner outer) 
          then rec (L l body)  ((inner,outer):processed) fdefs fusedFunctions
          else do
             -- fuse
            (validFused, fNew, fusedDefs) <-  (fuse  ddefs fdefs inner outer ) 
            let fused_function = fusedDefs M.! fNew
            let newFusedEntry = (outer,inner, -1, fNew)

            (recAppBody, recAppDefs, retFusedFunctions) <- transform
              ddefs fusedDefs (funBody fused_function) (newFusedEntry : fusedFunctions) 
            --clean 
            let newFusedFunctions =  (newFusedEntry : fusedFunctions) L.++ retFusedFunctions
            let cleaned_function = removeUnusedDefs fused_function{funBody = recAppBody} 
                fdefs_tmp2       = M.union fusedDefs recAppDefs 
                fdefs_tmp3       = M.insert  fNew cleaned_function fdefs_tmp2
            -- tuple
            (tupledBody, tupleDefs) <- tuple ddefs fdefs_tmp3
                                        (funBody cleaned_function) newFusedFunctions
            let tupled_function = cleaned_function{funBody = tupledBody}
                fdefs_tmp4      = M.union   fdefs_tmp3 tupleDefs 
                fdefs_tmp5      = M.insert  fNew tupled_function fdefs_tmp4
                valid = validFused
                newDefs = fdefs_tmp5
            if ( valid==True )
              then let body' = foldFusedCalls (outer,inner, -1, fNew) (L l body) 
              --`debug`  ("final rewrite" L.++ (show outer )L.++ (show inner )L.++ (show fNew )L.++ (show body)) 
                    in rec body' ((inner,outer):processed)
                        (M.union fdefs newDefs) newFusedFunctions
              else  rec (L l body)  ((inner,outer):processed) fdefs fusedFunctions

fusion2 :: Prog1 -> PassM Prog1
fusion2 (L1.Prog defs funs main) = do
    (main', funs') <- case main of 
        Nothing   -> return $ (Nothing, M.empty)
        Just (m, ty)    -> do
            (m', newDefs, _) <- (transform defs funs m [] )
            return (Just (m',ty), M.union funs newDefs)
    return $ L1.Prog defs funs' main'