
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
import Data.Char ( toLower )
import Gibbon.L1.Syntax as L1
import Debug.Trace
import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Gibbon.Common
import Data.Tuple.All
import Data.Vector as V
import Control.Monad

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
  , fun_uses :: ![(Exp1,Int,Maybe Symbol)] -- ^ functions calls that uses the definition
  , all_use_count:: !Int -- ^ total number of uses (calls and not calls)
  } deriving (Show , Generic)
  
type DefTable = M.Map Symbol DefTableEntry 
type PotentialPair = (Symbol, Symbol)
type PotentialsList = [DefTableEntry] 

buildDefTable:: Exp1 -> DefTable
buildDefTable ex  = rec ex M.empty 
 where 
  rec ex table = case (ex) of
    VarE (Var sym) ->  M.update incrUses sym table     
  
    letExpr@(LetE ((Var symLet),_,_,bind) body) ->
      case (getExp bind) of 
          callExp@(AppE _ _ (L _  (VarE (Var sym ))))  -> 
              let table' = M.update (addFunctionUse (callExp,-1, Just symLet))
                     sym table      
              in let table'' = M.insert symLet (DefTableEntry {def=(getExp bind), 
                      fun_uses=[], all_use_count = 0} ) table'
              in rec (getExp body) table''
        
          callExp@(AppE _ _ (L _  (MkProdE argsList))) ->
              let table' = 
                    buildDefTable_args callExp argsList table 0
                      where
                        buildDefTable_args _ [] table _ = table
                        buildDefTable_args callExp (h:tail)  table index = 
                           case (getExp h)  of 
                              VarE (Var sym) -> buildDefTable_args callExp tail
                                 (M.update (addFunctionUse (callExp, index, 
                                   Just symLet))  sym table) (index+1)
                     
                              otherwise    -> buildDefTable_args callExp 
                                  tail  table (index+1)
              in rec (getExp body) table' 

          otherwise -> 
            let table' =  (rec (getExp bind) table) 
            in let table'' = 
                    case (getExp bind) of
                      AppE _ _ _  -> M.insert symLet 
                          (DefTableEntry {def=(getExp bind), fun_uses=[],
                            all_use_count = 0} ) table' 
                      otherwise            ->  table'  
            in rec (getExp body) table''

    callExp@(AppE _ _ (L _  (MkProdE argsList))) -> buildDefTable_args callExp
        argsList table 0
       where
        buildDefTable_args _ [] table _ = table
        buildDefTable_args callExp (h:tail)  table index = case getExp h  of 
            VarE (Var sym) -> buildDefTable_args callExp tail
                (M.update f sym table) (index+1)
              where  f = addFunctionUse (callExp,index, Nothing)
            otherwise       -> buildDefTable_args callExp tail  table (index+1)

    callExp@(AppE _ _ (L _  (VarE (Var sym ))))  -> M.update f sym table 
        where  f = addFunctionUse (callExp,-1, Nothing)
             -- -1 means there is no ProdE ( only one argument)
            
    PrimAppE _ ls ->  L.foldl f table ls
            where  f tbl exp = rec (getExp exp) tbl
 
    IfE cond thenBody elseBody      -> let table' = rec (getExp cond) table 
        in let table'' = rec ( getExp thenBody) table'
        in rec (getExp elseBody) table''
    CaseE e ls      -> let table' = rec ( getExp e) table 
          in L.foldl f table' ls
        where
          f tbl (_, _, exp ) = rec (getExp exp) tbl
   
    DataConE _ _ ls -> L.foldl f table ls where f tbl exp = rec (getExp exp) tbl
    TimeIt exp _ _  -> rec (getExp exp) table   
    ProjE index exp -> rec (getExp exp) table
    otherwise       -> table
   where 
      addFunctionUse newUse ( DefTableEntry  def fun_uses c )=  Just $
         DefTableEntry def (newUse:fun_uses) (c+1) 
     
      incrUses (DefTableEntry  def fun_uses c) = Just $
          DefTableEntry def fun_uses (c+1)

extractAppNameFromLet ::  Exp1 -> Var
extractAppNameFromLet (LetE ((Var symLet),_,_,L _ (AppE var _ _ )) _)  = var

extractLetSymbolFromLet ::  Exp1 -> Symbol
extractLetSymbolFromLet (LetE ((Var symLet),_,_,L _ (AppE var _ _ )) _)  = symLet

extractAppEName ::  Exp1 -> Var
extractAppEName (AppE var _ _ ) = var

-- isInList :: (Var, Var) -> [(Var, Var)] ->Bool
-- isInList (outer, inner ) [] = False;
-- isInList (outer, inner) ((outer',inner'):xs) = 
-- ((fromVar outer)==(fromVar outer') &&
-- (fromVar inner) ==(fromVar inner))||
-- ( isInList (outer, inner ) xs)

-- returns ((innerFun, outerFun), symbol defined by the outer)
findPotential :: DefTable -> [(Var, Var)] -> Maybe ((Var, Var), Maybe Symbol)
findPotential table skipList = 
  ( case (L.find predicate  (M.toList table)) of
    Nothing       -> Nothing --`debug`  (show skipList) 
    Just (_, (DefTableEntry def fun_uses use_count ) ) -> 
        Just ( ( (extractAppEName def),
                 (extractAppEName(sel1 (L.head fun_uses)))), 
                   (sel3 (L.head fun_uses)) ) )
                --   `debug` ("selected is " L.++ show (L.find predicate (L.reverse (M.toList table))))
   where 
    predicate (_,DefTableEntry def fun_uses use_count )  =
      (L.length fun_uses >= 1) && (L.notElem ( (extractAppEName def),
        (extractAppEName(sel1 (L.head fun_uses))) ) skipList ) 
            
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

inline :: FunDef1 -> FunDef1 -> Int  ->  FunDef1
inline inlined_fun outer_fun arg_pos  =  
  -- right now i am only handling when the outer function have one argument 
  -- which is the tree prodcued by the inlined function 
  -- in the future i shoul allow multiple arguments ...
  -- why dont we always make the type prod for simplification !
  -- also right now we assume that the inlined fuction takes one argument which 
  -- is the input tree
  let old_exp  = l $ case (fst (funTy outer_fun)) of
       ProdTy _      ->  error "not handled yet"  
        -- ProjE arg_pos (l (VarE (fst (funArg outer_fun) )) )
       _             ->  VarE (funArg outer_fun)

  in let newFunArg = case  argType_outer  of 
          ProdTy ls -> error "not supported yet"
           -- (argVar, ProdTy (take arg_pos ls  L.++ drop (1 + arg_pos) ls) )
          _         -> case  argType_inlined  of 
              ProdTy ls -> error "not supported yet" 
              -- (argVar, ProdTy (take arg_pos ls  L.++ drop (1 + arg_pos) ls) )
              _         ->  funArg inlined_fun
          where
            argType_outer = fst (funTy outer_fun)
            argVar_outer = funArg outer_fun
            argType_inlined= fst (funTy inlined_fun)
            argVar_inlined = funArg inlined_fun

  in outer_fun { funArg  = newFunArg ,
                 funBody = substE old_exp (funBody inlined_fun) 
                  (funBody outer_fun) }

--  THERE IS AN ASSUMPTION THAT DataConstE takes only list of 
-- variable references ( no nested pattern matching) 
simplifyCases :: FunDef1 -> FunDef1
simplifyCases function = function {funBody = rec ( funBody function) }
  where
    rec ( L l ex)  = case  ex of
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

-- this one as well assumes that one arg  (outer and inner )
 -- > can be changed not to by carrying the deftable around 
foldFusedCalls_f :: (Var, Var, Int, Var) -> FunDef1 -> FunDef1
foldFusedCalls_f rule function = function{funBody= 
  foldFusedCalls rule (funBody function)}

foldFusedCalls :: (Var, Var, Int,Var ) -> L Exp1  ->(L Exp1) 
foldFusedCalls rule@(outerName, innerName, argPos,newName ) body = 
  let defTable = buildDefTable (getExp body)  
  in let rec (L l ex ) = case (ex) of 
          AppE v loc argList -> 
            let ignore = L l $ AppE v loc (rec argList) 
            in if(v ==  outerName) 
                then case (getExp argList ) of 
                  VarE (Var sym) ->
                    if( innerName == getDefiningFuntion sym)  
                      then L l  $AppE  newName loc (getArgs sym) 
                      else ignore -- the outer has only one argument
                   where
                      getDefiningFuntion x = case (M.lookup x defTable) of
                        Nothing    -> (toVar "")
                         --`debug`  ("defined by constructor !!!")
                        Just entry -> case (def  entry) of 
                          AppE v _ _   -> v
                          _            -> error  ("ops" L.++ (show(def  entry)))
                      getArgs x  = case (M.lookup x defTable) of
                        Nothing    -> error  "error in foldFusedCalls"
                        Just entry -> case (def  entry) of 
                          AppE _ _ args-> args
                          _            -> error  ("ops" L.++ (show(def  entry)))
                else
                  ignore 

          LetE (v,loc,t,lhs) bod   ->  L l $ LetE (v,loc,t, (rec lhs)) (rec bod) 
          IfE e1 e2 e3             ->  L l $ IfE (rec e1) ( rec e2) ( rec e3)     
          CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1)
            where
              f (dataCon,x,exp) = (dataCon, x, (rec exp)) 
          TimeIt e d b             ->  L l $ TimeIt ( rec e) d b
          DataConE loc datacons ls ->  L l $ DataConE loc datacons (L.map (\x-> rec x) ls)
          otherwise -> L l ex --`debug` ("here6  ") 
  in rec body

foldTupledFunctions_f :: ( FunDef1) ->[Var] ->PassM (FunDef1)
foldTupledFunctions_f funDef ls =
  do 
    body <- (foldTupledFunctions (funBody funDef ) funDef ls )
    return funDef {funBody =body}

foldTupledFunctions ::   L Exp1 -> ( FunDef1) -> [Var] -> PassM (L Exp1)
foldTupledFunctions body newFun oldCalls =
  do
     x <- (rec  body  M.empty) 
     return x 
  where
    rec (L l ex) mp =  
      do
      case (ex) of 
        p@(LetE (Var y, loc, t,rhs@(L _ (AppE f _ (L l (VarE input) )) )) body) ->
          do
            case (L.elemIndex f oldCalls ) of 
              Nothing ->
                do 
                  rhs' <- (rec rhs mp)
                  body' <- (rec body mp)
                  return ( L l $ LetE (Var y, loc, t, rhs')  body' )
              Just i  -> 
                do
                  case (M.lookup input mp) of --
                    Nothing  -> 
                      do 
                        newVar <- gensym (toVar ((fromVar input) L.++ "_unq_"))
                        let newMp = M.insert input newVar mp
                        body' <- (rec (L l p) newMp)
                        return ( L l $ LetE (newVar, [], (outTy (funTy newFun)),
                          (L l  (AppE (funName newFun) [] ( L l (VarE input) ))))
                             body') 
                                             
                    Just k   -> 
                      do 
                        body' <- ( rec body mp)
                        return( L l $ LetE (Var y, loc, t, L l (ProjE i  
                          (L l $ VarE k))) body')

        AppE name loc e          -> do
             e'<- (rec e mp)
             return $ L l $ AppE name loc   e'
        PrimAppE x ls            -> do 
            ls' <- (Prelude.mapM (\item -> (rec item mp)) ls)
            return $ L l $ PrimAppE x ls'
       
        LetE (v,loc,t,rhs) bod   -> do 
            body' <- (rec bod mp)
            rhs' <- (rec rhs mp)
            return $L l $LetE (v,loc,t, rhs') body'  
        IfE e1 e2 e3             -> do 
          e1' <- (rec e1 mp)
          e2' <- (rec e2 mp)
          e3' <- (rec e3 mp)
          return$ L l $ IfE e1' e2' e3'
       
        MkProdE ls               -> do 
          ls' <- (Prelude.mapM (\item -> (rec item mp)) ls)
          return $  L l $ MkProdE ls' 
        ProjE index exp          -> do 
          exp' <- (rec exp mp)
          return $ L l $ ProjE index exp' 
        CaseE e1 ls1 ->  do
          e1' <- ( rec e1  mp)
          ls' <- (Prelude.mapM (\(dataCon,x,exp)->
            do 
              exp' <- (rec exp mp)
              return (dataCon, x, exp')  
              ) ls1)
          return  $ L l $ CaseE e1'  ls'
         
               
        DataConE loc datacons ls -> do
          ls' <- (Prelude.mapM (\x-> (rec x mp)) ls)
          return $ L l $ DataConE loc datacons ls'
        TimeIt e d b             -> do 
          e'<-  rec e mp
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
tupleListOfFunctions :: DDefs Ty1 -> [FunDef1] -> (FunDef1, [Var] )
tupleListOfFunctions  ddefs ls = do
  let newName = L.foldl  appendName "" ls 
       where
        appendName tmp function = (tmp  L.++ "_t_" L.++ (fromVar (funName function)))  
  let lsVector    = V.fromList ls 
      retTypes    = V.map (\f -> (outTy (funTy f))) lsVector
      newRetType  = ProdTy (V.toList retTypes)  
      newArgVar = toVar "input"
      traversedType = inTy (funTy (L.head ls))
      newArgs = newArgVar
      step1 = L.map getBody ls 
       where
        getBody fun = substE  (l (VarE (funArg( L.head ls))) ) 
          (l (VarE newArgVar)) (funBody fun)  
      step2 = L.map mapAndSplit step1  
         where 
          mapAndSplit (L _(CaseE e ls)) = L.foldr f M.empty ls 
          f (dataCons, varls, exp) mp = M.insert dataCons (subsVars exp) mp
           where 
            subsVars ex = V.ifoldr subsVar ex (V.fromList varls) 
            subsVar index v ex   = substE  (l (VarE (fst v) )) 
              (l (VarE (toVar (L.map toLower (dataCons L.++ (show index)))))) ex

  let inputDef = lookupDDef ddefs typeStr 
        where 
          typeStr = case traversedType of
              (PackedTy typeStr _) -> typeStr --`debug`  (show traversedType L.++ (show ls)) 
              x -> error "not expected "`debug`  (show x )
      dataConsList = dataCons inputDef
      createOutVar index =  (toVar ("f" L.++(show index)L.++"out" )) 
 
  let  outPart = l ( MkProdE  genL  )
        where
          genL = V.toList $ 
            V.imap (\index _ ->l (VarE ( createOutVar index) ) ) (V.fromList ls)
  
  let retAllExp = MkProdE $
       V.toList ( V.imap (\index _ ->l (VarE (createOutVar index))) lsVector )
  let reduceStep = L.foldr reduce (CaseE (l (VarE newArgVar))[]) dataConsList 
       where
        reduce (dataCons, varls) (CaseE ex ls ) = CaseE ex ((consBody):ls) 
          where 
           consBody = (dataCons, newVarsList, combinedBodies) 
             where
              newVarsList = V.toList( V.imap 
                (\index _ -> ( toVar (L.map toLower (dataCons L.++ (show index))) ,() ) )
                  (V.fromList varls) ) 
              combinedBodies  =  V.ifoldr (\index body res  ->
                l (LetE ((createOutVar index),[],(unsafeIndex retTypes index),
                  body) res )) (l retAllExp) (V.fromList partialList)
               where
                 partialList =  L.map  helperFunc step2 
                  where 
                    helperFunc m = case ( M.lookup dataCons m) of 
                      (Just a ) -> a 
                      (Nothing) -> error "ooopsa1"

      funNames = L.map (\f -> funName f ) ls                                                                                          
  (FunDef (toVar ("_TUP_" L.++ newName L.++ "_TUP_") ) newArgs (traversedType,
    newRetType) (l reduceStep) , funNames)

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

-- the return of this function is map from variables to their consumers
buildUseTable::   L Exp1 -> M.Map Var [(Var, Exp1)]
buildUseTable ex  = 
  rec  ex (M.fromList []) 
 where
  rec (L l ex) tb = case ex of 
      AppE _ _ _               -> tb 
      PrimAppE _ _             -> tb
      LetE (v,_,_,(L _ callexp@(AppE _ _ (L _ (VarE par )) ) )) body ->  
          M.alter f par (rec body tb) 
        where -- add a check to make sure that the call exp represent a traversal
               -- and is not a simple functions call
           f Nothing   = Just [(v,callexp)]
           f (Just ls) = Just ((v,callexp):ls) 
      LetE (v,_,_,rhs) body    ->
        let t1 = rec rhs tb
          in rec body t1  
      IfE e1 e2 e3             -> let t1 = rec e1 tb 
                                      t2 = rec e2 t1
                                  in rec e3 t2 
      MkProdE ls               -> tb 
      ProjE index exp          -> tb
      CaseE e1 ls1             ->  
          let t1 = rec e1 tb in 
          L.foldl f t1 ls1 -- `debug` ("\nhandling in case \n" L.++ (show ls1 ))
         where 
          f table (_ ,_ ,exp) = rec exp table --`debug` ("\nhandling subecpr of case \n" L.++ (show exp ))
      DataConE loc datacons ls -> L.foldl f tb ls where f table exp = rec exp table 
      TimeIt exp _ _           -> rec exp tb  
      otherwise                -> tb --`debug` ("noooo" L.++ (show x))

-- In each set of a functions to be tupled we want them to all start with a case
-- on the input tree or all start with an If such that e1 is the same for all of them !
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

tuple :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> [(Var, Var, Int, Var)] ->
    (M.Map [Var] FunDef1 ) ->  PassM (L Exp1,  FunDefs1)
tuple ddefs fdefs oldExpIn fusedFunctions prevTupledFunctions = do
  -- we folded previously tupled functions here 
  oldExp <- Control.Monad.foldM (\ex' (funDef, ls)->
    ( foldTupledFunctions ex' funDef ls)) oldExpIn  (L.map (\(a,b)-> (b,a)) 
      (M.toList prevTupledFunctions))

  let useTable         = buildUseTable oldExp --`debug` (show oldExpIn L.++ "\n------\n"L.++ (show oldExp))
      candidates = L.filter checkLength (L.nub (L.map processEntry (M.toList useTable) ))
                where
                  processEntry (_, ls) = L.nub (L.sort (L.map extractFuncName ls))
                  extractFuncName (_,(AppE fName _ _ )) = fName
                  checkLength entry = (L.length entry >1)

      functionsToTuple = L.map (\ls -> L.map getFunDef ls) candidates --`debug` ( (show oldExp)L.++"candidates for tupling:"L.++ (show candidates)L.++ "from :\n"L.++ (show useTable) )
                        where
                         getFunDef fName  = case ( M.lookup fName fdefs ) of 
                           Nothing     ->error ("not expected" L.++ (show fName))
                           Just funDef -> funDef
      functionsToTuple_filtered = 
        L.filter traversePackedType functionsToTuple  -- filter out functions that does not traverse a packed type
          where  -- wee need to add more checks here TODO: ... also exclude previously fused ones 
            traversePackedType entry = 
              case ((fst(funTy(L.head entry)))) of
                (PackedTy typeStr _)->True  
                _ -> False

      freshBody f = do 
        b' <- freshExp [] (funBody f)
        return f{funBody =b'}
        
  functionsToTuple <- Prelude.mapM ( \ls->  (Prelude.mapM freshBody  ls))  
                         functionsToTuple_filtered   --L.filter check2 functionsToMerge
  
  let unfoldedTupledFunctions = L.map (tupleListOfFunctions ddefs) functionsToTuple
      -- for each tupled function fold the previously fused calls in it
      foldedTupledFunctions   = L.map ( \(funDef,ls) ->
        ((L.foldr (\entry fdef -> foldFusedCalls_f entry fdef) funDef 
          fusedFunctions),ls))  unfoldedTupledFunctions    

  foldedTupledFunctions2   <-  (Prelude.mapM (\(funDef,ls) ->  
          do 
            foldedFunc <-  foldTupledFunctions_f funDef ls
            return ((foldedFunc) ,ls)) 
          foldedTupledFunctions  )
  
  let newDefs = L.foldr (\(funDef,_) mp -> M.insert (funName funDef) funDef mp )
        M.empty foldedTupledFunctions2

  foldedTupledFunctions3WithFDefs <-
        Prelude.mapM  ( \(funDef, ls) ->
            do
                let preFusedPar = M.union prevTupledFunctions (M.fromList 
                      (L.map (\(a,b)->(b,a)) foldedTupledFunctions2))

                (newBody, newFunctions) <- tuple ddefs  (M.union fdefs newDefs) 
                    (funBody funDef) fusedFunctions preFusedPar 

                return ((funDef{funBody = newBody }, ls), newFunctions)
          
           ) foldedTupledFunctions2

  let foldedTupledFunctions3 = L.map (fst) foldedTupledFunctions3WithFDefs

  let  recGeneratedDefs = L.foldr (\item mp -> M.union item mp) M.empty
         (L.map (snd) (foldedTupledFunctions3WithFDefs))

  newExp <- Control.Monad.foldM (\ex' (funDef, ls)->
        ( foldTupledFunctions ex' funDef ls)) oldExp  foldedTupledFunctions3
  
  let newDefsFinal = L.foldr (\(funDef,_) mp -> M.insert (funName funDef) funDef mp )
        M.empty foldedTupledFunctions3

  return (newExp,M.union newDefsFinal recGeneratedDefs )

fuse :: DDefs Ty1 -> FunDefs1 -> Var -> Var -> [(Var, Var, Int, Var)]
 -> PassM  (Bool, Var,  FunDefs1)
fuse ddefs fdefs  innerVar  outerVar fusedFunctions_ = do
  let innerFunc =  fdefs M.! innerVar
      outerFunc =  fdefs M.! outerVar
      newVar    = toVar ("_FUS_f_" L.++ (fromVar outerVar) L.++ "_f_" L.++(fromVar innerVar ) L.++ "_FUS_")
  --newName   <-  gensym_tag (newVar) "inline" 
  let newName  = newVar
  innerFreshBody <- freshExp []  (funBody innerFunc)
  outerFreshBody <- freshExp []  (funBody outerFunc)
  let setp1 = inline innerFunc{funBody =innerFreshBody}
               outerFunc{funBody = outerFreshBody}  (-1)
      step2 =  (simplifyCases setp1 ){funName = newName}
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
            otherwise  -> True
        p2 = case (fst (funTy outerDef) ) of
            (PackedTy _ _) -> False 
            otherwise  -> True
    (p1 || p2)

transform :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> [(Var, Var, Int, Var)] -> 
  Bool -> [(Var, Var)] ->  PassM (L Exp1,  FunDefs1, [(Var, Var, Int, Var)])
transform  ddefs funDefs  exp fusedFunctions_ doTupling processedCandidates= do
  rec exp processedCandidates funDefs fusedFunctions_
 where
  rec (L l body) processed fdefs  fusedFunctions = do
    let defTable = buildDefTable body  
        potential = findPotential defTable processed 
    case (potential) of
      Nothing -> do 
        -- final clean and tuple
        let final_clean = removeUnusedDefs_exp (L l body)
        -- let (tupledBody, tupleDefs) = (final_clean, M.empty)
        (tupledBody, tupleDefs) <- do
          if (doTupling)
            then tuple ddefs fdefs  final_clean  fusedFunctions (M.fromList []) 
            else return (final_clean, M.empty)
        return $(tupledBody, M.union fdefs tupleDefs, fusedFunctions) 

      Just ((inner,outer), outerDefVarSymbol) -> 
        if( violateRestrictions fdefs inner outer) 
          then rec (L l body)  ((inner,outer):processed) fdefs fusedFunctions
          else do
             -- fuse
            (validFused, fNew, fusedDefs) <-  (fuse  ddefs fdefs inner outer 
               fusedFunctions_ )  
            let fused_function = fusedDefs M.! fNew 
            let newFusedEntry = (outer,inner, -1, fNew)
           
            (recAppBody, recAppDefs, retFusedFunctions) <- transform
              ddefs fusedDefs (funBody fused_function) 
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
            (m', newDefs, _) <- (transform defs funs m [] True [])
            return (Just (m',ty), M.union funs newDefs)
    return $ L1.Prog defs funs' main'
