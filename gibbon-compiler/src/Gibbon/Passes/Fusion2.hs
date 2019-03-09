{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-all #-}

module Gibbon.Passes.Fusion2 (fusion2) where
import Prelude hiding (exp)

import           Control.Exception
import           Data.Loc
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Vector as V
import           Data.Symbol
import           Data.Char ( toLower )
import           Debug.Trace
import           Control.DeepSeq
import           GHC.Generics (Generic, Generic1)
import           Data.Tuple.All
import qualified Data.Vector as V
import           Control.Monad
--import Data.Matrix as Matrix


import Gibbon.Common
import Gibbon.Passes.Freshen (freshExp1)
import Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

debug =  flip (dbgTrace 3)

{-

E.g.

    gibbon_main =
      let tinput = generateTree
          t1 = travers1(tinoput)
          t2 = traverse2(tinput)
      in 10

For htis program, the DefTAble looks like:

  {
    tinput -> DefTableEntry { def      = generateTree
                            , fun_uses = [ (traverse1(..), 0 , t1), (traverse2, 0 , t2) ],
                              all_use_count = 2
                            }

    t1 -> DefTableEntry { def      = traverse1(..)
                        , fun_uses = [ ],
                        , all_use_count = 0
                        }
  }

-}


type DefTable = M.Map Symbol DefTableEntry

{- There will be one entry for each variable in the table. Each entry consist of
    1)The function application expression.
    2)The index at which the definition  appears at in the argument list.
    3)The defined symbol, if the the consuming expression of the form let x=App.
-}
data DefTableEntry = DefTableEntry
  { def           :: !Exp1 -- ^ The expression that defines this variable
  , fun_uses      :: ![FunctionUses] -- ()
  , all_use_count :: !Int -- ^ total number of uses (calls and not)
  } deriving (Show , Generic)

type FunctionUses =
  ( Exp1 -- The AppE that uses a variable.
  , Int  -- i where variable V is the i'th argument in this function call.
  , Maybe Symbol -- The variable that binds this AppE.
  )


type PotentialPair = (Symbol, Symbol)
type PotentialsList = [DefTableEntry]

removeCommonExpressions ::  L Exp1->  L Exp1
removeCommonExpressions exp = go exp
   where
    go exp  = case (unLoc exp) of
      LetE (v, ls, t, bind) body ->
        case (unLoc bind) of
            ProjE i e ->
              let oldExp = l $ VarE v
                  newExp = l $ ProjE i e
                  body' = substE oldExp newExp body
              in go (body')-- `debug` ("replace ::"L.++ (show oldExp) L.++ "with" L.++ (show newExp))
            VarE v' ->
              let oldExp = l $ VarE v
                  newExp = l $ VarE v'
                  body' = substE oldExp newExp body
              in go (body')
            otherwise ->
              let oldExp = bind
                  newExp = l $ VarE v
                  body' = substE oldExp newExp body --`debug` ("removing duplicates of "L.++ (show oldExp))
              in l$ LetE (v, ls, t, bind) (go body')
      IfE cond thenBody elseBody ->
        l $ IfE (go cond) (go thenBody) (go elseBody)

      CaseE e ls      -> let ls' = L.map (\(x, y, exp) -> (x, y, go exp)) ls
          in  l$ CaseE e ls'

      TimeIt exp x y  ->l $   TimeIt (go exp) x y
      x       -> l $x

simplifyProjectionsOfProducts :: L Exp1->  L Exp1
simplifyProjectionsOfProducts exp = go exp M.empty
   where
    go exp mp = case (unLoc exp) of
      LetE (v, ls, t, bind) body ->
        case (unLoc bind) of
            MkProdE prodList ->
              let bind' = go bind mp
                  mp' = M.insert v (V.fromList prodList) mp
                  body' = go body mp'
              in l $  LetE (v, ls, t, bind')  body'
            otherwise ->
              let bind' = go bind mp
                  body' = go body mp
              in  l $  LetE (v, ls, t, bind')  body'

      IfE cond thenBody elseBody ->
        l $ IfE (go cond mp ) (go thenBody mp ) (go elseBody mp)

      CaseE e ls      -> let ls' = L.map (\(x, y, exp) -> (x, y, go exp mp)) ls
          in  l$ CaseE (go e mp) ls'

      PrimAppE p ls ->
        let ls' = L.map (\exp -> go exp mp) ls
        in l $ PrimAppE p ls'

      TimeIt exp x y  ->l $   TimeIt (go exp mp) x y

      L1.ProjE i e ->
        case (unLoc e ) of
          VarE v ->
            case(M.lookup v mp ) of
               Nothing ->  l $ L1.ProjE i e
               Just ls -> ls V.! i
          otherwise -> l $ L1.ProjE i (go e mp)
      DataConE x y ls->
        let ls' = L.map (\exp -> go exp mp) ls
        in l$ DataConE x y ls'
      AppE v loc args  ->
        l $   AppE v loc (map (\a -> go a mp) args)
      MkProdE ls->
        let ls' = L.map (\exp -> go exp mp) ls
        in  l$   MkProdE ls'

      x       -> l $x

-- This function optimizes the tupled function by removing redundant output
-- parameters and their computation
-- The function optimized function is a single case expression, the pass will
-- look at the leaf expression for each possible match, those are tuples of the
-- same size (prev optimizations guarantee that )
-- if all two position are the same in all of them
-- (X1, X2, X3, X4 = X1, X5) if X1= X4 for all of them then eliminate X4.
removeRedundantOutput :: FunDef1 -> (FunDef1, M.Map Int Int, [Int])
removeRedundantOutput fdef =
    let outputTuples = V.fromList  (collectOutputs (funBody fdef)) in
    let firstTuple = outputTuples V.! 0   in --return vecto
    let candidates = (V.ifoldl
          (\ls idx exp ->
            let matches =  V.findIndices (\ex-> ex==exp )  firstTuple
                cands =  L.map (\i -> (idx,i)) (V.toList matches)  --`debug` (show matches)
            in (ls L.++ cands)
          ) [] firstTuple )
        ncols = V.length firstTuple
        nrows = V.length outputTuples

        candidates2 = L.filter  alwaysMatches candidates
           where
             alwaysMatches (i,j)=
              let ls1 = L.map
                    (\r ->  let row = (outputTuples V.! r)
                                v1 =  row V.! i
                                v2 =  row V.! j
                            in  v1==v2)  [0..(nrows -1)]
              in (i < j) && (L.foldl (\out v-> out && v) True ls1)

        initialMap = M.fromList (L.map (\i -> (i, []) )
            [0..(ncols-1)])

    --    tricky!
        finalMap = L.foldl
            (\mp (i, j) ->
              let k = L.foldl
                    (\k idx -> if(k /= -1)
                       then k
                       else
                         case (M.lookup idx mp) of
                           Nothing -> k
                           Just ls ->
                             case (L.elemIndex i ls) of
                                Nothing -> k
                                otherwise -> idx
                    ) (-1) [0..i]
                  mp' = M.delete j mp
              in if(k== -1)
                  then (M.insert i ((mp' M.! i) L.++ [j] ) mp')
                  else (M.insert k ((mp' M.! k) L.++ [j] ) mp')
            ) initialMap candidates2

        removedPositions = L.foldl
           (\ls i ->
            case (M.lookup i finalMap ) of
              Nothing -> ls L.++[i]
              otherwise -> ls
          ) [] [0..(ncols-1)]

        newFunType =
          let oldOutTypesList = V.fromList (
                case (snd(funTy fdef)) of ProdTy ls->ls)
              newOutTypesList = V.ifoldl
                (\ls idx ty ->
                   case (L.elemIndex idx removedPositions) of
                      Nothing -> (ls L.++[ty])
                      otherwise-> ls
                ) [] oldOutTypesList
          in (fst(funTy fdef), ProdTy newOutTypesList )

        newOutputTuples = V.map (\ls -> removeDropped ls) outputTuples
          where
            removeDropped ls = MkProdE ( V.ifoldl
               (\ls idx exp ->
                  case (L.elemIndex idx removedPositions) of
                    Nothing -> (ls L.++[exp] )
                    otherwise -> ls
               ) [] ls )

        newFunBody = case (unLoc (funBody fdef)) of
          CaseE e ls ->
              let ls' = V.toList (V.imap
                   (\idx (x, y, exp)->
                        let exp' = replaceLeafExp exp ( l (newOutputTuples V.! idx) )
                        in (x, y, exp')) (V.fromList ls))
              in  l$ CaseE e ls'
        fdef' = fdef{funBody = newFunBody, funTy = newFunType}
        redirectMap = V.ifoldl
            (\mp idx (i,ls)->
                let mp' = M.insert i idx mp
                    mp'' = L.foldl (\m j -> M.insert j idx m) mp' ls
                in mp''
            ) M.empty (V.fromList (M.toList finalMap))

    in (fdef', redirectMap, removedPositions)--`debug` ("candidates:"  L.++(show newFunBody)L.++ "\n" L.++ (show removedPositions))

 where
  replaceLeafExp exp replacement =
    case (unLoc exp) of
      LetE (v, ls, t, bind) body ->
         l $  LetE (v, ls, t, bind) (replaceLeafExp body replacement)
      MkProdE ls -> replacement

  collectOutputs exp = case (unLoc exp) of
    CaseE e ls ->
         L.map (\(x, y, subBody) -> V.fromList(extractLeafTuple subBody)) ls
     where
        extractLeafTuple exp =
           case (unLoc exp) of
              LetE (v, ls, t, bind) body -> extractLeafTuple(body)
              MkProdE ls -> ls
              otherwise -> error ("not expected expression")

    otherwise -> error("should be case expression")

replaceLeafWithBind :: L Exp1 -> (Int -> Var) -> Ty1 -> L Exp1 -> L Exp1
replaceLeafWithBind exp genVar varType tailExp =
  go exp
   where
     go ex =
      case (unLoc ex) of
          L1.LetE (v,ls,t, e1) e2 -> l $ L1.LetE (v,ls,t, e1)  (go e2)
          x -> case (varType) of
              ProdTy ls2 ->
                  let xDestructed = V.fromList (case  x of MkProdE ls -> ls)
                      newExp = V.ifoldl
                              (\tExp subscript ty ->
                                let newVar = genVar subscript
                                in l $L1.LetE (newVar,[],ty, (xDestructed V.! subscript)) tExp
                              ) tailExp (V.fromList ls2)
                  in newExp
              otherwise ->
                let newVar = genVar 0
                in  l $L1.LetE (newVar,[],varType, l (x)) tailExp


{- This functions collect the following information for each defined variable:
  1) The defining expression. (stored in DefTableEntry::def)
  2) The consumer of the definition that are candidates for fusion;the function
  is consumed in the first argument. (stored in DefTableEntry::fun_uses)
  not: uses mutual exclusive paths are counted by adding them (each is
  considered  a use).
  3) Total number of uses (references) of the defined variable.
-}
buildDefTable :: Exp1 -> DefTable
buildDefTable ex  = go ex Nothing M.empty
 where
  go ex definingSymbol table = case (ex) of
    VarE (Var sym) ->  M.update incrUses sym table

    LetE ((Var symLet),_,_,bind) body ->
      let table' = M.insert symLet (DefTableEntry {def=(unLoc bind),
                    fun_uses=[], all_use_count = 0} ) table
          table'' = go (unLoc bind) (Just symLet) table'
      in go (unLoc body) definingSymbol table''

    -- The thing that is traversed is always the first argument.
    -- Here, we record a function use for the first argument
    -- in the DefTable.
    --
    -- add function uses of interest
    -- [functions calls traversing tree in first argument]
    AppE fName _ args ->
      let addFunctionUse newUse (DefTableEntry def fun_uses c) =
            Just $ DefTableEntry def (newUse:fun_uses) (c)

          table' = case unLoc (args !! 0) of
                     VarE (Var sym) ->
                       M.update (addFunctionUse (ex, 0, definingSymbol))
                                sym table
                     -- If it's anything else, it's not a candidate for fusion, and
                     -- we can ignore it.
                     _   -> table
      in foldl (\acc a -> go (unLoc a) Nothing acc) table' args

    MkProdE argsList -> buildDefTable_args  argsList table
        where
          buildDefTable_args [] tb  = tb
          buildDefTable_args  (h:tail)  table  = buildDefTable_args
            tail (go (unLoc h) Nothing table)

    PrimAppE _ ls ->  L.foldl f table ls
            where  f tbl exp = go (unLoc exp) Nothing tbl

    IfE cond thenBody elseBody      -> let table' = go (unLoc cond) Nothing table
        in let table'' = go ( unLoc thenBody) definingSymbol table'
        in go (unLoc elseBody) definingSymbol table''

    CaseE e ls      ->
        let table' = go (unLoc e) Nothing table
        in L.foldl f table' ls
      where
        f tbl (_, _, exp) = go (unLoc exp) definingSymbol tbl

    DataConE _ _ ls -> L.foldl f table ls
     where
       f tbl exp = go (unLoc exp) Nothing tbl
    TimeIt exp _ _  -> go (unLoc exp) definingSymbol table
    ProjE index exp -> go (unLoc exp) Nothing table
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

-- Takes the table, and candidates which are already processed and
-- return one that isn't.
--
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
      AppE var _ _  -> (L.length fun_uses >= 1) &&
                       (L.notElem (extractAppEName def, extractAppEName(sel1 (L.head fun_uses))) skipList)
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

{-
  The type of the new function is defined as the following :
   if 
     innerType = TreeX-> Args1... -> RetType1
     outerType = RetType Args2... -> RetType2
  then 
     inlinedType = TreeX -> Args1... ->  Args2... -> RetType2

-}

inline :: FunDef1 -> FunDef1 -> Int  ->  PassM FunDef1
inline inlined_fun outer_fun arg_pos  =  do
  newArgVar <- gensym(toVar("inputTree"))

  let argTypes_outer  = fst (funTy outer_fun)
      retType_outer   = snd (funTy outer_fun)
      argVar_outer    = head $ funArgs outer_fun
      argTypes_inlined = fst (funTy inlined_fun)
      argVar_inlined  = head $ funArgs inlined_fun
      retTypeInlined = snd (funTy inlined_fun)

      -- get it as item in list
      traversedType = head argTypes_inlined

    
      -- All arguments except the one that's traversed.
      sideArgsTypesInlined = tail argTypes_outer
      sidArgsTypesOuter    = tail argTypes_inlined

      newType = ([traversedType] ++ sideArgsTypesInlined ++ sidArgsTypesOuter,
                 retType_outer)

      inlinedFunBody = let oldExp  = l$ VarE argVar_inlined
                           newExp  = l$ VarE newArgVar
                       in substE oldExp newExp (funBody inlined_fun)

  
  let oldExp = l $ VarE argVar_outer
  let replaceWithCall exp =
        do 
          newVar <- gensym (toVar "innerCall")
          let rhs = l (AppE (funName inlined_fun) [] 
                        (L.map (\var -> (l (VarE var))) (funArgs inlined_fun)))
              body = substE oldExp (l (VarE newVar)) exp
          return $ l $ LetE (newVar, [], retTypeInlined, rhs) body
                     
  newBody <- do
     -- we inline the body of the inlined function in the e1 otherwise if it
     -- appears anywhere else we create a call to the inlined function. 
     case (unLoc (funBody outer_fun)) of
         CaseE e1 ls -> do
            ls' <- Prelude.mapM (\(dataCon, vars, exp) ->
                     do
                       newInnerExp <- replaceWithCall exp
                       return  (dataCon, vars, newInnerExp)
                    ) ls

            return $ l ( CaseE (substE oldExp inlinedFunBody e1) ls')
         exp ->
                  do
                    newInnerExp <- replaceWithCall (l exp)
                    return newInnerExp
  

  return outer_fun {funArgs = [newArgVar], funTy = newType, funBody = newBody}

-- inlineArgumentProjections :: FunDef1 -> FunDef1
-- inlineArgumentProjections function = case (fst(funTy function)) of
--     ProdTy _->   function {funBody = go (funBody function)}
--       where
--         go (L l ex)  = case  ex of
--           LetE (v,loc,t,rhs) body ->
--               case (unLoc rhs) of
--                 proj@(ProjE i (L _ (VarE v1))) ->
--                   if (v1 == (funArg function))
--                     then
--                       let oldEx  =  L l $ VarE v
--                           newExp =  L l $ proj
--                       in substE oldEx newExp (go body)
--                     else
--                      L l $ LetE (v,loc,t,(go rhs)) (go body)
--                 _ ->
--                     L l $LetE (v,loc,t,(go rhs)) (go body)
--           CaseE e1 ls1  ->
--                L l$ CaseE e1 (L.map f ls1)
--              where
--                f (dataCon, x, exp) = (dataCon, x, go exp)
--           AppE v loc e             ->  L l $ AppE v loc $ go e
--           IfE e1 e2 e3             ->  L l $ IfE (go e1) ( go e2) ( go e3)
--           TimeIt e d b             ->  L l $ TimeIt ( go e) d b
--           _                        -> L l ex

--     _ -> function

-- This function simplify the case expression when the matched expression 
-- is it self another case expression. In the same way wadler to it.

simplifyCases :: FunDef1 -> FunDef1
simplifyCases function = function {funBody = go ( funBody function) }
  where
    go ex  = case (unLoc ex) of

      CaseE e1@(L _  (CaseE e2 ls2)) ls1 -> 
          go (l (CaseE e2 (L.map f ls2)))
        where
          f oldItem = upd3 (l (CaseE (sel3 oldItem) ls1)) oldItem
     
      CaseE e1@(L l (DataConE loc k constructorVars)) caseList ->
          let newBody = L.find (\item-> sel1 item ==k) caseList
          in case newBody of
               Nothing -> error "unmatched constructor!"
               Just (k, caseVars, caseExp)  ->
                    go $case_subst constructorVars caseVars caseExp
                  where
                    case_subst (x1:l1) (x2:l2) exp = 
                        subst (fst x2) (x1) (case_subst l1 l2 exp)
                    case_subst [] [] exp = exp

      CaseE (L _ (IfE e1 e2 e3) ) ls          -> go $
         l $ IfE e1 (l (CaseE e2 ls)) (l (CaseE e3 ls) )

      -- CaseE e1@(L _  (LetE bind body )  ) ls1  ->  
      --   let body' = l $ go (l (CaseE body (ls1))) 
      --   in l $ LetE bind body'
      
      -- CaseE e1 ls1                              -> 
      --    l $ CaseE e1 (L.map f ls1)
      --   where
      --     f item = (upd3 (go (sel3 item)) item)
      LetE (v, loc, t, rhs) bod   ->  l  $ LetE (v,loc,t, (go rhs)) (go bod)
      AppE v loc expList          ->
          l  $ AppE v loc  (L.map (\ex -> go ex) expList) 
      IfE e1 e2 e3             ->  l  $ IfE (go e1) ( go e2) ( go e3)
      TimeIt e d b             ->  l  $ TimeIt ( go e) d b
      ex                       ->  l ex


foldFusedCalls_f :: (Var, Var, Int, Var) -> FunDef1 -> FunDef1
foldFusedCalls_f rule function = function{funBody=
  foldFusedCalls rule (funBody function)}

-- check note** just above the inline function
foldFusedCalls :: (Var, Var, Int,Var ) -> L Exp1  ->(L Exp1)
foldFusedCalls rule@(outerName, innerName, argPos, newName) body =
  let defTable = buildDefTable (unLoc body)
  in let go (L l ex ) = case (ex) of
          AppE fName loc argList ->
            let notFolded = L l $ AppE fName loc (go argList)
            in if(fName ==  outerName)
                then
                  case (unLoc argList ) of
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


          LetE (v,loc,t,lhs) bod   ->  L l $ LetE (v,loc,t, (go lhs)) (go bod)
          IfE e1 e2 e3             ->  L l $ IfE (go e1) ( go e2) ( go e3)
          CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1)
            where
              f (dataCon,x,exp) = (dataCon, x, (go exp))
          TimeIt e d b             ->  L l $ TimeIt ( go e) d b
          DataConE loc datacons ls ->  L l $ DataConE loc datacons
            (L.map (\x-> go x) ls)
          otherwise -> L l ex

  in go body
      where
        getDefiningFunction x defTable = case (M.lookup x defTable) of
            Nothing    -> (toVar "-1not-used-vars")
            Just entry -> case (def  entry) of
                  AppE v _ _   -> v
                  _            -> (toVar "-1not-used-var")
        getArgs x defTable = case (M.lookup x defTable) of
             Nothing    -> error  "error in foldFusedCalls"
             Just entry -> case (def  entry) of
                  AppE _ _ args-> case (unLoc (args)) of
                      MkProdE ls -> ls
                      x          -> [l x]
                  _            -> error  ("ops" L.++ (show(def  entry)))

-- foldTupledFunctions_f :: ( FunDef1) ->[Var] ->PassM (FunDef1)
-- foldTupledFunctions_f funDef ls =
--   do
--     body <- (foldTupledFunctions (funBody funDef ) funDef ls )
--     return funDef {funBody =body}

-- ok wait what !!? this list is re ordered do ge the canonical representation
-- we cared originally about which one is first ,, omg what are you talking about
-- how did i used to resolve ths projection then !!

foldTupledFunctions ::   L Exp1 -> (FunDef1) -> [Exp1] -> Exp1 -> V.Vector Int ->
  Maybe (M.Map Int Int) -> PassM (L Exp1)
foldTupledFunctions body newFun oldCalls firstCall outputPositions redirectMap =

  do
     newVar <- gensym (toVar ("tupled_output"))
     x <- (go body  newVar)
     return x
  where
    go (L l ex) newVar =  do
      case (ex) of
        LetE (Var y, loc, t, rhs) body ->
          do
            case (L.elemIndex (unLoc rhs) oldCalls) of
              Nothing ->
                do
                  rhs' <- (go rhs newVar)
                  body' <- (go body newVar)
                  return ( L l $ LetE (Var y, loc, t, rhs')  body' )
              Just i ->
                do
                  -- replace the call with the call to the tupled function
                  -- then replace each usage of the result of the old call with

                  if (firstCall == (unLoc rhs))
                    then
                      do
                        body' <- go body newVar
                        let args = L.foldl f [] oldCalls
                             where
                              f ls1 exp = ls1 L.++ (extractArgs exp)
                              extractArgs exp = case exp of
                                 AppE _ _  args->
                                    case (unLoc args) of
                                       MkProdE (h:tail) -> tail
                        let args' = L l $ MkProdE ((getFirstArg rhs):args)
                             where
                              getFirstArg (L _ ( AppE _ _ (L _  (MkProdE (h:_)))))= h

                        let rhs' =  L l $AppE (funName newFun) [] args'
                        let bindType = (outTy (funTy newFun))
                        let rhs'' =  case t of
                              ProdTy ls -> L l ( MkProdE (
                                V.toList ( V.imap (\index _ ->
                                  let idx = case redirectMap of
                                        Nothing -> (outputPositions V.! i )+index
                                        Just mp -> mp M.! ((outputPositions V.! i )+index)

                                  in L l $ ProjE (idx) ( L l $ VarE newVar) )
                                      (V.fromList ls)  ))  )

                              otherwise ->
                                  let idx = case redirectMap of
                                         Nothing -> (outputPositions V.! i )
                                         Just mp -> mp M.! (outputPositions V.! i )
                                  in L l  $ ProjE (idx) ( L l $ VarE newVar)-- not complete buggy (i +eps)
                        let body'' =   L l $ LetE (Var y, loc, t, rhs'') body'
                        return ( L  l $LetE (newVar, [], bindType, rhs') body'')
                    else
                      do
                        body' <- ( go body newVar) --`debug` ("\nhere\n")
                        let rhs' =  case t of
                              ProdTy ls -> L l ( MkProdE (
                                V.toList ( V.imap (\index _ ->
                                  let idx = case redirectMap of
                                        Nothing -> (outputPositions V.! i )+index
                                        Just mp -> mp M.! ((outputPositions V.! i )+index)

                                  in L l $ ProjE (idx) ( L l $ VarE newVar) )
                                      (V.fromList ls)  ))  )

                              otherwise ->
                                  let idx = case redirectMap of
                                         Nothing -> (outputPositions V.! i )
                                         Just mp -> mp M.! (outputPositions V.! i )
                                  in L l  $ ProjE (idx) ( L l $ VarE newVar) -- not complete buggy (i +eps) `de
                        return( L l $ LetE (Var y, loc, t, rhs') body')

        AppE name loc e          -> do
             e'<- (go e newVar)
             return $ L l $ AppE name loc   e'
        PrimAppE x ls            -> do
            ls' <- (Prelude.mapM (\item -> (go item newVar)) ls)
            return $ L l $ PrimAppE x ls'

        LetE (v,loc,t,rhs) bod   -> do
            body' <- (go bod newVar)
            rhs' <- (go rhs newVar)
            return $L l $LetE (v,loc,t, rhs') body'
        IfE e1 e2 e3             -> do
          e1' <- (go e1 newVar)
          e2' <- (go e2 newVar)
          e3' <- (go e3 newVar)
          return$ L l $ IfE e1' e2' e3'

        MkProdE ls               -> do
          ls' <- (Prelude.mapM (\item -> (go item newVar)) ls)
          return $  L l $ MkProdE ls'
        ProjE index exp          -> do
          exp' <- (go exp newVar)
          return $ L l $ ProjE index exp'
        CaseE e1 ls1 ->  do
          e1' <- ( go e1  newVar)
          ls' <- (Prelude.mapM (\(dataCon,x,exp)->
            do
              exp' <- (go exp newVar)
              return (dataCon, x, exp')
              ) ls1)
          return  $ L l $ CaseE e1'  ls'


        DataConE loc datacons ls -> do
          ls' <- (Prelude.mapM (\x-> (go x newVar)) ls)
          return $ L l $ DataConE loc datacons ls'
        TimeIt e d b             -> do
          e'<- go e newVar
          return $L l $ TimeIt e'  d b
        otherwise                -> do
          return $ L l ex

removeUnusedDefs :: FunDef1 -> FunDef1
removeUnusedDefs f = f{funBody = removeUnusedDefs_exp (funBody f)}

removeUnusedDefs_exp :: L Exp1 ->  L Exp1
removeUnusedDefs_exp exp =
  let defTable = buildDefTable (unLoc exp)
  in go exp defTable
    where
      go (L l ex) dTable = case ex of
        LetE (Var s,loc,t,rhs) bod   -> case (M.lookup s dTable ) of
          Nothing -> L l $ LetE (Var s,loc,t, (go rhs dTable)) (go bod dTable)
          Just ( DefTableEntry _ _ 0) -> (go bod dTable)
          Just _  -> L l $ LetE (Var s,loc,t, (go rhs dTable)) (go bod dTable)
        IfE e1 e2 e3             ->  L l $
          IfE (go e1 dTable) ( go e2 dTable) ( go e3 dTable)
        CaseE e1 ls1             ->  L l $ CaseE e1 (L.map f ls1)
          where
            f (dataCon,x,exp) = (dataCon, x, (go exp dTable))
        AppE v loc e             ->  L l $ AppE v loc $ go e dTable
        TimeIt exp a b           ->  L l $ TimeIt (go exp dTable) a b
        otherwise -> L l ex


 -- the out of this is the tupled functions and a list of mapping between the
 -- the index of the output of each functions with its location in the tupled
 -- output
tupleListOfFunctions :: DDefs Ty1 -> [FunDef1] ->Var -> PassM(FunDef1) --, [Map Int Int])
tupleListOfFunctions  ddefs funcList newName = do
  ls <- Prelude.mapM freshBody  funcList

  let lsVector    = V.fromList ls
      retTypes    = V.map (\f -> (outTy (funTy f))) lsVector
  --    newRetType  = ProdTy (V.toList retTypes)
      newRetType  = ProdTy (V.foldl
        (\ls ty ->
          case ty of
            ProdTy ls2 -> ls L.++ ls2
            otherwise -> ls L.++ [ty]
         ) [] retTypes )

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

  let functionsBodies = V.toList (V.imap getBody lsVector)
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

  -- write a comment about each step in this functions
  -- it sort of complicated function
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

  let createOutVar index subscript=
          (toVar ("f" L.++(show index)L.++"out" L.++ (show subscript) ))

  -- this is changed now
  let tailExpr = MkProdE ( ( V.ifoldl
       (\ls index ty  ->
           case ty of
             ProdTy ls2 ->
              let newElements =V.toList(
                   V.imap (\subscript _ -> l $VarE  (createOutVar index subscript))
                      (V.fromList ls2))
              in (ls L.++ newElements)

             otherwise ->
                let newElement =  l $VarE  (createOutVar index 0 )
                in ls L.++ [newElement]

       ) [] retTypes ))

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
  replaceProj i1 argVar1 i2 argvar2 exp =
    let oldExp = l $ ProjE i1 (l (VarE argVar1))
        newExp = l $ ProjE i2 (l (VarE argvar2))
    in substE oldExp newExp exp

  freshBody func = do
      b' <- freshExp1 M.empty (funBody func)
      return (func{funBody =b'})
renameFunction :: FunDef1 -> Var -> FunDef1
renameFunction function newName =
   function{funName=newName, funBody = go (funBody function)}
    where
     go (L l ex) =
      let oldName = funName function in
        case ex of
          AppE name loc e          ->  L l $
            AppE (if name==oldName then newName else name) loc (go e)
          PrimAppE x ls            ->  L l $ PrimAppE x (L.map f ls)
            where f item = (go item)--`debug`  ("so2")
          LetE (v,loc,t,rhs) bod   ->  L l $ LetE (v,loc,t, (go rhs)) (go bod)
          MkProdE ls               ->  L l $ MkProdE (L.map (\x-> go x) ls)
          ProjE index exp          ->  L l $ ProjE index (go exp)
          CaseE e1 ls1             ->  L l $ CaseE (go e1)  (L.map f ls1)
            where f (dataCon,x,exp) = (dataCon, x, (go exp))
          DataConE loc datacons ls ->  L l $
            DataConE loc datacons(L.map (\x-> go x) pls)
          TimeIt e d b             ->  L l $ TimeIt ( go e) d b
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
  go  ex (M.fromList [])
 where
  go (L l ex) tb = case ex of
      AppE _ _ _               -> tb
      PrimAppE _ _             -> tb
      LetE (v,_,_,rhs) body    ->
        let t1 =go rhs t1
            t2= go body tb
        in case (unLoc rhs) of
            callExp@(AppE fName _ argList) ->
                case (unLoc argList) of
                    MkProdE ((L _ (VarE inputTree)):tail) ->
                        if((isTupleable (fDefs M.! fName)) &&
                            (haveIndependentArgs tail traversedTree))
                          then
                            let f Nothing   = Just [callExp]
                                f (Just ls) = Just (L.nub (callExp:ls))
                            in   (M.alter f inputTree (go body tb))

                          else t2
                    otherwise   -> t2
            otherwise -> t2

      IfE e1 e2 e3             -> let t1 = go e1 tb
                                      t2 = go e2 t1
                                  in go e3 t2
      MkProdE ls               -> tb
      ProjE index exp          -> tb
      CaseE e1 ls1             ->
          let t1 = go e1 tb in
          L.foldl f t1 ls1
         where
          f table (_ ,_ ,exp) = go exp table
      DataConE loc datacons ls ->
         L.foldl f tb ls where f table exp = go exp table
      TimeIt exp _ _           -> go exp tb
      otherwise                -> tb
   where
    isTupleable f = case (unLoc (funBody f)) of
      ---add a check that there is no nested case (maybe)
        CaseE e _ -> case (unLoc e) of
            ProjE 0 (L l (VarE v))-> if(v == (funArg f)) then True else False
            _ -> False --`debug` "\n5\n"
        _ -> False --`debug` "\n7\n"

    haveIndependentArgs args  traversedTree= L.foldl f True args
     where
      f b arg  = b &&
         (case (unLoc arg) of
             LitE _ -> True
             ProjE i (L l (VarE v)) -> case (traversedTree) of
                Nothing -> False
                Just inputVar ->  if(v==inputVar)  then True else False
             x -> False )


tuple :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> Maybe Var -> [(Var, Var, Int, Var)] ->
  (M.Map Var (M.Map Int Int)) ->  PassM (L Exp1,  FunDefs1)
tuple ddefs fdefs oldExpIn traversedTree fusedFunctions redirectMaps = do

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

  (oldExp, fdefs, redirectMaps) <- Control.Monad.foldM f (oldExpIn, fdefs, redirectMaps)  candidates2

  let oldExp' = removeUnusedDefs_exp (
                   simplifyProjectionsOfProducts(
                        removeCommonExpressions( removeCommonExpressions  oldExp )))
  return $(oldExp',fdefs) --`debug`("tuple candidates" L.++ (show candidates1))

 where
    f (exp, fdefs, redirectMaps) (tupledFName, callExpressions, firstCall) = do
      case (M.lookup tupledFName fdefs) of
          Just fdef -> do
            let redirectMap = M.lookup tupledFName redirectMaps --`debug` ((show tupledFName)L.++ (show redirectMaps))
            exp' <-foldTupledFunctions exp fdef callExpressions firstCall
                 (V.fromList (getOutputStartPositions fdefs callExpressions redirectMap ))redirectMap

            let exp'' =  simplifyProjectionsOfProducts(exp')
            return (exp'', fdefs, redirectMaps)

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

            (recTupledBody, newDefs) <- tuple ddefs fdefs'
              (removeCommonExpressions (funBody tupledFunction'))
                (Just (funArg tupledFunction')) fusedFunctions redirectMaps
                  --`debug`("\ntupling:" L.++ (show tupledFName))

            let tupledFunction'' =tupledFunction'{funBody=recTupledBody }
            let tupledFunction''' =tupledFunction''{
              funBody= removeUnusedDefs_exp (
                 simplifyProjectionsOfProducts(
                     removeCommonExpressions(
                     funBody tupledFunction'')))}
            let (tupledFunction4, redirectMap, removedPositions) =
                  removeRedundantOutput  tupledFunction'''

            let tupledFunction5 = tupledFunction4{
              funBody =
                removeUnusedDefs_exp (
                  simplifyProjectionsOfProducts(
                    removeCommonExpressions(
                      fixCalls (funBody tupledFunction4) tupledFunction4
                 redirectMap removedPositions))) }-- fix calls to the first in the body of the second for completeness need to be called on each function in newDefs

            let fdefs'' = M.insert tupledFName tupledFunction5  newDefs

            exp' <- foldTupledFunctions exp  tupledFunction5 callExpressions
                 firstCall
                 (V.fromList (getOutputStartPositions fdefs''
                  callExpressions (Just redirectMap))) (Just redirectMap)
            let exp'' =
                  simplifyProjectionsOfProducts(exp')
            return (exp'', fdefs'',  M.insert  tupledFName redirectMap redirectMaps)
     --       return (exp, fdefs'')

fixCalls :: L Exp1 -> FunDef1 -> M.Map Int Int -> [Int] -> L Exp1
fixCalls exp fdef redirectMap removedPositions = go exp
    where
      go exp = case (unLoc exp) of

        CaseE e ls ->
          let ls' = L.map (\(x, y, ex)-> (x, y, go ex)) ls
          in  l $ CaseE e ls'
        LetE (Var y, loc, t, rhs) body->
          case (unLoc rhs) of
            AppE v ls e ->
              if (v == (funName fdef ))
                then
                  -- here is the main work
                  -- change the type t
                  let t' = snd (funTy fdef) in
                  let body' = L.foldl
                        (\ex (i, j )->
                         if (i==j)
                             then ex
                           else
                              let oldExp = l $ProjE i ( l (VarE (Var y)) )
                                  newExp = l $ProjE j ( l (VarE (Var y)) )
                              in  substE oldExp newExp ex
                        ) body (M.toList redirectMap)
                  in l $ LetE (Var y, loc, t', rhs) (go body')
                else
                  l $  LetE (Var y, loc, t, rhs) (go body)
            otherwise ->
              l $  LetE (Var y, loc, t, rhs) (go body)
        otherwise-> l $ otherwise

getOutputStartPositions:: FunDefs1 -> [Exp1] -> Maybe (M.Map Int Int) -> [Int]
getOutputStartPositions fdefs callExpressions redirectMap =
     let functionsArgsLengths = L.map getCalledFunDef  callExpressions in
     let ls = L.foldl (\ls i -> ls L.++ [i+ (L.last ls)]  ) [0]
          functionsArgsLengths
     in  ls

   where
     getCalledFunDef callExpr = case (callExpr) of
          (AppE fName _ _) ->
            case (M.lookup fName fdefs) of
              Just fdef -> case (snd (funTy fdef)) of
                ProdTy ls -> L.length ls
                otherwise -> 1

-- the last argument is a set of already fused fuction in the form of 
-- [(outer, inner, 0, fusedFun)]

fuse :: DDefs Ty1 -> FunDefs1 -> Var -> Var -> [(Var, Var, Int, Var)]
     -> PassM (Bool, Var,  FunDefs1)

fuse ddefs fdefs  innerVar  outerVar fusedFunctions_ = do
    config <- getGibbonConfig
    newVar <- if (verbosity config >= 4)
            then pure (toVar ("_FUS_f_" ++ (fromVar outerVar) ++ "_f_" ++ 
                   (fromVar innerVar ) ++ "_FUS_"))
            else gensym "fuse_"
    innerFreshBody <- freshExp1 M.empty (funBody innerFunc)
    outerFreshBody <- freshExp1 M.empty (funBody outerFunc)
    setp1 <- inline innerFunc{funBody = innerFreshBody} 
                 outerFunc{funBody = outerFreshBody}  (-1)
    let step2 = (simplifyCases setp1 ){funName = newVar} --`debug`(show setp1)
        step3 = (foldFusedCalls_f (outerVar, innerVar, -1, newVar)  step2) --`debug` ((show newName )L.++"\n")
         -- fold upper already fused functions
        step4 = L.foldl (\f e -> foldFusedCalls_f e f ) step3 fusedFunctions_
        step5 = step4 {funBody = removeUnusedDefs_exp  (funBody step4)}
    
    return $(True, newVar, M.insert newVar step5 fdefs )

-- Check if a function conforms to restrictions we impose.
violateRestrictions :: FunDefs1 -> Var -> Var -> Bool
violateRestrictions fdefs inner outer =
  do
    let innerDef = case (M.lookup inner fdefs) of (Just v) -> v
        outerDef = case (M.lookup outer fdefs) of (Just v) -> v
        p1 = case head (fst (funTy innerDef)) of
               (PackedTy _ _ ) -> False
               x  -> True --`debug` ("ops "L.++ (show x))
        p2 = case head (fst (funTy outerDef) ) of
               (PackedTy _ _) -> False
               x  -> True --`debug` ("ops "L.++ (show x))
    (p1 || p2)

transform :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> Maybe Var->  [(Var, Var, Int, Var)] ->
  Bool -> [(Var, Var)] ->  PassM (L Exp1,  FunDefs1, [(Var, Var, Int, Var)])
transform  ddefs funDefs  exp traversedTree fusedFunctions_ doTupling processedCandidates = do
  go exp processedCandidates funDefs fusedFunctions_
 where
  go (L l body) processed fdefs  fusedFunctions = do
    let defTable = buildDefTable body
        potential = findPotential defTable processed --`debug`(show defTable)
    case (potential) of
      Nothing -> do
        -- final clean and tuple
        let final_clean = removeUnusedDefs_exp (L l body)
        -- let (tupledBody, tupleDefs) = (final_clean, M.empty)
        (tupledBody, tupleDefs) <- do
          if (doTupling)
            then tuple ddefs fdefs  final_clean traversedTree fusedFunctions M.empty
            else return (final_clean, M.empty)
        return $(tupledBody, M.union fdefs tupleDefs, fusedFunctions)

      Just ((inner,outer), outerDefVarSymbol) ->
        if (violateRestrictions fdefs inner outer)
          then go (L l body)  ((inner,outer):processed) fdefs fusedFunctions-- `debug` ("here" L.++ (show(inner,outer) ))
          else do
             -- fuse
            (validFused, fNew, fusedDefs) <-  (fuse  ddefs fdefs inner outer fusedFunctions_ )
            let fused_function = fusedDefs M.! fNew
            let newFusedEntry = (outer,inner, -1, fNew)

            (recAppBody, recAppDefs, retFusedFunctions) <- transform
              ddefs fusedDefs (funBody fused_function) (Just $ head (funArgs fused_function))
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
                   in go body' ((inner,outer):processed)
                        (M.union fdefs newDefs) newFusedFunctions
              else go (L l body)  ((inner,outer):processed) fdefs fusedFunctions

fusion2 :: Prog1 -> PassM Prog1
fusion2 (L1.Prog defs funs main) = do
    (main', funs') <- case main of
        Nothing   -> return $ (Nothing, funs)
        Just (m, ty)    -> do
            (m', newDefs, _) <- (transform defs funs m Nothing [] True [])
            return (Just (m',ty), M.union funs newDefs)
    return $ L1.Prog defs funs' main'
