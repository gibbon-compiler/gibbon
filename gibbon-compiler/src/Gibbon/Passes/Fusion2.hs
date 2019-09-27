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
import           Control.Monad
import Gibbon.Pretty
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
  , varType       :: Ty1
  } deriving (Show , Generic)

type FunctionUses =
  ( Exp1 -- The AppE that uses a variable.
  , Int  -- i where variable V is the i'th argument in this function call.
  , Maybe Symbol -- The variable that binds this AppE.
  )


type PotentialPair = (Symbol, Symbol)
type PotentialsList = [DefTableEntry]

freshFunction :: FunDef1 -> PassM FunDef1
freshFunction f = do
  body' <- freshExp1 M.empty  (funBody f)
  let  f' = f{funBody = body' }
  let argsOld = funArgs f'
  argsNew <- Prelude.mapM gensym argsOld
  let f'' = f'{funArgs = argsNew}
  return $ substArgs f''  argsOld argsNew
 where
  substArgs f [] [] = f
  substArgs f (old:told) (new:tnew) =
    let f' = f{funBody = substE (l (VarE old)) (l (VarE new)) (funBody f)}
    in substArgs f' told tnew

removeCommonExpressions ::  L Exp1->  L Exp1
removeCommonExpressions = go
   where
    go exp  = case unLoc exp of
      LetE (v, ls, t, bind) body ->
        case unLoc bind of
            ProjE i e ->
              let oldExp = l $ VarE v
                  newExp = l $ ProjE i e
                  body' = substE oldExp newExp body
              in go body'-- `debug` ("replace ::"L.++ (show oldExp) L.++ "with" L.++ (show newExp))
            VarE v' ->
              let oldExp = l $ VarE v
                  newExp = l $ VarE v'
                  body' = substE oldExp newExp body
              in go body'
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

simplifyProjections :: L Exp1->  L Exp1
simplifyProjections exp = removeCommonExpressions (go exp M.empty)
 --   `debug` ("before the death" L.++ render (pprint go exp M.emptyZZZZzzzz) )
   where
    go exp mp = case unLoc exp of
      LetE (v, ls, t, bind) body ->
        case unLoc bind of
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
        let ls' = L.map (`go` mp) ls
        in l $ PrimAppE p ls'

      TimeIt exp x y  ->l $   TimeIt (go exp mp) x y

      L1.ProjE i e ->
        case unLoc e of
          VarE v ->
            case M.lookup v mp of
               Nothing ->  l $ L1.ProjE i e
               Just ls -> ls V.! i
          otherwise -> l $ L1.ProjE i (go e mp)
      DataConE x y ls->
        let ls' = L.map (`go` mp) ls
        in l$ DataConE x y ls'
      AppE v loc args  ->
        l $   AppE v loc (map (`go` mp) args)
      MkProdE ls->
        let ls' = L.map (`go` mp) ls
        in  l$   MkProdE ls'

      x       -> l $x

replaceLeafWithBind :: L Exp1 -> (Int -> Var) -> Ty1 -> L Exp1 -> L Exp1
replaceLeafWithBind exp genVar varType tailExp =
  go exp
   where
     go ex =
      case unLoc ex of
          L1.LetE (v,ls,t, e1) e2 -> l $ L1.LetE (v,ls,t, e1)  (go e2)
          x -> case varType of
              ProdTy ls2 ->
                  let xDestructed = V.fromList (case  x of MkProdE ls -> ls)
                      newExp = V.ifoldl
                              (\tExp subscript ty ->
                                let newVar = genVar subscript
                                in l $L1.LetE (newVar,[],ty, xDestructed V.! subscript) tExp
                              ) tailExp (V.fromList ls2)
                  in newExp
              otherwise ->
                let newVar = genVar 0
                in  l $L1.LetE (newVar,[],varType, l x) tailExp

addOuterTailCall:: L Exp1 -> Var -> Var -> Ty1 ->  [L Exp1] -> L Exp1
addOuterTailCall exp fName parName varType outerArgs =
  removeCommonExpressions (go exp)
   where
     go ex =
      case unLoc ex of
          L1.LetE (v,ls,t, e1) e2 -> l $ L1.LetE (v,ls,t, e1)  (go e2)
          x ->
            let newCall = l $AppE fName [] ( (l (VarE parName)) :outerArgs)
                newLet = l $ LetE (parName, [], varType, l x) newCall
            in newLet
{- This function≈ collect the following information for each defined variable:
  1) The defining expression. (stored in DefTableEntry::def)
  2) The consumer of the definition that are candidates for fusion;the function
  is consumed in the first argument. (stored in DefTableEntry::fun_uses)
  not: uses mutual exclusive paths are counted by adding them (each is
  considered  a use).
  3) Total number of uses (references) of the defined variable.
-}
buildDefTable :: Exp1 -> DefTable
buildDefTable ex = go ex Nothing M.empty
  where
    go ex definingSymbol table =
      case ex of
        VarE (Var sym) -> M.update incrUses sym table
        LetE (Var symLet, _, t, bind) body ->
          let table' =
                M.insert
                  symLet
                  (DefTableEntry
                     { def = unLoc bind
                     , fun_uses = []
                     , all_use_count = 0
                     , varType = t
                     })
                  table
              table'' = go (unLoc bind) (Just symLet) table'
           in go (unLoc body) definingSymbol table''

    -- The thing that is traversed is always the first argument.
    -- Here, we record a function use for the first argument
    -- in the DefTable.
    -- add function uses of interest
    -- [functions calls traversing tree in first argument]
        AppE fName _ args ->
          let addFunctionUse newUse (DefTableEntry def fun_uses c t) =
                Just $ DefTableEntry def (newUse : fun_uses) c t
              table' =
                if ((length args) > 0)
                  then case unLoc (head args) of
                         VarE (Var sym) ->
                           M.update
                             (addFunctionUse (ex, 0, definingSymbol))
                             sym
                             table
                              -- If it's anything else, it's not a candidate for fusion, and
                             -- we can ignore it.
                         _ -> table
                  else table
           in foldl (\acc a -> go (unLoc a) Nothing acc) table' args
        MkProdE argsList -> buildDefTable_args argsList table
          where buildDefTable_args [] tb = tb
                buildDefTable_args (h:tail) table =
                  buildDefTable_args tail (go (unLoc h) Nothing table)
        PrimAppE _ ls -> L.foldl f table ls
          where f tbl exp = go (unLoc exp) Nothing tbl
        IfE cond thenBody elseBody ->
          let table' = go (unLoc cond) Nothing table
           in let table'' = go (unLoc thenBody) definingSymbol table'
               in go (unLoc elseBody) definingSymbol table''
        CaseE e ls ->
          let table' = go (unLoc e) Nothing table
           in L.foldl f table' ls
          where f tbl (_, _, exp) = go (unLoc exp) definingSymbol tbl
        DataConE _ _ ls -> L.foldl f table ls
          where f tbl exp = go (unLoc exp) Nothing tbl
        TimeIt exp _ _ -> go (unLoc exp) definingSymbol table
        ProjE index exp -> go (unLoc exp) Nothing table
        LitE _ -> table
        x ->
          table `debug`
          ("please handle:" L.++ show x L.++ "in buildDefTable\n")
      where
        incrUses (DefTableEntry def fun_uses c t) =
          Just $ DefTableEntry def fun_uses (c + 1) t


extractAppNameFromLet ::  Exp1 -> Var
extractAppNameFromLet (LetE (Var symLet,_,_,L _ (AppE var _ _ )) _)  = var

extractLetSymbolFromLet ::  Exp1 -> Symbol
extractLetSymbolFromLet (LetE (Var symLet,_,_,L _ (AppE var _ _ )) _)  = symLet

extractAppEName ::  Exp1 -> Var
extractAppEName (AppE var _ _ ) = var
extractAppEName  x = error(show x)

-- Takes the table, and candidates which are already processed and
-- return one that isn't.
--
-- returns ((innerFun, outerFun), symbol defined by the outer)
findPotential :: DefTable -> [(Var, Var)] -> Maybe ((Var, Var), Maybe Symbol)
findPotential table skipList =
  case L.find predicate (M.toList table) of
    Nothing -> Nothing
    Just (_, DefTableEntry def fun_uses use_count t) ->
      Just
        ( (extractAppEName def, extractAppEName (sel1 (L.head fun_uses)))
        , sel3 (L.head fun_uses))
  where
    predicate (_, DefTableEntry def fun_uses use_count t) =
      case def of
        AppE var _ _ ->
          not (null fun_uses) &&
          L.notElem
            (extractAppEName def, extractAppEName (sel1 (L.head fun_uses)))
            skipList
        _ -> False

isPotential :: DefTable -> Maybe Symbol -> [(Var, Var)] -> Bool
isPotential table symbol skipList =
  case symbol of
    Nothing -> False
    Just symb ->
      case table  M.!? symb of
         Nothing       -> False --`debug`  (show skipList)
         Just (DefTableEntry def fun_uses use_count t)  ->
             (L.length fun_uses == 1) && L.notElem  (extractAppEName def,
                extractAppEName(sel1 (L.head fun_uses)) ) skipList

simplifyCases2 :: L Exp1 ->  L Exp1
simplifyCases2 = go
  where
    go ex =
      case unLoc ex of
        CaseE e1@(L _ (CaseE e2 ls2)) ls1 -> go (l (CaseE e2 (L.map f ls2))) --`debug` (show "original input was \n" L.++ (show (l (CaseE e2 (L.map f ls2)))))
          where f oldItem = upd3 (l (CaseE (sel3 oldItem) ls1)) oldItem
        CaseE e1@(L l (DataConE loc k constructorVars)) caseList ->
          let newBody = L.find (\item -> sel1 item == k) caseList
           in case newBody of
                Nothing -> error "unmatched constructor!"
                Just (k, caseVars, caseExp) ->
                  go $case_subst constructorVars caseVars caseExp
                  where case_subst (x1:l1) (x2:l2) exp =
                          subst (fst x2) x1 (case_subst l1 l2 exp)
                        case_subst [] [] exp = exp
        CaseE (L _ (IfE e1 e2 e3)) ls ->
          go $ l $ IfE e1 (l (CaseE e2 ls)) (l (CaseE e3 ls))
        CaseE e1@(L _ (LetE bind body)) ls1 ->
          let body' = go (l (CaseE body ls1))
           in l $ LetE bind body'
        CaseE e1 ls1 -> l $ CaseE e1 (L.map f ls1)
          where f item = upd3 (go (sel3 item)) item
        LetE (v, loc, t, rhs) bod -> l $ LetE (v, loc, t, go rhs) (go bod)
        AppE v loc expList -> l $ AppE v loc (L.map go expList)
        IfE e1 e2 e3 -> l $ IfE (go e1) (go e2) (go e3)
        TimeIt e d b -> l $ TimeIt (go e) d b
        ex -> l ex

inline2 :: FunDef1 -> FunDef1  -> PassM FunDef1
inline2 inlined_fun outer_fun  =
 do
  newTraversedTreeArg <- gensym (toVar "inputTree")
  let argTypes_outer = fst (funTy outer_fun)
      retType_outer = snd (funTy outer_fun)
      argVar_outer = head $ funArgs outer_fun
      argTypes_inlined = fst (funTy inlined_fun)
      argVar_inlined = head $ funArgs inlined_fun
      retTypeInlined = snd (funTy inlined_fun)
      traversedType = head argTypes_inlined
      -- All arguments except the one that's traversed.

      -- is it ok that those are swapped lol!
      sideArgsTypesInlined = tail argTypes_inlined
      sidArgsTypesOuter = tail argTypes_outer
      newType =
        ( [traversedType] ++ sideArgsTypesInlined ++ sidArgsTypesOuter
        , retType_outer)
      inlinedFunBody =
        let oldExp = l $ VarE argVar_inlined
            newExp = l $ VarE newTraversedTreeArg
         in substE oldExp newExp (funBody inlined_fun)

  -- the traversed tree in the outer is replaced with either a call to the inner
  -- or the body of the inner
  let oldExp = l $ VarE argVar_outer
  let replaceWithCall exp = do
        newVar <- gensym (toVar "innerCall")
        let rhs =
              l
                (AppE
                   (funName inlined_fun)
                   []
                   (L.map (l . VarE) ( newTraversedTreeArg:tail (funArgs inlined_fun))))
            body = substE oldExp (l (VarE newVar)) exp
        return $ l $ LetE (newVar, [], retTypeInlined, rhs) body

  let outerCaseList =
        case unLoc (funBody outer_fun) of
           CaseE e1 ls -> ls

  newBody <-
    case unLoc (inlinedFunBody) of
      CaseE e1 ls -> do
        ls' <-
          Prelude.mapM
            (\(dataCon, vars, exp) -> do
              if hasConstructorTail exp
                then
                 do
                  let exp' = l (CaseE (exp) outerCaseList)
                  exp'' <- replaceWithCall exp'
                  return (dataCon, vars,  exp'')
                else
                 do
                  newSymbol <-  gensym (toVar "outerCall")
                  let exp' =
                       addOuterTailCall exp (funName outer_fun) (newSymbol)
                          (snd(funTy inlined_fun)) (L.map (\v -> l(VarE v)) (tail (funArgs outer_fun)))

                  return (dataCon, vars, exp')
            )
            ls
        return $ l (CaseE (l (VarE newTraversedTreeArg)) ls')
 --     exp -> replaceWithCall (substE oldExp inlinedFunBody (l exp))

  let newArgs =
        [newTraversedTreeArg] L.++ L.tail (funArgs inlined_fun) L.++
        L.tail (funArgs outer_fun)
  return outer_fun {funArgs = newArgs, funTy = newType, funBody = newBody}

{-
  The type of the new function is defined as the following :
   if
     innerType = TreeX-> Args1... -> RetType1
     outerType = RetType Args2... -> RetType2
  then
     inlinedType = TreeX -> Args1... ->  Args2... -> RetType2

-}
inline :: FunDef1 -> FunDef1 -> Int -> PassM FunDef1
inline inlined_fun outer_fun arg_pos = do
  newTraversedTreeArg <- gensym (toVar "inputTree")
  let argTypes_outer = fst (funTy outer_fun)
      retType_outer = snd (funTy outer_fun)
      argVar_outer = head $ funArgs outer_fun
      argTypes_inlined = fst (funTy inlined_fun)
      argVar_inlined = head $ funArgs inlined_fun
      retTypeInlined = snd (funTy inlined_fun)
      traversedType = head argTypes_inlined
      -- All arguments except the one that's traversed.
      sideArgsTypesInlined = tail argTypes_outer
      sidArgsTypesOuter = tail argTypes_inlined
      newType =
        ( [traversedType] ++ sideArgsTypesInlined ++ sidArgsTypesOuter
        , retType_outer)
      inlinedFunBody =
        let oldExp = l $ VarE argVar_inlined
            newExp = l $ VarE newTraversedTreeArg
         in substE oldExp newExp (funBody inlined_fun)

  -- the traversed tree in the outer is replaced with either a call to the inner
  -- or the body of the inner
  let oldExp = l $ VarE argVar_outer
  let replaceWithCall exp = do
        newVar <- gensym (toVar "innerCall")
        let rhs =
              l
                (AppE
                   (funName inlined_fun)
                   []
                   (L.map (l . VarE) (funArgs inlined_fun)))
            body = substE oldExp (l (VarE newVar)) exp
        return $ l $ LetE (newVar, [], retTypeInlined, rhs) body
  newBody <-
    case unLoc (funBody outer_fun) of
      CaseE e1 ls -> do
        ls' <-
          Prelude.mapM
            (\(dataCon, vars, exp) -> do
               newInnerExp <- replaceWithCall (substE oldExp inlinedFunBody exp)
               return (dataCon, vars, newInnerExp))
            ls
        return $ l (CaseE (substE oldExp inlinedFunBody e1) ls')
      exp -> replaceWithCall (substE oldExp inlinedFunBody (l exp))
  let newArgs =
        [newTraversedTreeArg] L.++ L.tail (funArgs inlined_fun) L.++
        L.tail (funArgs outer_fun)
  return outer_fun {funArgs = newArgs, funTy = newType, funBody = newBody}


-- This function simplify the case expression when the matched expression
-- is it self another case expression.
-- In the same way Wadler do it [nested case rule]
-- We only need to simplify the top level case
simplifyCases :: FunDef1 -> FunDef1
simplifyCases function = function {funBody = go (funBody function)}
  where
    go ex =
      case unLoc ex of
        CaseE e1@(L _ (CaseE e2 ls2)) ls1 -> go (l (CaseE e2 (L.map f ls2))) --`debug` (show "original input was \n" L.++ (show (l (CaseE e2 (L.map f ls2)))))
          where f oldItem = upd3 (l (CaseE (sel3 oldItem) ls1)) oldItem
        CaseE e1@(L l (DataConE loc k constructorVars)) caseList ->
          let newBody = L.find (\item -> sel1 item == k) caseList
           in case newBody of
                Nothing -> error "unmatched constructor!"
                Just (k, caseVars, caseExp) ->
                  go $case_subst constructorVars caseVars caseExp
                  where case_subst (x1:l1) (x2:l2) exp =
                          subst (fst x2) x1 (case_subst l1 l2 exp)
                        case_subst [] [] exp = exp
        CaseE (L _ (IfE e1 e2 e3)) ls ->
          go $ l $ IfE e1 (l (CaseE e2 ls)) (l (CaseE e3 ls))
        CaseE e1@(L _ (LetE bind body)) ls1 ->
          let body' = go (l (CaseE body ls1))
           in l $ LetE bind body'
        CaseE e1 ls1 -> l $ CaseE e1 (L.map f ls1)
          where f item = upd3 (go (sel3 item)) item
        LetE (v, loc, t, rhs) bod -> l $ LetE (v, loc, t, go rhs) (go bod)
        AppE v loc expList -> l $ AppE v loc (L.map go expList)
        IfE e1 e2 e3 -> l $ IfE (go e1) (go e2) (go e3)
        TimeIt e d b -> l $ TimeIt (go e) d b
        ex -> l ex


foldFusedCallsF :: (Var, Var, Int, Var) -> FunDef1 -> FunDef1
foldFusedCallsF rule function =
  function {funBody = foldFusedCalls rule (funBody function)}

foldFusedCalls :: (Var, Var, Int, Var) -> L Exp1 -> L Exp1
foldFusedCalls rule@(outerName, innerName, argPos, newName) body =
  let defTable = buildDefTable (unLoc body)
      go ex =
        case unLoc ex of
          AppE fName loc argList ->
            let notFolded = l $ AppE fName loc argList
             in if fName == outerName
                  then case unLoc (head argList) of
                         VarE (Var symInner) ->
                           if innerName == getDefiningFunction symInner defTable
                             then let innerArgs = getArgs symInner defTable
                                      outerArgs = argList
                                      newCallArgs =
                                        (innerArgs L.++ tail argList)
                                   in l $ AppE newName loc newCallArgs
                             else notFolded
                         _ -> notFolded
                  else notFolded
          LetE (v, loc, t, lhs) bod -> l $ LetE (v, loc, t, go lhs) (go bod)
          IfE e1 e2 e3 -> l $ IfE (go e1) (go e2) (go e3)
          CaseE e1 ls1 -> l $ CaseE e1 (L.map f ls1)
            where f (dataCon, x, exp) = (dataCon, x, go exp)
          TimeIt e d b -> l $ TimeIt (go e) d b
          DataConE loc dataCons ls -> l $ DataConE loc dataCons (L.map go ls)
          _ -> ex
   in removeUnusedDefsExp (go body)
  where
    getDefiningFunction x defTable =
      case M.lookup x defTable of
        Nothing -> toVar "dummy"
        Just entry ->
          case def entry of
            AppE v _ _ -> v
            _ -> toVar "dummy"
    getArgs x defTable =
      case M.lookup x defTable of
        Nothing -> error "error in foldFusedCalls"
        Just entry ->
          case def entry of
            AppE _ _ args -> args
            _ -> error ("ops" L.++ show (def entry))

-- outputPositions specify for each call i at what index is the corresponding
-- output in the returned tuple

foldTupledFunctions ::   L Exp1 -> FunDef1 -> [Exp1] ->
 V.Vector Int->   M.Map (Int, Int) (Int, Int)  -> PassM (L Exp1)
foldTupledFunctions bodyM newFun oldCalls  outputPositions syncedArgs  =
  do
     newVar <- gensym (toVar "tupled_output")
     go bodyM newVar True
  where
    go ex newVar first =
      case unLoc ex of
        LetE (Var y, loc, t, rhs) body ->
            case L.elemIndex (unLoc rhs) oldCalls of
              Nothing ->
                do
                  rhs' <- go rhs newVar first
                  l . LetE (Var y, loc, t, rhs') <$> go body newVar first
              Just i ->
                  if first -- not valid af
                    then
                      do
                        body' <- go body newVar False
                        let args = V.ifoldl f []  (V.fromList oldCalls)
                             where
                              f ls1 fIdx exp = ls1 L.++ (extractArgs fIdx) exp

                              extractArgs fIdx (AppE _ _  (h:tail)) =
                                 V.toList (V.ifilter -- argIdx+1 because head is dropped (idx 0)
                                  (\argIdx arg -> not ( M.member (fIdx, argIdx+1) syncedArgs))
                                     (V.fromList tail))

                        let args' = getFirstArg rhs:args
                             where
                              getFirstArg (L _ (AppE _ _ (h:_)))= h --`debug` ("oldCalls" L.++ (show oldCalls) L.++
                                 --(render( pprint bodyM)))

                        let rhs' =  l $AppE (funName newFun) [] args'
                               `debug` ("new call" L.++ (show (AppE (funName newFun) [] args')))
                        let bindType = outTy (funTy newFun)
                        let rhs'' =  case t of
                              ProdTy ls ->  l ( MkProdE (
                                V.toList ( V.imap (\index _ ->
                                  let idx =(outputPositions V.! i) +index
                                  in  l $ ProjE idx (l $ VarE newVar) )
                                      (V.fromList ls)  ))  )
                              otherwise ->
                                  let idx = outputPositions V.! i

                                  in  l  $ ProjE idx (l $ VarE newVar)-- not complete buggy (i +eps)
                        let body'' =    l $ LetE (Var y, loc, t, rhs'') body'
                            body3  =  l $LetE (newVar, [], bindType, rhs') body''
                            body4 =   collectArgsConstruction args body3
                        return body4

                    else
                      do
                        body' <- go body newVar first--`debug` ("\nhere\n")
                        let rhs' =  case t of
                              ProdTy ls ->  l ( MkProdE (
                                V.toList ( V.imap (\index _ ->
                                  let idx =  (outputPositions V.! i )+index

                                  in  l $ ProjE idx (l $ VarE newVar) )
                                      (V.fromList ls)  )))

                              _ ->
                                  let idx =  outputPositions V.! i

                                  in  l $ ProjE idx (l $ VarE newVar) -- not complete buggy (i +eps)
                        return(l $ LetE (Var y, loc, t, rhs') body')

        AppE name loc argList         ->
           do
             argList' <- Prelude.mapM  (\x -> go x newVar first) argList
             return $  l $ AppE name loc argList'
        PrimAppE x ls            ->
            l . PrimAppE x <$> Prelude.mapM (\x -> go x newVar first) ls

        LetE (v,loc,t,rhs) bod   -> do
            body' <- go bod newVar first
            rhs' <- go rhs newVar first
            return $ l $LetE (v,loc,t, rhs') body'
        IfE e1 e2 e3             -> do
          e1' <- go e1 newVar first
          e2' <- go e2 newVar first
          l . IfE e1' e2' <$> go e3 newVar first

        MkProdE ls               ->
          l . MkProdE <$> Prelude.mapM (\x -> go x newVar first)   ls
        ProjE index exp          ->
          l . ProjE index <$> go exp newVar first
        CaseE e1 ls1 ->  do
        --  e1' <- go e1  newVar first
          l . CaseE e1 <$> Prelude.mapM (\(dataCon,x,exp)->
            do
              exp' <- go exp newVar True
              return (dataCon, x, exp')
              ) ls1

        DataConE loc datacons ls ->
          l . DataConE loc datacons <$> Prelude.mapM (\x -> go x newVar first) ls
        TimeIt e d b             -> do
          e'<- go e newVar first
          return $ l $ TimeIt e'  d b
        _                ->
          return ex

    defTable = buildDefTable (unLoc bodyM)
    collectRec leafExp exp  =
      case unLoc exp of
        VarE v@(Var symbol) ->
              case M.lookup symbol defTable of
                Nothing ->  leafExp
                Just (DefTableEntry definingExp _ _ t)->
                  collectRec ( l $ LetE (v ,[], t, l definingExp) leafExp) (l definingExp)
        AppE fName _ args -> L.foldl collectRec leafExp args
        MkProdE expList ->  L.foldl collectRec leafExp expList
        PrimAppE _ args -> L.foldl collectRec leafExp args
        IfE cond thenBody elseBody      ->
           L.foldl collectRec leafExp  [cond,  thenBody, elseBody ]
        DataConE _ _ expList -> L.foldl collectRec leafExp expList
        ProjE index exp -> collectRec leafExp exp
        LitE _ -> leafExp
        x       -> error ( "please handle me explicitly" L.++ (show x))

    collectArgsConstruction  args  exp =  L.foldl collectRec exp args
removeUnusedDefs :: FunDef1 -> FunDef1
removeUnusedDefs f = f{funBody = removeUnusedDefsExp (funBody f)}

removeUnusedDefsExp :: L Exp1 ->  L Exp1
removeUnusedDefsExp exp =
  let defTable = buildDefTable (unLoc exp)
  in go exp defTable
    where
      go  ex dTable = case unLoc ex of
        LetE (Var s,loc,t,rhs) bod   ->
         case M.lookup s dTable of
            Nothing ->  l $ LetE (Var s,loc,t, go rhs dTable) (go bod dTable)
            Just ( DefTableEntry _ _ 0 t) -> go bod dTable
            Just _  ->  l $ LetE (Var s,loc,t, go rhs dTable) (go bod dTable)
        IfE e1 e2 e3             ->  l $
          IfE (go e1 dTable) ( go e2 dTable) ( go e3 dTable)
        CaseE e1 ls1             ->   l $ CaseE e1 (L.map f ls1)
          where
            f (dataCon,x,exp) = (dataCon, x, go exp dTable)
        AppE v loc argList       ->
          l  $ AppE v loc (L.map (`go` dTable) argList )
        TimeIt exp a b           ->   l $ TimeIt (go exp dTable) a b
        _ ->  ex

tupleListOfFunctions :: DDefs Ty1 -> [FunDef1] -> Var ->
   M.Map (Int, Int) (Int, Int) -> PassM FunDef1
tupleListOfFunctions  ddefs funcList newName syncedArgs = do
  funcBodies <- Prelude.mapM freshFunction funcList
  let funcBodiesV = V.fromList funcBodies
      retTypes    = V.map (snd . funTy) funcBodiesV
      newRetType  = ProdTy (V.foldl
        (\ls ty ->
          case ty of
            ProdTy ls2 -> ls L.++ ls2
            otherwise -> ls L.++ [ty]
         ) [] retTypes )

      -- we can change this now
      newFuncInputType = V.ifoldl f [] funcBodiesV
        where
          f ls fIdx fdef =
            case fst (funTy fdef) of
              (h:tail)->
                let concreteArgs = V.ifoldl f [] (V.fromList tail)
                     where
                      f res argIdx arg =
                        -- add one to argIdx becasue head is deleted
                        if M.member (fIdx, argIdx+1 ) syncedArgs
                          then res
                          else res L.++ [arg]

                in if fIdx == 0
                    then
                      ls L.++ [h] L.++ concreteArgs
                    else
                      ls L.++ concreteArgs

  let traversedType = L.head newFuncInputType

  traversedTreeArg <- gensym (toVar "input")
  let newArgs = traversedTreeArg:
        V.ifoldl
         (\ls fIdx f ->
            ls L.++
                (V.toList
                   (V.ifilter
                     (\argIdx _-> not (M.member (fIdx, argIdx+1) syncedArgs))
                     (V.fromList (L.tail (funArgs f))))
                )
          ) [] funcBodiesV

  let argsLocsToVarMap =
        V.ifoldl
         (\mp fIdx func ->
            V.ifoldl
              (\mpinner argIdx argVar-> M.insert (fIdx, argIdx) argVar mpinner)
               mp (V.fromList (funArgs func))
          ) M.empty funcBodiesV

  -- replace the traversed tree variable with the new common one
  let functionsBodies' = V.toList (V.imap getBody funcBodiesV)
       where
          getBody i func =
            let oldExp = l $ VarE (L.head (funArgs func ))
                newExp = l (VarE traversedTreeArg)
            in substE  oldExp newExp (funBody func)

  -- output of this is a map from dataCons -> [exp'] which are the portions
  -- from each functions that map to the constructor
  let step2 = L.foldl mapAndSplit M.empty functionsBodies'
        where
          mapAndSplit mp (L _(CaseE e lsCase))  = L.foldl f mp lsCase
            where f mp (dataCons, vars, exp)  =
                    let exp' = subsVars exp
                    in case M.lookup dataCons mp of
                         Nothing -> M.insert dataCons [exp'] mp
                         Just x -> M.insert dataCons (x L.++ [exp']) mp
                    where
                       subsVars ex = V.ifoldr subsVar ex (V.fromList vars)
                       subsVar index v ex   =
                          let oldExp = l $ VarE (fst v)
                              newExp = l (VarE (toVar (L.map toLower
                                 (dataCons L.++ show index))))
                          in substE  oldExp newExp ex


  let traversedTreeDDef =
        lookupDDef ddefs (case traversedType of (PackedTy tName _) -> tName)

  -- this is the returned tuple (out1_1, out1_2, out2_1 ..etc) those variables
  -- stores the result
  let tailExpr = MkProdE ( V.ifoldl
       (\ls index ty  ->
           case ty of
             ProdTy ls2 ->
              let newElements =V.toList(
                   V.imap (\subscript _ -> l $VarE  (createOutVar index subscript))
                      (V.fromList ls2))
              in (ls L.++ newElements)

             _ ->
                let newElement =  l $VarE  (createOutVar index 0 )
                in ls L.++ [newElement]

       ) [] retTypes)

  let topLevelExpr = CaseE (l (VarE traversedTreeArg)) []

  let extendedCase = L.foldr addConstructorBody topLevelExpr
        (dataCons traversedTreeDDef)
        where
          addConstructorBody (dataCons, varls) (CaseE e1 caseList) =

            -- a list of the names of the constructor variables
            --  e.g [leaf0, leaf1]  or [inner0, inner1, inner2, inner3]
            let newVarsList = V.toList( V.imap (\index _ -> ( toVar (L.map
                  toLower (dataCons L.++ show index)) ,() ) )(V.fromList varls))

                bodiesOfConst =V.fromList (L.reverse (step2 M.! dataCons))
                combinedBodies  =  V.ifoldl f (l tailExpr) bodiesOfConst
                 where
                  f tailExp index exp  =

                    let pos = V.length funcBodiesV - index  -1
                        newVar   = createOutVar pos
                        newVarType = snd (funTy  (funcBodiesV V.!pos))
                    in replaceLeafWithBind exp newVar newVarType tailExp
            in CaseE e1 ((dataCons, newVarsList, combinedBodies):caseList)
  -- replace uses of eliminated synced Input args
  let finalBody =
       M.foldlWithKey
        (\exp k v->
           let oldExp = l $ VarE (argsLocsToVarMap M.! k)
               newExp = l $ VarE (argsLocsToVarMap M.! v)
           in substE  oldExp newExp exp
        ) (l extendedCase) syncedArgs

  return (FunDef newName newArgs (newFuncInputType,newRetType) finalBody)
 where
  createOutVar index subscript=
          toVar ("f" L.++ show index L.++"out" L.++ show subscript)


renameFunction :: FunDef1 -> Var -> FunDef1
renameFunction function newName =
   function{funName=newName, funBody = go (funBody function)}
    where
     go ex =
      let oldName = funName function in
      case unLoc ex of
          AppE name loc argList          ->   l $
            AppE (if name==oldName then newName else name) loc argList
          PrimAppE x ls            ->   l $ PrimAppE x (L.map f ls)
            where f item = go item
          LetE (v,loc,t,rhs) bod   ->   l $ LetE (v,loc,t, go rhs) (go bod)
          MkProdE ls               ->   l $ MkProdE (L.map go ls)
          ProjE index exp          ->   l $ ProjE index (go exp)
          CaseE e1 ls1             ->   l $ CaseE (go e1)  (L.map f ls1)
            where f (dataCon,x,exp) = (dataCon, x, go exp)
          DataConE loc dataCons ls ->   l $
            DataConE loc dataCons (L.map go ls)
          TimeIt e d b             ->   l $ TimeIt (go e) d b
          _                ->   ex



{- We want to search for
the following:
  f1 (x1, v1,v2 ...vn)
  f2 (x1, k1,k2 ...kn)
 such that
body (f1) = case (x1) of {}
body (f2) = case (x1) of {}
and k1..kn do not dependent on the results of f1

the return  format is the following [(x1, [f1, f2])]
-}

-- should be a preorder and not a post order OMG!!!
buildTupleCandidatesTable::   FunDefs1 -> L Exp1 -> [Var] -> M.Map Var [Exp1]
buildTupleCandidatesTable fDefs exp argsVars =
   M.map (\ls -> L.map snd ls) (go exp M.empty)
 where
  go ex tb = case unLoc ex of
      AppE{}                   -> tb
      PrimAppE _ _             -> tb
      LetE (boundedVar,_,_,rhs) body    ->
        let tb'=
             case unLoc rhs of
                callExp@(AppE fName _ argList@(L _ (VarE inputTree):tail)) ->
                  let otherCalls = if M.member inputTree  tb
                                    then (tb  M.! inputTree)
                                    else [] in
                  if (isTupleable (fDefs M.! fName)) &&
                        (haveIndependentArgsNew tail otherCalls)
                    then
                      let addCall Nothing   = Just [(boundedVar, callExp)]
                          addCall (Just ls) = Just $ L.nub  $(boundedVar, callExp):ls
                      in M.alter addCall inputTree  tb
                    else  tb
                _ -> tb
        in  go body tb'

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
      _                -> tb
   where
    defTable = buildDefTable (unLoc exp)

    isTupleable f = case unLoc (funBody f) of
      ---add a check that there is no nested case (maybe)
        CaseE e _ -> case unLoc e of
            VarE v -> v == L.head (funArgs f)
            _ -> False
        _ -> False

    isTrivial f =
      if not (isTupleable f )
        then True
        else
          case unLoc (funBody f) of
            CaseE e ls ->
              L.foldl (\res (_ ,_ ,exp) -> res && (go exp )) True ls
               where
                go exp =
                  case unLoc exp of
                    LetE (boundedVar,_,_,rhs) body  ->
                      case unLoc rhs of
                           AppE{} -> False
                           otherwise -> go body
                    AppE{} -> False
                    otherwise -> True




    -- we want to make sure that args are independent on "other calls"
    haveIndependentArgsNew args otherCalls =
      let varsToAvoid = S.fromList (L.map fst otherCalls)
          dependentVars = S.unions (L.map collectDependentVarsExp  args)
      in S.null (S.intersection varsToAvoid dependentVars)

    collectDependentVarsExp exp =
     case unLoc exp of
       VarE v@(Var symbol) ->
            case M.lookup symbol defTable of
              Nothing -> S.empty
              Just (DefTableEntry definingExp _ _ _) ->
                  S.insert v  (collectDependentVarsExp (l definingExp))

       AppE fName _ args -> S.unions (L.map collectDependentVarsExp args )
       MkProdE expList -> S.unions (L.map collectDependentVarsExp expList)
       PrimAppE _ args->  S.unions (L.map collectDependentVarsExp args )

       IfE cond thenBody elseBody      ->
         S.unions
           [collectDependentVarsExp cond, collectDependentVarsExp thenBody,
              collectDependentVarsExp elseBody ]
       DataConE _ _ expList -> S.unions (L.map collectDependentVarsExp expList)
       ProjE index exp -> collectDependentVarsExp exp
       LitE _ -> S.empty
       x       -> error ( "please handle me explicitly" L.++ (show x))

cleanExp ::  L Exp1 -> L Exp1
cleanExp exp = removeCommonExpressions (removeUnusedDefsExp exp)


-- argsVars represents the arguments of the function that contains oldExp
tuple :: DDefs Ty1 -> FunDefs1 -> L Exp1 -> [Var] -> Int -> PassM (L Exp1,  FunDefs1)
tuple ddefs fdefs oldExp_ argsVars depth= do
 if depth> 10 then return (oldExp_, fdefs)
 else
  do
--lets pic one at a time only !!
    let oldExp = cleanExp oldExp_
  -- candidates1 : a list of [(fName, CallExpressions)] functions that traverses
  -- same input
    let candidates1 = L.filter f (M.toList (buildTupleCandidatesTable
           fdefs  oldExp argsVars) )
         where f (_, ls) = L.length ls> 1

  -- candidates2: a list  [(tupleName, calls, syncedArgsLocs)]
  -- syncedArgsLocs = [((1,2),(3,4)),..] this means args 4 in f3 is the same as
  -- arg 2 in f1
    let candidates2 = L.map  ( \(traversedVar, ls) ->
            let sortedCalls = L.sortOn f ls
                   where f exp@(AppE fName _ _) = (fName, exp)
                syncArgsLocs = computeSyncedArgs sortedCalls

            in (constructName sortedCalls (M.toList syncArgsLocs), sortedCalls,
                 syncArgsLocs)
               --`debug` ("orgArgs:" L.++ (render (pprint sortedCalls)) L.++ "\nargs" L.++ (show syncArgsLocs))
                ) candidates1

    --(newExp, fdefs') <-  Control.Monad.foldM go (oldExp, fdefs)  candidates2
    if L.length candidates2 > 0
      then
        do
           (newExp, fdefs') <- go (oldExp, fdefs) (L.head candidates2)
           let newExp' = removeUnusedDefsExp (simplifyProjections newExp )
           (newExp'', fdefs'') <- tuple ddefs fdefs'  newExp' argsVars depth
           return (newExp'', fdefs'')
      else
         return (oldExp, fdefs) `debug` (show "no candidates")
   where
    go (exp, fdefs) (tupledFName, callExpressions, syncArgsLocs) =
      case M.lookup tupledFName fdefs of
        Just fdef -> do
            exp' <-foldTupledFunctions exp fdef callExpressions
                 (getOutputStartPositions fdefs callExpressions) syncArgsLocs

            let exp'' =  simplifyProjections exp'
            return (exp'', fdefs) `debug` ("fold1" L.++ render (pprint exp''))

        Nothing -> do
            let functionsToTuple = L.map getCalledFunDef  callExpressions
                  where
                    getCalledFunDef callExpr = case callExpr of
                        (AppE fName _ _) -> case M.lookup fName fdefs of
                             Just fdef -> fdef

            tupledFunction <-
              tupleListOfFunctions
                 ddefs functionsToTuple tupledFName syncArgsLocs
                 --   `debug` ("funcs to tuple" L.++ (show functionsToTuple))

            let tupledFunction' =
                  tupledFunction {funBody = cleanExp (funBody tupledFunction)}
                   -- `debug` ("tupled f is :" L.++ (render(pprint tupledFunction)))

            let fdefs' = M.insert tupledFName  tupledFunction'  fdefs
            let traversedArg =  funArgs tupledFunction'

            (recTupledBody, newDefs) <-
               tuple ddefs fdefs' (funBody tupledFunction')  traversedArg  (depth+1)
                 -- `debug` ("\n tupling :" L.++ (show tupledFName)
                  --    L.++ (render (pprint  tupledFunction')  )
                --    )

            let tupledFunction'' = tupledFunction'{funBody=recTupledBody}
            let tupledFunction''' =
                  tupledFunction''{funBody= removeUnusedDefsExp
                    (simplifyProjections (funBody tupledFunction''))}

            let tupledFunction5 =
                 tupledFunction''' {funBody = removeUnusedDefsExp(
                    simplifyProjections (funBody tupledFunction''' )) }

            let fdefs'' = M.insert tupledFName tupledFunction5  newDefs

            exp' <-
              foldTupledFunctions exp  tupledFunction5 callExpressions
                   (getOutputStartPositions fdefs''
                   callExpressions ) syncArgsLocs

            let exp'' = simplifyProjections exp'

            return (exp'', fdefs'')  `debug` ("fold2" L.++ render (pprint exp''))


    constructName ls syncArgsLocs =
      let syncedArgsText = L.foldr f "" syncArgsLocs
           where
            f ((f1, id1), (f2, id2)) txt =
              txt L.++ "f" L.++ (show f1) L.++ "_" L.++ (show id1) L.++ "_from_" L.++
              "f" L.++
              show (f2) L.++
              "_" L.++
              (show id2) L.++
              "_n_"
      in toVar
          ("_TUP_" L.++ L.foldl appendName "" ls L.++ syncedArgsText L.++ "_TUP_")

    appendName str (AppE fName _ _) =
       str L.++ "_t_" L.++ fromVar fName

    computeSyncedArgs callExpressions =
     --list of vectors of args [V1, V2 ...]
      let argsLists = L.map f callExpressions
            where
              f (AppE _ _ (h:tail)) = V.fromList tail

          -- single list of (func-pos, arg-pos, argExp) all args in one list
          allArgsList = V.ifoldr f [] (V.fromList argsLists)
            where
              f idxFunc argsV res =
               res L.++ V.toList
                 (V.imap (\idxVar var -> (idxFunc, idxVar + 1, var)) argsV)
          redundantPositions = L.foldr f (M.empty, M.empty) allArgsList
            where
             f (funPos, argPos, argExp) (firstAppear, redundant) =
                 if M.member argExp firstAppear
                  then
                  (firstAppear,
                    M.insert (funPos, argPos) (firstAppear M.! argExp) redundant)
                  else
                    (M.insert argExp (funPos, argPos) firstAppear ,redundant)

       in snd redundantPositions

fixCalls :: L Exp1 -> FunDef1 -> M.Map Int Int  -> M.Map Int Int -> Var->L Exp1
fixCalls exp fdef redirectMap outputFromInput newName = go exp
    where
      go exp = case unLoc exp of
        CaseE e ls ->
          let ls' = L.map (\(x, y, ex)-> (x, y, go ex)) ls
          in  l $ CaseE e ls'
        LetE (Var y, loc, t, rhs) body->
          case unLoc rhs of
            AppE v ls args ->
              if v == funName fdef
                then
                  let t' = snd (funTy fdef) in
                  let rhs' = l $ AppE newName ls args in
                  let
                    body'=  L.foldl
                        (\ex (i, j )->
                              let oldExp = l $ProjE i ( l (VarE (Var y)) )
                                  newExp = getExpAtIndex args j
                              in  substE oldExp newExp ex  `debug` ("replacing" L.++ (show oldExp) L.++"with" L.++ ( show newExp)L.++ (show outputFromInput ))
                        ) body (M.toList outputFromInput)

                    body'' = L.foldl
                        (\ex (i, j )->
                         if i==j
                             then ex
                           else
                              let oldExp = l $ProjE i ( l (VarE (Var y)) )
                                  newExp = l $ProjE j ( l (VarE (Var y)) )
                              in  substE oldExp newExp ex `debug` ("replacing" L.++ (show oldExp) L.++"with" L.++ ( show newExp))
                        ) body' (M.toList redirectMap)-- in

                  in l $ LetE (Var y, loc, t',  rhs') (go  body'')
                else
                  l $  LetE (Var y, loc, t, rhs) (go body)
            _ ->
              l $  LetE (Var y, loc, t, rhs) (go body)
        otherwise -> l otherwise

getExpAtIndex ::  [L Exp1] -> Int -> L Exp1
getExpAtIndex ls id = ls L.!! id

getOutputStartPositions:: FunDefs1 -> [Exp1]  -> V.Vector Int
getOutputStartPositions fdefs callExpressions =
     let functionsArgsLengths = L.map getCalledFunDef  callExpressions in
     let ls = L.foldl (\ls i -> ls L.++ [i+ L.last ls]  ) [0]
          functionsArgsLengths
     in  V.fromList ls
   where
     getCalledFunDef callExpr = case callExpr of
          (AppE fName _ _) ->
            case M.lookup fName fdefs of
              Just fdef -> case snd (funTy fdef) of
                ProdTy ls -> L.length ls
                _ -> 1

-- the last input argument is a set of already fused functions in the form of
-- [(outer, inner, 0, fusedFunName)]
fuse :: DDefs Ty1 -> FunDefs1 -> Var -> Var -> [(Var, Var, Int, Var)]
     -> PassM (Bool, Var,  FunDefs1)
fuse ddefs fdefs  innerVar  outerVar prevFusedFuncs = do
    innerFunc <-  freshFunction (fdefs M.! innerVar)
    outerFunc <- freshFunction (fdefs M.! outerVar)

    config <- getGibbonConfig
    newName <- if verbosity config >= 0
            then  return (toVar ("_FUS_f_" ++ fromVar outerVar ++ "_f_" ++
                    fromVar innerVar ++ "_FUS_"))
            else gensym "_FUSE_"

    step1 <- inline2 innerFunc outerFunc
    -- `debug`
        -- ("inner: " L.++ (render (pprint innerFunc)) L.++ "outer: " L.++ (render (pprint outerFunc)))

    let step2 = (simplifyCases step1 ){funName = newName} --`debug` render (pprint step1)
        step3 = foldFusedCallsF (outerVar, innerVar, -1, newName)  step2 --`debug` render (pprint step2)
        step4 = L.foldl (flip foldFusedCallsF ) step3 prevFusedFuncs --`debug`   render (pprint step3)
        step5 = step4 {funBody = removeUnusedDefsExp  (funBody step4)} --`debug` render (pprint step4)
    return (True, newName, M.insert newName step5 fdefs)

violateRestrictions :: FunDefs1 -> Var -> Var -> Bool
violateRestrictions fdefs inner outer =
  let innerDef =
        case M.lookup inner fdefs of
          (Just v) -> v
      outerDef =
        case M.lookup outer fdefs of
          (Just v) -> v
      p1 =
        if (length (fst (funTy innerDef)) > 0)
          then case head (fst (funTy innerDef)) of
                 (PackedTy _ _) -> False
                 x              -> True
          else True
      p2 =
        if (length (fst (funTy innerDef)) > 0)
          then case head (fst (funTy outerDef)) of
                 (PackedTy _ _) -> False
                 x              -> True
          else True
      p3 =
        case (unLoc (funBody innerDef)) of
          CaseE _ ls ->
            not
              (L.foldr (\(_, _, exp) res -> res && (hasConstructorTail exp)) True ls)
          _ -> True
      p4 =
        case (unLoc (funBody outerDef)) of
          CaseE _ _ -> False
          _         -> True
   in (p1 || p2 || p4)

type FusedElement =
  (Var, -- outer fused function
   Var, -- Inner fused function
   Int, -- position at which inner is consumed
   Var -- the name of the fused function
  )

type TransformReturn =
  (L Exp1, --transformed expression
   FunDefs1, -- updates functions stores
   [FusedElement] -- list of functions that are fused during the transformation
  )

data FusePassParams =  FusePassParams
 { exp             :: L Exp1, -- expression to transform
   args            :: [Var], -- arguments of the function that the transformed
                            -- expression belongs to
   fusedFunctions :: [FusedElement], -- already fused functions
   skipList       :: [(Var, Var)], -- functions to skip for fusion purposes
   depth          :: Int
  } deriving (Show , Generic)


tuple_pass :: DDefs Ty1 -> FunDefs1 -> PassM (FunDefs1)
tuple_pass ddefs fdefs =
    foldM tupleFunction fdefs fdefs
  where
   tupleFunction defs' f  =
    do
      let fName = funName f
      if L.isPrefixOf "_FUS"  (fromVar fName) ||  L.isPrefixOf "_TUP"  (fromVar fName)
        then do
          (tupledBody, tupleDefs) <- tuple ddefs fdefs (funBody f) (funArgs f) 0
          let defs'' = M.insert fName f{funBody = tupledBody} defs'
          return (M.union  defs'' tupleDefs)

        else
          return defs'


fuse_pass ::  DDefs Ty1 -> FunDefs1 -> FusePassParams  -> PassM TransformReturn
fuse_pass ddefs funDefs
   (FusePassParams exp argsVars fusedFunctions skipList depth) =
  if depth >1000
   then  return (exp, funDefs, fusedFunctions)
   else go (unLoc exp) skipList funDefs fusedFunctions
 where
  go body processed fdefs prevFusedFuncs = do
    let defTable = buildDefTable body
        potential = findPotential defTable processed
    case potential of
      Nothing -> do
        let final_clean = removeUnusedDefsExp (l body)
        return  (final_clean, fdefs, prevFusedFuncs)

      Just ((inner,outer), outerDefVarSymbol) ->
       do
        if violateRestrictions fdefs inner outer
          then
               go  body ((inner,outer):processed) fdefs prevFusedFuncs
          else do
             -- fuse
            (validFused, fNew, fusedDefs) <-
               fuse ddefs fdefs inner outer prevFusedFuncs

            let fusedFunction = fusedDefs M.! fNew  --`debug` ("new fused:" L.++ (
               --  render (pprint ( fusedDefs M.! fNew  ))))
                newFusedEntry = (outer,inner, -1, fNew)
                newFusedFunctions =  newFusedEntry : prevFusedFuncs
                newProcessed = (inner,outer):processed

            (retFuncBody, retFunDefs, retFusedFunctions) <- fuse_pass  ddefs
              fusedDefs  (FusePassParams (funBody fusedFunction)  (funArgs fusedFunction)
                newFusedFunctions newProcessed (depth+1))

            --clean
            let newFusedFunctions = retFusedFunctions
              --   (newFusedEntry : prevFusedFuncs) L.++ retFusedFunctions
                cleanedFunction =
                    removeUnusedDefs fusedFunction{funBody = retFuncBody}
                fdefs_tmp2       = M.union fusedDefs retFunDefs
                fdefs_tmp3       = M.insert  fNew cleanedFunction fdefs_tmp2
                newDefs =  (M.union fdefs fdefs_tmp3)

            let foldedBody = foldFusedCalls (outer,inner, -1, fNew) (l body)
            if validFused
              then
                let body' = removeUnusedDefsExp foldedBody
                in go (unLoc body') newProcessed  newDefs  newFusedFunctions
              else
                 go body  newProcessed fdefs prevFusedFuncs

tupleAndOptimize :: DDefs Ty1 -> FunDefs1 -> PassM (FunDefs1)
tupleAndOptimize ddefs fdefs =
  do
    newDefs <- tuple_pass ddefs fdefs
    if newDefs == fdefs
      then return newDefs
      else  tupleAndOptimize ddefs (redundancy_output_pass newDefs) `debug` "run new tuple round"

fusion2 :: Prog1 -> PassM Prog1
fusion2 (L1.Prog defs funs main) = do
  (main', funs') <-
    case main of
      Nothing -> return (Nothing, funs)
      Just (mainBody, ty) -> do
        (mainBody', newDefs, _) <-
          fuse_pass defs funs (FusePassParams mainBody [] [] [] 0)
        newDefs' <- tupleAndOptimize defs (M.union funs newDefs)
        return (Just (mainBody', ty), newDefs')

  return $ L1.Prog defs funs' main'


-- Those  functions are used for the redundancy analysis
redundancy_output_pass :: FunDefs1 -> FunDefs1
redundancy_output_pass fdefs =
  let (fdefs', rules) = M.foldl (pass1F fdefs) (fdefs, M.empty) fdefs
      fdefs'' = M.foldlWithKey pass2F fdefs' rules
   in if fdefs'' == fdefs
        then fdefs''
        else redundancy_input_pass fdefs''
  where
    pass2F fdefs fName (redirectMap, outPutFromInput, newName) =
      M.map (pass2Fsub fdefs fName (redirectMap, outPutFromInput, newName)) fdefs

    pass2Fsub fdefs fName (redirectMap, outPutFromInput, newName) f =
      f
        { funBody =
            removeUnusedDefsExp
              (simplifyProjections
                 (removeCommonExpressions
                    (fixCalls
                       (funBody f)
                       (fdefs M.! fName)
                       redirectMap
                       outPutFromInput
                       newName
                       )))
        }

    pass1F orgFdefs (fdefs, rules) f =
      let fName = funName f
       in if L.isPrefixOf "_TUP" (fromVar fName)
            then let  testedPositions =
                            testAllOutputPositions orgFdefs fName M.empty

                      newName =  toVar (fromVar fName L.++ "outputFixed") in
                      if M.member newName fdefs
                        then
                         (fdefs, rules)

                        else

                          let  (fNew, redirectMap, outPutFromInput) =
                                 removeRedundantOutput
                                 f
                                testedPositions --`debug` ("testing" L.++ (show fName))

                         in ( M.insert (funName fNew) fNew fdefs
                             ,M.insert fName (redirectMap, outPutFromInput, funName fNew) rules)
                      --  `debug` ((show fName) L.++ "new things" L.++  (show (getOutputsFromInput f)))
            else (fdefs, rules)


testAllOutputPositions:: FunDefs1 -> Var -> M.Map (Var,Int,Int) Bool ->
  M.Map (Var,Int,Int) Bool
testAllOutputPositions  fdefs fName testedPositions =
   let f = fdefs M.! fName
       n = case snd (funTy f) of
             ProdTy ls -> L.length ls
   in loop1 0 0 n testedPositions
  where
    loop1 i j n testedPositions =
      if j>=n
        then
          testedPositions
        else
          if i>= n
            then
              loop1 0 (j+1) n testedPositions
            else
               loop1 (i+1) j n (snd( testTwoOutputPositions fdefs (fName, i, j) testedPositions))
               --  `debug` (show"start" L.++ show((fName, i, j) ))

testTwoOutputPositions :: FunDefs1 -> (Var, Int, Int) -> M.Map (Var,Int,Int) Bool
  -> (Bool,  M.Map (Var,Int,Int) Bool)
testTwoOutputPositions fdefs (fName, i, j) testedPositions =
  if i==j then (True, testedPositions)
    else
      case M.lookup (fName, i, j) testedPositions of
        Just res -> (res, testedPositions)
        Nothing ->
          case M.lookup (fName, j, i) testedPositions of
            Just res -> (res, M.insert (fName, j, i) res testedPositions)
            Nothing ->
              let (cond, inductiveAssumption, unresolvedConditions) =
                    extractAssumptionAndConditions fName i j
              in if cond
                  then
                    let (cond', inductiveAssumption') =
                          testTwoOutputPositionsRec inductiveAssumption unresolvedConditions
                    in if cond'
                       then
                        -- if there are not more conditions to resolve then we
                        --  are done and correct !
                          let testedPositions' = S.foldl
                                (\mp (fName, i, j)  -> M.insert (fName, i, j) True mp)
                                  testedPositions   inductiveAssumption'
                          in (True, testedPositions')
                      else
                        (False, M.insert (fName, i, j) False testedPositions)

                  else
                      (False, M.insert (fName, i, j) False testedPositions)


 where
  testTwoOutputPositionsRec inductiveAssumption unresolvedConditions =
    -- for each unresolved condition
    -- 1-check if equivalent rules are satisfied
    -- 2-if not return false
    -- 3-if yes move it to inductive assumptions and add the appropriate new
    --  conditions if any
    -- 4-if at the end result is false we are done, otherwise if there is no
    -- unresolvedConditions then proof is done also, otherwise call perform the
    -- call recursively.
    let (res, inductiveAssumption', unresolvedConditions') =
          S.foldl f (True, inductiveAssumption, S.empty) unresolvedConditions
        unresolvedConditions'' = S.filter  (\(f, i, j)->
            S.notMember (f, i, j) inductiveAssumption' &&
              S.notMember (f, j, i) inductiveAssumption') unresolvedConditions'

    in if res && S.null unresolvedConditions''
         then (res, inductiveAssumption')
         else
            if res==False
              then
               (False, S.empty)
              else
                testTwoOutputPositionsRec inductiveAssumption'  unresolvedConditions''

  f (condInput, assumptionsInput, unresolvedInput) (fName, i, j) =

    let (cond, inductiveAssumption, unresolvedConditions) =
              extractAssumptionAndConditions fName i j
    in (cond && condInput, S.union assumptionsInput inductiveAssumption,
        S.union unresolvedConditions unresolvedInput )

  extractAssumptionAndConditions fName i j  =
    let exp = funBody (fdefs M.! fName)
        inlinedContent = inlineAllButAppE exp --`debug` (show (fName) L.++ "inlined body\n"L.++ (render (pprint exp)))
    in case unLoc inlinedContent of
          CaseE e ls ->
            let parametrizedExprsList = L.map parametrizeProdExprs ls
                cond = L.foldl (checkExpressions i j) True parametrizedExprsList
            in if cond
                then
                  let inductiveAssumption  = S.insert (fName, i, j) S.empty
                      unresolvedConditions = L.foldl (collectConditions i j)
                        S.empty parametrizedExprsList

                      unresolvedConditions' = S.filter  (\(f, i, j)->
                        S.notMember (f, i, j) inductiveAssumption &&
                          S.notMember (f, j, i) inductiveAssumption)
                            unresolvedConditions
                  in  (True, inductiveAssumption, unresolvedConditions)
                else
                    (False, S.empty, S.empty)

  parametrizeProdExprs (_, _, subExp) =
      let vars = collectVars subExp
          leafProd = getLeafProd subExp
          varsToFuncs =  collectVarToFuncs  subExp
      in case unLoc leafProd of
        (MkProdE ls) ->L.map  (parametrizeExp vars varsToFuncs) ls
  checkExpressions i j b prodListParametrized=
    let (expi, pars1) =  prodListParametrized L.!! i
        (expj, pars2) = prodListParametrized L.!! j
    in b && expi== expj && parsCheck pars1 pars2

  parsCheck [] [] = True
  parsCheck ((_, v1, _):ls1)  ((_, v2, _):ls2) =
     v1==v2 && parsCheck ls1 ls2

  collectConditions i j s prodListParametrized =
    let (_, ls1) =  prodListParametrized L.!! i
        (_, ls2) = prodListParametrized L.!! j
        s' = collectConditionsPars  ls1 ls2
    in S.union s' s

  collectConditionsPars [] [] = S.empty
  collectConditionsPars ((idx1, v1, f):ls1)  ((idx2, v2, _):ls2) =
     let sNext =  collectConditionsPars ls1 ls2
     in if idx1==idx2
          then
            sNext
          else
            S.insert (f, idx1, idx2) sNext

getLeafProd :: L Exp1 -> L Exp1
getLeafProd = rec
 where
   rec ex =
     case unLoc ex of
       LetE (v, ls, t, L _ AppE{}) body -> rec body
       leaf@MkProdE{} -> l leaf
       x-> error (show x)

hasConstructorTail :: L Exp1 -> Bool
hasConstructorTail = rec
  where
    rec ex =
      case unLoc ex of
        LetE _ body -> rec body
        DataConE _ _ _ -> True
        x -> False

collectVars :: L Exp1 -> S.Set Var
collectVars = rec
 where
   rec ex = case unLoc ex of
     LetE (v, ls, t, L _ AppE{}) body ->
        S.insert v (rec body)
     MkProdE{} -> S.empty

collectVarToFuncs :: L Exp1 -> M.Map Var Var
collectVarToFuncs = rec
 where
   rec ex = case unLoc ex of
     LetE (v, ls, t, L _  (AppE f _ _)) body ->
       M.insert v  f  (rec body)
     MkProdE{} -> M.empty

-- Given a set of variables that represents results of function calls
-- and a mapping from those variables to the called function
-- and an expression => parameterize the expression around those
parametrizeExp ::  S.Set Var ->  M.Map Var Var -> L Exp1 -> (L Exp1, [(Int, Var, Var)])
parametrizeExp vars mp exp   =
 let (retExp, ls) = rec exp []
 in (retExp, L.map (\(i, v)-> (i, v, mp M.! v )) ls )
  where
    rec ex ls = case unLoc ex of
      LetE{} -> error "let not expected in parametrizeExp"
      -- TODO: this is work around (correct not complete)[should be also handled]
      x@(CaseE caseE caseLs) -> (l x, ls)
       -- error( "CaseE not expected in parametrizeExp" ++ (render (pprint ex )))
      AppE v loc args ->
        let (args', pList) = L.foldl f ([], ls) args
             where
               f (expList, projList) exp =
                  let (exp' , ls') = rec exp projList
                  in (expList L.++ [exp'], projList L.++ ls')
        in (l (AppE v loc args'), pList)

      DataConE loc dataCons expList->
        let (expList', pList) = L.foldl f ([], ls) expList
             where
               f (expList, projList) exp =
                 let (exp' , ls') = rec exp projList
                 in (expList L.++ [exp'], projList L.++ ls')
        in (l (DataConE loc dataCons expList'), pList)

      x@(ProjE i (L _ (VarE v))) ->
          if S.member v vars
              then
                let exp' = VarE (toVar ("par" L.++ show (L.length ls)))
                    ls' = ls L.++ [(i, v)]
                in (l exp', ls')
              else
                (l x, ls)
      otherwise -> (l otherwise, ls)

-- this function inline all expressions except function application
-- that returns tuples
inlineAllButAppE::L Exp1 -> L Exp1
inlineAllButAppE = rec
 where
  rec ex = case unLoc ex of
    LetE (v, ls, t, bind) body ->
     let oldExp = l $ VarE v
         newExp = bind
         body' = substE oldExp newExp body
     in case unLoc bind of
          AppE{} -> case t  of
               ProdTy{} -> l$  LetE (v, ls, t, bind) (rec body)
               _ ->  rec body'
          _      ->  rec body'
    CaseE e ls    ->
      let ls' = L.map (\(x, y, exp) -> (x, y, rec exp)) ls
      in  l$ CaseE e ls'
    otherwise ->  l otherwise

-- This function optimizes the tupled function by removing redundant output
-- parameters and their computation.
-- redundant positions are pr-computed and stored in testedPositions.
removeRedundantOutput :: FunDef1 -> M.Map (Var,Int,Int) Bool  -> (FunDef1, M.Map Int Int, M.Map Int Int)
removeRedundantOutput  fdef testedPositions =
    let outputsFromInputs = getOutputsFromInput fdef in
    let outputTuples = V.fromList  (collectOutputs (funBody fdef)) in
    let firstTuple = outputTuples V.! 0   in --return vector
    let loop i j =
         if j >= (V.length firstTuple)
          then []
          else
            let res =
                 if(M.member (funName fdef, i, j) testedPositions)
                  then testedPositions  M.!  (funName fdef, i, j)
                  else  testedPositions  M.!  (funName fdef, j, i)
            in if res
              then [j] L.++ (loop i (j+1))
              else  loop i (j+1)

        candidates = V.ifoldl
          (\ls idx _ ->
            let matches = V.fromList(loop idx (idx+1))
                cands =  L.map (idx,) (V.toList matches)  --`debug` (show matches)
            in (ls L.++ cands)
          ) [] firstTuple

        ncols = V.length firstTuple
        nrows = V.length outputTuples
        initialMap = M.fromList (L.map (, []) [0..(ncols-1)])
    --    tricky!
        finalMap = L.foldl
            (\mp (i, j) ->
              let k = L.foldl
                    (\k idx -> if k /= -1
                       then k
                       else
                         case M.lookup idx mp of
                           Nothing -> k
                           Just ls ->
                             case L.elemIndex i ls of
                                Nothing -> k
                                otherwise -> idx
                    ) (-1) [0..i]
                  mp' = M.delete j mp
              in if k== -1
                  then M.insert i ((mp' M.! i) L.++ [j] ) mp'
                  else M.insert k ((mp' M.! k) L.++ [j] ) mp'
            ) initialMap candidates

        removedPositions_ = L.foldl
           (\ls i ->
            case M.lookup i finalMap of
              Nothing -> ls L.++[i]
              otherwise -> ls
          ) [] [0..(ncols-1)]

        removedPositions =
           S.toList (S.union
               (S.fromList removedPositions_)
               (S.fromList (L.map (\(x,y)->x )  (M.toList outputsFromInputs) )))
        newFunType =
          let oldOutTypesList = V.fromList (
                case snd(funTy fdef) of ProdTy ls->ls)
              newOutTypesList = V.ifoldl
                (\ls idx ty ->
                   case L.elemIndex idx removedPositions of
                      Nothing -> ls L.++[ty]
                      otherwise-> ls
                ) [] oldOutTypesList
          in (fst(funTy fdef), ProdTy newOutTypesList )

        newOutputTuples = V.map removeDropped outputTuples
          where
            removeDropped ls = MkProdE (V.ifoldl
               (\ls idx exp ->
                  case L.elemIndex idx removedPositions of
                    Nothing -> ls L.++[exp]
                    otherwise -> ls
               ) [] ls)

        newFunBody = case unLoc (funBody fdef) of
          CaseE e ls ->
              let ls' = V.toList (V.imap
                   (\idx (x, y, exp)->
                        let exp' = replaceLeafExp exp ( l (newOutputTuples V.! idx) )
                        in (x, y, exp')) (V.fromList ls))
              in  l$ CaseE e ls'
        fdef' = fdef{funBody = newFunBody, funTy = newFunType}

        redirectMap = V.ifoldl
            (\mp idx (i, ls)->
                let mp'  = M.insert i idx mp
                    mp'' = L.foldl (\m j -> M.insert j idx m) mp' ls
                in mp''
            ) M.empty (V.fromList (M.toList finalMap))

        removedUnhandled = L.map (\(a, b)->a) (M.toList outputsFromInputs)
        redirectMap'  = L.foldl (\mp i->M.delete i mp) redirectMap removedUnhandled
        redirectMap''  = M.map (\v -> v- (countLess v)) redirectMap'
          where
            countLess v = L.foldl (\res a-> if (a<v) then 1+res else res)
               0 removedUnhandled

        fdef'' =
          fdef'{funName =
             if (newFunBody == funBody fdef)
                     then funName fdef'
                     else toVar (fromVar (funName fdef') L.++"outputFixed" )
              }
    in (fdef'',  redirectMap'', outputsFromInputs) --`debug` ("summer for " L.++ (show (funName fdef')) L.++ (show  outputsFromInputs ))

 where
  replaceLeafExp exp replacement =
    case unLoc exp of
      LetE (v, ls, t, bind) body ->
         l $  LetE (v, ls, t, bind) (replaceLeafExp body replacement)
      MkProdE ls -> replacement

  collectOutputs exp = case unLoc exp of
    CaseE e ls ->
         L.map (\(x, y, subBody) -> V.fromList(extractLeafTuple subBody)) ls
     where
        extractLeafTuple exp =
           case unLoc exp of
              LetE (v, ls, t, bind) body -> extractLeafTuple body
              MkProdE ls -> ls
              _ -> error "not expected expression"

    _ -> error"should be case expression"

eliminateInputArgs :: FunDefs1 -> Var -> M.Map Int Int -> (Var, FunDefs1)
eliminateInputArgs fdefs fNameOld syncedArgs =
  let newName = toVar ((M.foldlWithKey buildName ((fromVar fNameOld) L.++ "elimpass_") syncedArgs)L.++"_elimpass")
      fdefs' =
            if M.member newName fdefs
              then fdefs
              else
                   let oldFdef = fdefs M.! fNameOld
                       oldInputType = fst (funTy oldFdef)
                       oldArgs = funArgs oldFdef
                       oldBody = funBody oldFdef
                       newInputType =
                         V.toList
                           (V.ifilter
                              (\idx _ -> M.notMember idx syncedArgs)
                              (V.fromList oldInputType)
                           )
                       newArgs =
                         V.toList
                           (V.ifilter
                              (\idx _ -> M.notMember idx syncedArgs)
                               (V.fromList oldArgs)
                           )
                       newBody =
                         M.foldlWithKey
                           (\exp k v ->
                              if (v<1000)
                              then
                                let oldExp = l $ VarE ((V.fromList oldArgs) V.! k)
                                    newExp = l $ VarE ((V.fromList oldArgs) V.! v)
                                 in substE oldExp newExp exp
                              else
                                exp
                              )
                           (oldBody)
                           syncedArgs
                       newFdef =
                         oldFdef
                           { funBody = cleanExp newBody
                           , funArgs = newArgs
                           , funTy = (newInputType, snd (funTy oldFdef))
                           , funName = newName
                           }
                    in M.insert newName newFdef fdefs
  in (newName, fdefs')
 where
    buildName name i j =
      name L.++ "_sync" L.++ (show i) L.++ "_fr_" L.++ (show j) L.++ "sync_"

-- simplest version for single functions
getOutputsFromInput ::FunDef1 -> M.Map Int Int
getOutputsFromInput func  =
  let body = funBody func
      leafProducts = case unLoc body of
            CaseE e ls ->
               L.map (\(_,_,exp) -> getLeafProdExpressions exp) ls
      inputVars = funArgs func
      candidatesList =

       L.map(\exprList->
          V.ifoldl f M.empty (V.fromList exprList)) leafProducts
         where f out idx outExp =
                case unLoc outExp of
                    VarE v ->
                      case L.elemIndex v inputVars of
                        Nothing -> out
                        Just argIdx -> M.insert idx argIdx out
                    otherwise -> out
      candidatesListSets = L.map (\mp-> S.fromList (M.toList mp)) candidatesList
      intersectionsSet = L.foldl S.intersection (L.head candidatesListSets) candidatesListSets
      in M.fromList (S.toList intersectionsSet)

getLeafProdExpressions :: L Exp1 -> [L Exp1]
getLeafProdExpressions = rec
 where
   rec ex =
     case unLoc ex of
       LetE (v, ls, t, L _ AppE{}) body -> rec body
       MkProdE ls -> ls
       x-> []


removeRedundantInputExp :: FunDefs1 -> L Exp1 ->Bool -> (FunDefs1,L Exp1)
removeRedundantInputExp fdefs exp  mode =
  case unLoc exp of
    CaseE e ls ->
      let (fdefs', e') = removeRedundantInputExp fdefs e mode
          (fdefs'', ls') = L.foldl f (fdefs', []) ls
            where
              f (fdefsInner, lsInner) (dataCon, vars, exp) =
                let (fdefsInner', exp') = removeRedundantInputExp fdefsInner exp mode
                 in (fdefsInner', lsInner L.++ [(dataCon, vars, exp')])
       in (fdefs'', l $ CaseE e' ls')

    LetE rhs@(var, ls, t, bind) body ->

      let (fdefs', body') = removeRedundantInputExp fdefs body mode
          boringCase =  (fdefs', l (LetE rhs  body'))
      in case unLoc bind of
          x@( AppE fName loc args) ->
            if (L.isPrefixOf "_TUP"  (fromVar fName) ||
                L.isPrefixOf "_FUS" (fromVar fName) )
                then

                  let redundantPositions =
                       if(mode)
                        then
                          snd( V.ifoldl findRedundantPos (M.empty, M.empty) (V.fromList args))
                        else
                           V.ifoldl (findRedundantPos_UnusedArgs fName) M.empty (V.fromList args)
                        --        redundantPositions3 = M.union redundantPositions2 redundantPositions `debug`
                        -- ("checking call to :" L.++ (show fName) L.++ "opppaaaa" L.++ show redundantPositions2)
                  in
                   if M.null redundantPositions
                    then
                      boringCase
                    else

                      let (fNameNew, fdefsNew) =
                            eliminateInputArgs  fdefs' fName  redundantPositions
                          newCall =
                            AppE fNameNew loc
                              (V.toList
                                (V.ifilter
                                  (\idx _ -> M.notMember idx  redundantPositions )
                                     (V.fromList args)))
                      in (fdefsNew,l (LetE (var, ls, t, (l newCall)) body' ))
                else
                  boringCase
          otherwise -> boringCase
    otherwise ->  (fdefs, l otherwise)

   where
        findRedundantPos (firstAppear, redundant) argIdx arg =
            if M.member arg firstAppear
                then
                  (firstAppear, M.insert argIdx (firstAppear M.! arg) redundant)
                else
                  (M.insert arg argIdx firstAppear, redundant)

        findRedundantPos_UnusedArgs fName mp argIdx arg =
           let callee = fdefs M.! fName in
           if (isUsedArg (funBody callee)  ((V.fromList (funArgs callee)) V.! argIdx ))
              then mp
              else M.insert argIdx 100000 mp

        isUsedArg exp var =
          case unLoc exp of
            ProjE i e  ->
              isUsedArg e var

            VarE v'    ->
              v' == var

            CaseE e ls ->
              let b1 = isUsedArg e var
                  b2 =
                    L.foldl (\res (dataCon, vars, ex)->
                                (res || isUsedArg ex var ))
                            False ls
              in b1 || b2


            AppE fName loc args ->
                L.foldl (\res ex -> (res || isUsedArg ex var )) False args

            LetE (v, ls, t, bind) body -> (isUsedArg bind var)|| (isUsedArg  body var)
            PrimAppE p ls ->  L.foldl (\res ex -> (res || isUsedArg ex var )) False ls
            MkProdE ls    ->  L.foldl (\res ex -> (res || isUsedArg ex var )) False ls
            DataConE _ _ ls-> L.foldl (\res ex -> (res || isUsedArg ex var )) False ls

            x       -> False `debug` ("not handled is "L.++ (show x))




removeRedundantInputFunc :: FunDefs1 -> FunDef1 -> FunDefs1
removeRedundantInputFunc fdefs fdef =
  let (fdefs', exp) = removeRedundantInputExp fdefs (funBody fdef) True
    --    `debug` ("Dowing1"L.++ (render (pprint fdef)))
      fdef' = fdef {funBody = exp}
      (fdefs'', exp') = removeRedundantInputExp (M.insert (funName fdef) fdef' fdefs')
                          exp False
      fdef'' = fdef' {funBody = exp'}-- `debug` ("Dowing2 "L.++ (render (pprint (fdef' {funBody = exp'}))))

  in (M.insert (funName fdef) fdef'' fdefs'')

redundancy_input_pass :: FunDefs1 -> FunDefs1
redundancy_input_pass fdefs =
  let fdefs' =
        M.foldl
          (\fDefsInner fdef -> removeRedundantInputFunc fDefsInner fdef)
          fdefs
          fdefs
   in if fdefs' == fdefs
        then fdefs'
        else redundancy_output_pass fdefs'
