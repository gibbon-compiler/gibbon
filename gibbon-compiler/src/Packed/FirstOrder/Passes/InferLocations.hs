
{-# LANGUAGE OverloadedStrings #-}

-- TEMP:
-- {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
-- {-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- TEMP:
-- {-# OPTIONS_GHC -Wno-all #-}

-- | Convert from L1 to L2, adding region constructs.

module Packed.FirstOrder.Passes.InferLocations
    (-- data types
     FullEnv, TiM, InferState, Result, UnifyLoc, Failure, Dest(..),
     -- functions for manipulating locations
     fresh, freshUnifyLoc, finalUnifyLoc, fixLoc, freshLocVar, finalLocVar, assocLoc, finishExp,
          prim, emptyEnv,
     -- main functions
     unify, inferLocs, inferExp, inferExp', convertFunTy)
    where
      
{-
  Basic Strategy
  --------------

The basic strategy here is to use a simple, type-directed pass to translate
programs from L1 to L2. First, we start with a function type, with the 
basic starting assumption that all packed values will have distinct locations:

```
  f  :: Int -> Tree -> Tree
  f' :: forall l_1 in r_1, l_2 in r_2 . Int -> Tree l_1 -> Tree l_2
```

After this, the locations from the function type are treated as *fixed*, and
the inference procedure proceeds to walk through the body of the function.

To infer location bindings in an expression, we build up a set of *constraints*
and propogate them up the expression (ie, recurring on a sub-expression will
yield the constraints induced by that sub-expression). After recurring on 
all sub-expressions, we use these constraints to determine whether to
emit a binding for a new location or a new region.

Constraints in location inference are very similar to constraints used
in type checking L2. When the expression in consideration is a data type
constructor, a series of constraints are generated: the locations for
each field in the constructor are constrained to occur after the previous one
(enforcing that they occur in the right order), and the first field must
occur after the tag of the data constructor itself. 

Knowing all this *isn't enough* to generate the location bindings, however,
since the values that we use in the constructor may have been produced
by multiple different function calls (for example), so the locations 
must carefully be bound earlier in the expression at the right locations.
Ideally, we also want them to be bound as tightly as possible, to avoid
binding locations that aren't used (eg, in some branches of a conditional).
So the constraints are *discharged* as the recursion unwinds.

For example, a constraint that location `loc1` occurs after the value `x2`
can safely be discharged after the value `x2` is bound, so in the handling
of a let binding for a packed value, we search through the constraints 
returned by recurring on the body of the let and discharge any constraint
that invloves a location occurring after that newly-bound variable. 

 Program repair
 --------------

During the inference procedure, unification will occur between locations,
and if two *fixed* locations are unified there will be an error thrown.
To recover, the procedure will have to transform (repair) the expression. 
The simplest way to do this is to insert a copy.

Naively, this simple strategy will require lots of copies. For exmaple, the identity
function's type transforms as follows:

```
  id  :: Tree -> Tree
  id' :: forall l1 in r1, l2 in r2 . Tree l1 -> Tree l2
```

With this type, inferExp will immediately fail on the body of 'id x = x', requiring
a copy-insertion tactic to repair the failure and proceed.

Copy-insertion is very simple. For each data type, we generate a copy traversal
function which matches on each element of the structure. These functions undergo
location inference just like normal user code. During location inference when
a unification failure indicates a copy must be inserted, a call to `"copy_Type"` 
is emitted, where `Type` is the name of the packed data type that must be copied.

-}

import Data.Loc
import qualified Data.Sequence as Seq
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Foldable as F
import Data.Maybe
import qualified Control.Monad.Trans.State.Strict as St
import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans (lift)
import Debug.Trace


import Packed.FirstOrder.GenericOps (gFreeVars)
import Packed.FirstOrder.Common as C hiding (extendVEnv)
import Packed.FirstOrder.Common (Var, Env2, DDefs, LocVar, runSyM, SyM, gensym, toVar)
import qualified Packed.FirstOrder.L1.Syntax as L1
import Packed.FirstOrder.L2.Syntax as L2
import Packed.FirstOrder.L2.Typecheck as T
import Packed.FirstOrder.Passes.InlineTriv (inlineTriv)
import Packed.FirstOrder.Passes.Flatten (flattenL1)

-- Environments
----------------------------------------------------------------------------------------------------

-- | Combine the different kinds of contextual information in-scope.
data FullEnv = FullEnv
    { dataDefs :: (DDefs Ty2)           -- ^ Data type definitions
    , valEnv :: M.Map Var Ty2           -- ^ Type env for local bindings
    , funEnv :: M.Map Var (ArrowTy Ty2) -- ^ Top level fundef types
    } deriving Show

extendVEnv :: Var -> Ty2 -> FullEnv -> FullEnv
extendVEnv v ty fe@FullEnv{valEnv} = fe { valEnv = M.insert v ty valEnv }

lookupVarLoc :: Var -> FullEnv -> LocVar
lookupVarLoc v env = case lookupVEnv v env of
                       PackedTy _ lv -> lv
                       _ -> err $ "Variable does not have location: " ++ (show v)
             
lookupVEnv :: Var -> FullEnv -> Ty2
lookupVEnv v FullEnv{valEnv} = valEnv # v

lookupFEnv :: Var -> FullEnv -> ArrowTy Ty2
lookupFEnv v FullEnv{funEnv} = funEnv # v

-- Types
--------------------------------------------------------------------------------

-- | This helper exemplifies the simplicity of our current approach.
-- If we assume output regions are disjoint from input ones, then we
-- can instantiate an L1 function type into a polymorphic L2 one,
-- mechanically.
convertFunTy :: (L1.Ty1,L1.Ty1) -> SyM (ArrowTy Ty2)
convertFunTy (from,to) = do
    from' <- convertTy from
    to'   <- convertTy to
    -- For this simple version, we assume every location is in a separate region:
    lrm1 <- toLRM from' Input
    lrm2 <- toLRM to'   Output
    return $ ArrowTy { locVars = lrm1 ++ lrm2
                     , arrIn   = from'
                     , arrEffs = S.empty
                     , arrOut  = to'
                     , locRets = [] }
 where
   toLRM ls md =
       mapM (\v -> do r <- freshLocVar "r"
                      return $ LRM v (VarR r) md)
            (F.toList ls)

convertTy :: L1.Ty1 -> SyM Ty2
convertTy ty = traverse (const (freshLocVar "loc")) ty

convertDDefs :: DDefs L1.Ty1 -> SyM (DDefs Ty2)
convertDDefs ddefs = traverse f ddefs
    where f (DDef n dcs) = do
            dcs' <- forM dcs $ \(dc,bnds) -> do
                             bnds' <- forM bnds $ \(isb,ty) -> do
                                               ty' <- convertTy ty
                                               return (isb, ty')
                             return (dc,bnds')
            return $ DDef n dcs'

-- Inference algorithm
--------------------------------------------------------------------------------

-- | The location inference monad is a stack of ExceptT and StateT.
type TiM a = ExceptT Failure (St.StateT InferState SyM) a

-- | The state of the inference procedure is a map from location variable
-- to `UnifyLoc`, which is explained below.
-- This is a bit awkward, since after inference is done we have to make another
-- pass over the AST to update all the `LocVar`s. One refactoring that would
-- make this less awkward would be to make a type-level distinction between
-- `LocVar`s that occur before and after this pass.
-- Also, it would be more efficient to use mutable state directly for this,
-- or possibly some more sophisticated union find thing.
type InferState = M.Map LocVar UnifyLoc

-- | A location is either fixed or fresh. Two fixed locations cannot unify.
data UnifyLoc = FixedLoc Var
              | FreshLoc Var
                deriving (Show, Eq)

data Failure = FailUnify Ty2 Ty2
             | FailInfer L1.Exp1
               deriving (Show, Eq)

---------------------------------------

-- | Constraints here mean almost the same thing as they do in the L2 type checker.
-- One difference is the presence of an AfterTag constraint, though I'm not opposed to
-- adding one to the L2 language for symmetry.
data Constraint = AfterConstantL LocVar Int LocVar
                | AfterVariableL LocVar Var LocVar
                | AfterTagL LocVar LocVar
                | StartRegionL LocVar Region
                  deriving (Show, Eq)

-- | The result type for this pass.  Return a new expression and its
-- type, which includes/implies its location.
type Result = (L Exp2, Ty2, [Constraint])

inferLocs :: L1.Prog -> SyM L2.Prog
inferLocs initPrg = do
  (L1.Prog dfs fds me) <- addCopyFns initPrg
  let m = do
          dfs' <- lift $ lift $ convertDDefs dfs
          fenv <- forM fds $ \(L1.FunDef _ (_,inty) outty _) ->
                  lift $ lift $ convertFunTy (inty,outty)
          let fe = FullEnv dfs' M.empty fenv
          me' <- case me of
            Just me -> do
              (me',ty') <- inferExp' fe me NoDest
              return $ Just (me',ty')
            Nothing -> return Nothing
          fds' <- forM fds $ \(L1.FunDef fn fa frt fbod) -> do
                                   let arrty = lookupFEnv fn fe
                                       fe' = extendVEnv (fst fa) (arrIn arrty) fe
                                   dest <- destFromType (arrOut arrty)
                                   fixType_ (arrIn arrty)
                                   (fbod',_) <- inferExp' fe' fbod dest
                                   return $ L2.FunDef fn arrty (fst fa) fbod'
          return $ L2.Prog dfs' fds' me'
  prg <- St.runStateT (runExceptT m) M.empty
  case fst prg of
    Right a -> return a
    Left a -> err $ show a
  where 

-- | Destination can be a single location var, a tuple of destinations,
-- or nothing (for scalar values)
data Dest = SingleDest LocVar -- TODO: refactor to just be list of locations, or actually enforce invariants of non-empty list, etc
          | TupleDest [Dest]
          | NoDest

mkDest :: [LocVar] -> Dest
mkDest [lv] = SingleDest lv
mkDest [] = NoDest
mkDest lvs = TupleDest $ L.map (mkDest . (\lv -> [lv])) lvs

destFromType :: Ty2 -> TiM Dest
destFromType frt = 
  case frt of
    PackedTy _tc lv -> fixLoc lv >> return (SingleDest lv)
    ProdTy tys -> mapM destFromType tys >>= return . TupleDest
    _ -> return NoDest

destFromType' :: Ty2 -> TiM Dest
destFromType' frt = 
  case frt of
    PackedTy _tc lv -> return (SingleDest lv)
    ProdTy tys -> mapM destFromType tys >>= return . TupleDest
    _ -> return NoDest

freshTyLocs :: Ty2 -> TiM Ty2
freshTyLocs ty =
    case ty of
      PackedTy tc lv -> fresh >>= return . PackedTy tc
      ProdTy tys -> mapM freshTyLocs tys >>= return . ProdTy
      _ -> return ty

fixType_ :: Ty2 -> TiM ()
fixType_ ty =
    case ty of
      PackedTy _tc lv -> fixLoc lv >> return ()
      ProdTy tys -> mapM_ fixType_ tys
      _ -> return ()

-- | Wrap the inferExp procedure, and consume all remaining constraints
inferExp' :: FullEnv -> (L L1.Exp1) -> Dest -> TiM (L L2.Exp2, L2.Ty2)
inferExp' env lex0@(L sl1 exp) dest =
  let lc = L sl1

      -- TODO: These should not be necessary, eventually

      bindAllLocations :: Result -> TiM Result
      bindAllLocations (expr,ty,constrs) = return $ (expr',ty,[])
          where constrs' = L.nub constrs
                expr' = foldr addLetLoc expr constrs'
                addLetLoc i a =
                    case i of
                      AfterConstantL lv1 v lv2 -> lc$ Ext (LetLocE lv1 (AfterConstantLE v lv2) a)
                      AfterVariableL lv1 v lv2 -> lc$ Ext (LetLocE lv1 (AfterVariableLE v lv2) a)
                      StartRegionL lv r -> lc$ Ext (LetLocE lv (StartOfLE r) a)
                      AfterTagL lv1 lv2 -> lc$ Ext (LetLocE lv1 (AfterConstantLE 1 lv2) a)

      -- bindAllStartRegions :: Result -> TiM Result
      -- bindAllStartRegions (expr,ty,constrs) = return $ (expr',ty,[])
      --     where constrs' = L.nub constrs
      --           expr' = foldr addLetLoc expr constrs'
      --           addLetLoc i a =
      --               case i of
      --                 StartRegionL lv r -> lc$ Ext (LetLocE lv (StartOfLE r) a)
      --                 _ -> a

      -- bindAllAfterTags :: Result -> TiM Result
      -- bindAllAfterTags (expr,ty,constrs) = return $ (expr',ty,[])
      --     where constrs' = L.nub constrs
      --           expr' = foldr addLetLoc expr constrs'
      --           addLetLoc i a =
      --               case i of
      --                 AfterTagL lv1 lv2 -> lc$ Ext (LetLocE lv1 (AfterConstantLE 1 lv2) a)
      --                 _ -> a

  in do res <- inferExp env lex0 dest
        let (_,_,rcs) = res
        (e,ty,cs) <- bindAllLocations res
        e' <- finishExp e
        let (e'',_s) = cleanExp e'
        return (e'',ty)
     -- inferExp env lex0 dest >>= bindAllLocations >>= \(a,b,_) -> return (a,b)
                    
-- | We proceed in a destination-passing style given the target region
-- into which we must produce the resulting value.
inferExp :: FullEnv -> (L L1.Exp1) -> Dest -> TiM Result
inferExp env@FullEnv{dataDefs}
         lex0@(L sl1 ex0) dest =
  let lc = L sl1

      -- | Check if there are any StartRegion constraints that can be dischaged here.
      -- The basic logic is that if we know a location `loc` is the start of a region `r`,
      -- and we know that there are no constraints for anything after `loc` left
      -- to be discharged, then we can insert the region binding for `r`.
      tryBindReg :: Result -> TiM Result
      tryBindReg (e,ty,((StartRegionL lv r) : cs)) =
          do lv' <- finalLocVar lv
             (e',ty',cs') <- tryBindReg (e,ty,cs)
             b1 <- noAfterLoc lv' cs' cs'
             if b1 
             then do (e'',ty'',cs'') <- bindTrivialAfterLoc lv' (e',ty',cs')
                     return (l$ Ext (LetRegionE r (l$ Ext (LetLocE lv' (StartOfLE r) e''))), ty'', cs'')
             else return (e',ty',(StartRegionL lv r):cs')
      tryBindReg (e,ty,c:cs) =
          do (e',ty',cs') <- tryBindReg (e,ty,cs)
             return (e',ty',c:cs')
      tryBindReg (e,ty,[]) = return (e,ty,[])

      -- | Check the existing list of constraints to determine if we need to introduce a new
      -- StartRegion constraint based on an existing AfterTag constraint.
      -- The logic here is that if we have an AfterTag constraint on two locations loc1 and loc2,
      -- (ie, loc2 is a data structure and loc1 is its first field), and we know that nothing is
      -- before loc2 and it isn't a fixed location, then it might be the start of a new region.
      -- We can't just bind the region immediately, though, so this function just adds a new
      -- constraint when appropriate, which will be discharged later.
      -- TODO: refactor and merge this function with other logic for region insertion
      tryInRegion :: [Constraint] -> TiM [Constraint]
      tryInRegion cs = tryInRegion' cs cs

      -- Hack, need a full copy of the constraint set in addition to the one being iterated over.
      tryInRegion' :: [Constraint] -> [Constraint] -> TiM [Constraint]
      tryInRegion' fcs (c:cs) =
          case c of
            AfterTagL lv1 lv2 ->
                do lv1' <- finalLocVar lv1
                   lv2' <- finalLocVar lv2
                   b1 <- noBeforeLoc lv2' fcs
                   b2 <- noRegionStart lv2' fcs
                   b3 <- notFixedLoc lv2'
                   if b1 && b2 && b3
                   then do cs' <- tryInRegion' fcs cs
                           r <- lift $ lift $ freshRegVar
                           let c' = StartRegionL lv2' r
                           return (c':c:cs')
                   else do cs' <- tryInRegion' fcs cs
                           return (c:cs')
            _ -> do cs' <- tryInRegion' fcs cs
                    return (c:cs')
      tryInRegion' _ [] = return []

      -- | This function looks at a series of locations and a type, and determines if
      -- any of those locations could be the start of a region. Similar to `tryInRegion`.
      -- A location might be the start of a region if there's nothing before it and
      -- it isn't fixed.
      tryNeedRegion :: [LocVar] -> Ty2 -> [Constraint] -> TiM [Constraint]
      tryNeedRegion (l:ls) ty cs =
          do lv <- finalLocVar l
             vls <- mapM finalLocVar (locsInTy ty)
             if not (lv `L.elem` vls)
             then do b1 <- noBeforeLoc lv cs
                     b2 <- noRegionStart lv cs
                     b3 <- notFixedLoc lv
                     if b1 && b2 && b3
                     then do cs' <- tryNeedRegion ls ty cs
                             r <- lift $ lift $ freshRegVar
                             let c = StartRegionL lv r
                             return (c:cs')
                     else tryNeedRegion ls ty cs
             else tryNeedRegion ls ty cs
      tryNeedRegion [] _ cs = return cs

      -- | This function will transform a result to wrap the sub-expression with any
      -- simple location bindings for locations from the provided list.
      -- For example, if a location `loc1` is known from an AfterTag constraint,
      -- and `[loc1]` is passed in, the `letloc` binding for `loc1` will be wrapped
      -- around the expression in the result.
      bindImmediateDependentLocs :: [LocVar] -> Result -> TiM Result
      bindImmediateDependentLocs (lv:lvs) (bod,ty,cs) =
          do (bod',ty',cs') <- bindImmediateDependentLocs lvs (bod,ty,cs)
             bindImmediateDependentLoc lv (bod',ty',cs')
      bindImmediateDependentLocs [] res = return res

      -- single location variant of above function
      bindImmediateDependentLoc :: LocVar -> Result -> TiM Result
      bindImmediateDependentLoc lv (bod,ty,((AfterTagL lv1 lv2) : cs)) =
          do lv' <- finalLocVar lv
             lv1' <- finalLocVar lv1
             lv2' <- finalLocVar lv2
             if lv' == lv1'
             then do (bod',ty',cs') <- bindImmediateDependentLoc lv (bod,ty,cs)
                     let bod'' = l$ Ext (LetLocE lv1' (AfterConstantLE 1 lv2') bod')
                     return (bod'',ty',cs')
             else do (bod',ty',cs') <- bindImmediateDependentLoc lv (bod,ty,cs)
                     return (bod',ty',(AfterTagL lv1 lv2):cs')
      bindImmediateDependentLoc lv (bod,ty,(c:cs)) =
          do (bod',ty',cs') <- bindImmediateDependentLoc lv (bod,ty,cs)
             return (bod',ty',c:cs')
      bindImmediateDependentLoc lv (bod,ty,[]) = return (bod,ty,[])

      -- | This transforms a result to add location bindings that can be inserted safely
      -- once the variable passed in is in scope.
      -- This is expected to be called on the *whole let expression*, not its body.
      handleTrailingBindLoc :: Var -> Result -> TiM Result
      handleTrailingBindLoc v res =
          do (e,ty,cs) <- bindAfterLoc v res
             case e of
               (L _ (Ext (LetLocE lv1 (AfterVariableLE v lv2) e))) ->
                   do (e',ty',cs') <- bindTrivialAfterLoc lv1 (e,ty,cs)
                      return (l$ Ext (LetLocE lv1 (AfterVariableLE v lv2) e'), ty', cs')
               _ -> return (e,ty,cs) -- Should this signal an error instead of silently returning?

      handleTrailingBindLocs :: [Var] -> Result -> TiM Result
      handleTrailingBindLocs (v:vs) res = handleTrailingBindLoc v res >>= handleTrailingBindLocs vs
      handleTrailingBindLocs _ res = return res

      -- | Transforms a result by adding a location binding derived from an AfterVariable constraint
      -- associated with the passed-in variable.
      bindAfterLoc :: Var -> Result -> TiM Result
      bindAfterLoc v (e,ty,c:cs) =
          case c of
            AfterVariableL lv1 v' lv2 ->
                if v == v'
                then do lv1' <- finalLocVar lv1
                        lv2' <- finalLocVar lv2
                        return (lc$ Ext (LetLocE lv1' (AfterVariableLE v lv2) e), ty, cs)
                else do (e',ty',cs') <- bindAfterLoc v (e,ty,cs)
                        return (e',ty',c:cs')
            _ -> do (e',ty',cs') <- bindAfterLoc v (e,ty,cs)
                    return (e',ty',c:cs')
      bindAfterLoc _ (e,ty,[]) = return (e,ty,[])

      -- | Transform a result by discharging AfterVariable constraints corresponding to
      -- a list of newly bound variables.
      bindAfterLocs :: [Var] -> Result -> TiM Result
      bindAfterLocs (v:vs) res =
          do res' <- bindAfterLoc v res
             bindAfterLocs vs res'
      bindAfterLocs [] res = return res

      -- | Transforms a result by binding any additional locations that are safe to be bound
      -- once the location passed in has been bound. For example, if we know `loc1` is `n`
      -- bytes after `loc2`, and `loc2` has been passed in, we can bind `loc1`. 
      bindTrivialAfterLoc :: LocVar -> Result -> TiM Result
      bindTrivialAfterLoc lv (e,ty,c:cs) =
          case c of
            AfterTagL lv1 lv2 ->
                do lv1' <- finalLocVar lv1
                   lv2' <- finalLocVar lv2
                   lv' <- finalLocVar lv
                   if lv2' == lv'
                   then do (e',ty',cs') <- bindTrivialAfterLoc lv1 (e,ty,cs)
                           return (lc$ Ext (LetLocE lv1' (AfterConstantLE 1 lv2') e'), ty', cs')
                   else do (e',ty',cs') <- bindTrivialAfterLoc lv (e,ty,cs)
                           return (e',ty',c:cs')
            AfterConstantL lv1 v lv2 ->
                do lv1' <- finalLocVar lv1
                   lv2' <- finalLocVar lv2
                   lv' <- finalLocVar lv
                   if lv2' == lv'
                   then do (e',ty',cs') <- bindTrivialAfterLoc lv1 (e,ty,cs)
                           return (lc$ Ext (LetLocE lv1' (AfterConstantLE v lv2') e'), ty', cs')
                   else do (e',ty',cs') <- bindTrivialAfterLoc lv (e,ty,cs)
                           return (e',ty',c:cs')
            _ -> do (e',ty',cs') <- bindTrivialAfterLoc lv (e,ty,cs)
                    return (e',ty',c:cs')
      bindTrivialAfterLoc _ (e,ty,[]) = return (e,ty,[])

      -- | Remove all constraints associated with a list of locations
      removeLocs :: [LocVar] -> [Constraint] -> [Constraint]
      removeLocs ls (c:cs) =
          let lv = case c of
                     AfterTagL lv _ -> lv
                     AfterConstantL lv _ _ -> lv
                     AfterVariableL lv _ _ -> lv
                     StartRegionL lv _ -> lv
          in if L.elem lv ls then removeLocs ls cs else c:(removeLocs ls cs)
      removeLocs ls [] = []

      -- | To handle a case expression, we need to bind locations
      -- appropriately for all the fields.
      doCase :: DDefs Ty2 -> FullEnv -> LocVar -> Dest
             -> (DataCon, [(Var,())],     L L1.Exp1) ->
             TiM ((DataCon, [(Var,LocVar)], L L2.Exp2), Ty2, [Constraint])
      doCase ddfs env src dst (con,vars,rhs) = do
        vars' <- forM vars $ \(v,_) -> do lv <- lift $ lift $ freshLocVar "case"
                                          _ <- fixLoc lv
                                          return (v,lv)
        let contys = lookupDataCon ddfs con
            newtys = L.map (\(ty,(_,lv)) -> fmap (const lv) ty) $ zip contys vars'
            env' = L.foldr (\(v,ty) a -> extendVEnv v ty a) env $ zip (L.map fst vars') newtys
        res <- inferExp env' rhs dst
        (rhs',ty',cs') <- bindAfterLocs (L.map fst vars') res
        -- traceShowM cs'
        -- let cs'' = removeLocs (L.map snd vars') cs'
        -- TODO: check constraints are correct and fail/repair if they're not!!!
        return ((con,vars',rhs'),ty',cs')

  in
  case ex0 of
    L1.VarE v ->
      let e' = lc$ VarE v in
      case dest of
        NoDest -> return (e', lookupVEnv v env, [])
        TupleDest ds -> err $ "TODO: handle tuple of destinations for VarE"
        SingleDest d  -> do
                  let ty  = lookupVEnv v env
                  loc <- case ty of
                           PackedTy _ lv -> return lv
                           -- TODO: refactor this so we never try to put a non-packed type
                           -- in a location
                           _ -> lift $ lift $ freshLocVar "imm"
                  let ty' = case ty of
                              PackedTy k lv -> PackedTy k d
                              t -> t
                  unify d loc
                            (return (e',ty',[]))
                            (copy (e',ty,[]) d)

    L1.MkProdE ls ->
      case dest of
        NoDest -> err $ "Expected destination(s) for expression"
        SingleDest d -> case ls of
                          [e] -> do (e',ty,les) <- inferExp env e dest
                                    return (lc$ MkProdE [e'], ty, les)
                          _ -> err $ "Cannot match single destination to tuple"
        TupleDest ds -> do results <- mapM (\(e,d) -> inferExp env e d) $ zip ls ds
                           return (lc$ MkProdE ([a | (a,_,_) <- results]),
                                     ProdTy ([b | (_,b,_) <- results]),
                                     concat $ [c | (_,_,c) <- results])
          
    L1.LitE n -> return (lc$ LitE n, IntTy, [])

    L1.LitSymE s -> return (lc$ LitSymE s, SymTy, [])

    L1.AppE f ls arg ->
        do let arrty = lookupFEnv f env
           valTy <- freshTyLocs $ arrOut arrty
           argTy <- freshTyLocs $ arrIn arrty
           argDest <- destFromType' argTy
           (arg',aty,acs) <- inferExp env arg argDest
           return (lc$ L2.AppE f (locsInTy aty ++ locsInTy valTy) arg', valTy, acs)

    L1.TimeIt e t b ->
        do (e',ty',cs') <- inferExp env e dest
           return (lc$ TimeIt e' ty' b, ty', cs')

    L1.DataConE () k ls ->
      case dest of
        NoDest -> err $ "Expected single location destination for DataConE"
        TupleDest _ds -> err $ "Expected single location destination for DataConE"
        SingleDest d -> do
                  locs <- sequence $ replicate (length ls) fresh
                  ls' <- mapM (\(e,lv) -> (inferExp env e $ SingleDest lv)) $ zip ls locs
                  newLocs <- mapM finalLocVar locs                  
                  let afterVar :: (Maybe (L Exp2), Maybe LocVar, Maybe LocVar) -> Maybe Constraint
                      afterVar ((Just (L _ (VarE v))), (Just loc1), (Just loc2)) =
                          Just $ AfterVariableL loc1 v loc2
                      afterVar ((Just (L _ (LitE _))), (Just loc1), (Just loc2)) =
                          Just $ AfterConstantL loc1 8 loc2
                      afterVar _ = Nothing
                      constrs = concat $ [c | (_,_,c) <- ls']
                      constrs' = if null locs
                                 then constrs
                                 else let tmpconstrs = [AfterTagL (L.head locs) d] ++
                                                       (mapMaybe afterVar $ zip3
                                                         -- ((map Just $ L.tail ([a | (a,_,_) <- ls' ])) ++ [Nothing])
                                                        (map Just ([a | (a,_,_) <- ls']))
                                                         -- (map Just locs)
                                                        ((map Just $ L.tail locs) ++ [Nothing])
                                                        (map Just locs))
                                                         -- ((map Just $ L.tail locs) ++ [Nothing])) ++
                                      in tmpconstrs ++ constrs
                  -- traceShow k $ traceShow locs $
                  return (lc$ DataConE d k [ e' | (e',_,_)  <- ls'],
                            PackedTy (getTyOfDataCon dataDefs k) d,
                            constrs')
    
    L1.IfE a b c@(L _ ce) -> do
       -- Here we blithely assume BoolTy because L1 typechecking has already passed:
       (a',bty,acs) <- inferExp env a NoDest
       assumeEq bty BoolTy
       -- Here BOTH branches are unified into the destination, so
       -- there is no need to unify with eachother.
       (b',tyb,csb)    <- inferExp env b dest
       (c',tyc,csc)    <- inferExp env c dest
       return (lc$ IfE a' b' c', tyc, L.nub $ acs ++ csb ++ csc)

    L1.PrimAppE pr es -> 
      case dest of
        SingleDest _ -> err "Cannot unify primop with destination" 
        TupleDest _ -> err "Cannot unify primop with destination" 
        NoDest -> do results <- mapM (\e -> inferExp env e NoDest) es
                     -- Assume arguments to PrimAppE are trivial
                     -- so there's no need to deal with constraints or locations
                     ty <- lift $ lift $ convertTy $ L1.primRetTy pr
                     return (lc$ PrimAppE (prim pr) [a | (a,_,_) <- results], ty, [])

    L1.CaseE ex ls -> do 
      -- Case expressions introduce fresh destinations for the scrutinee:
      loc <- lift $ lift $ freshLocVar "scrut"
      (ex',ty2,cs) <- inferExp env ex (SingleDest loc)
      let src = locOfTy ty2
      pairs <- mapM (doCase dataDefs env src dest) ls
      return (lc$ CaseE ex' ([a | (a,_,_) <- pairs]),
              (\(_,b,_)->b) (L.head pairs),
              (concat $ [c | (_,_,c) <- pairs]))

    L1.LetE (vr,locs,bty,L sl2 rhs) bod | [] <- locs ->
      case rhs of
        L1.AppE f [] arg -> do
          let arrty = lookupFEnv f env
          valTy <- freshTyLocs $ arrOut arrty
          argTy <- freshTyLocs $ arrIn arrty -- TODO: check for and fail on invalid arguments
          argDest <- destFromType' argTy
          (arg',aty,acs) <- inferExp env arg argDest
          res <- inferExp (extendVEnv vr valTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr res
          vcs <- tryNeedRegion (locsInTy valTy) ty'' $ acs ++ cs''
          fcs <- tryInRegion vcs
          -- fcs <- tryInRegion $ acs ++ cs''
          res <- tryBindReg (lc$ L2.LetE (vr,[], valTy, L sl2 $ L2.AppE f (locsInTy aty ++ locsInTy valTy) arg') bod'', ty'', fcs)
          bindImmediateDependentLocs (locsInTy aty ++ locsInTy valTy) res

        L1.LetE{} -> err $ "Expected let spine, encountered nested lets: " ++ (show lex0)
        L1.LitE i -> do
          (bod',ty',cs') <- inferExp (extendVEnv vr IntTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],IntTy,L sl2 $ L2.LitE i) bod'', ty'', fcs)
                     
        PrimAppE p ls -> do
          lsrec <- mapM (\e -> inferExp env e NoDest) ls
          ty <- lift $ lift $ convertTy bty
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          let ls' = L.map (\(a,_,_)->a) lsrec
              cs'' = concat $ [c | (_,_,c) <- lsrec]
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs' ++ cs'')
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[],ty,L sl2 $ L2.PrimAppE (prim p) ls') bod'',
                    ty'', fcs)
        DataConE _loc k ls  -> do
          loc <- lift $ lift $ freshLocVar "datacon"
          (rhs',rty,rcs) <- inferExp env (L sl2 $ DataConE () k ls) $ SingleDest loc
          (bod',ty',cs') <- inferExp (extendVEnv vr (PackedTy (getTyOfDataCon dataDefs k) loc) env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs' ++ rcs)
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],PackedTy (getTyOfDataCon dataDefs k) loc,rhs') bod'',
                    ty', fcs)
        LitSymE x     -> do
          (bod',ty',cs') <- inferExp (extendVEnv vr IntTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],IntTy,L sl2 $ L2.LitSymE x) bod'', ty'', fcs)
        ProjE i e     -> do
          (e,ProdTy tys,cs) <- inferExp env e NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr (tys !! i) env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs ++ cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],ProdTy tys,L sl2 $ L2.ProjE i e) bod'',
                             ty'', fcs)
        CaseE ex ls    -> do
          loc <- lift $ lift $ freshLocVar "scrut"
          (ex',ty2,cs) <- inferExp env ex (SingleDest loc)
          let src = locOfTy ty2
          rhsTy <- lift $ lift $ convertTy bty
          caseDest <- destFromType' rhsTy
          pairs <- mapM (doCase dataDefs env src caseDest) ls
          (bod',ty',cs') <- inferExp (extendVEnv vr rhsTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,locsInTy rhsTy,rhsTy, L sl2 $ L2.CaseE ex' ([a | (a,_,_) <- pairs])) bod'',
                        ty'', L.nub $ cs ++ fcs)
        MkProdE ls    -> _mkprod
        TimeIt e t b       -> do
          lv <- lift $ lift $ freshLocVar "timeit"
          let subdest = case bty of
                          PackedTy _ _ -> SingleDest lv
                          _ -> NoDest
          (e',ty,cs) <- inferExp env e subdest
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs ++ cs')
          vcs <- tryNeedRegion (locsInTy ty) ty'' cs''
          fcs <- tryInRegion vcs
          tryBindReg (lc$ L2.LetE (vr,[],ty,L sl2 $ TimeIt e' ty b) bod'',
                    ty'', fcs)
          
        _oth -> err $ "Unhandled case in lhs of let: " ++ (show lex0)

    _oth -> err $ "Unhandled case: " ++ (show lex0)



-- TODO: Should eventually allow src and dest regions to be the same
-- for in-place updates packed data with linear types.
  
-- | Transforms an expression by updating all locations to their final mapping
-- as a result of unification.
finishExp :: L Exp2 -> TiM (L Exp2)
finishExp (L i e) =
    let l e = L i e
    in
    case e of
      VarE v -> return $ l$ VarE v
      LitE i -> return $ l$ LitE i
      LitSymE v -> return $ l$ LitSymE v
      AppE v ls e1 -> do
             e1' <- finishExp e1
             ls' <- mapM finalLocVar ls
             return $ l$ AppE v ls' e1'
      PrimAppE pr es -> do
             es' <- mapM finishExp es
             return $ l$ PrimAppE pr es'
      LetE (v,ls,t,e1) e2 -> do
             e1' <- finishExp e1
             e2' <- finishExp e2
             ls' <- mapM finalLocVar ls
             t' <- case t of
               PackedTy tc lv ->
                   do lv' <- finalLocVar lv
                      return $ PackedTy tc lv'
               _ -> return t
             return $ l$ LetE (v,ls',t',e1') e2'
      IfE e1 e2 e3 -> do
             e1' <- finishExp e1
             e2' <- finishExp e2
             e3' <- finishExp e3
             return $ l$ IfE e1' e2' e3'
      MkProdE es -> do
             es' <- mapM finishExp es
             return $ l$ MkProdE es'
      ProjE i e1 -> do
             e1' <- finishExp e1
             return $ l$ ProjE i e1'
      CaseE e1 prs -> do
             e1' <- finishExp e1
             prs' <- forM prs $ \(dc, lvs, e2) -> do
                         e2' <- finishExp e2
                         lvs' <- forM lvs $ \(v,lv) -> do
                                                    lv' <- finalLocVar lv
                                                    return (v,lv')
                         return (dc,lvs',e2')
             return $ l$ CaseE e1' prs'
      DataConE lv dc es -> do
             es' <- mapM finishExp es
             lv' <- finalLocVar lv
             return $ l$ DataConE lv' dc es'
      TimeIt e1 t b -> do
             e1' <- finishExp e1
             t' <- case t of
                     PackedTy tc lv ->
                         do lv' <- finalLocVar lv
                            return $ PackedTy tc lv'
                     _ -> return t
             return $ l$ TimeIt e1' t' b
      Ext (LetRegionE r e1) -> do
             e1' <- finishExp e1
             return $ l$ Ext (LetRegionE r e1')
      Ext (LetLocE loc lex e1) -> do
             e1' <- finishExp e1
             loc' <- finalLocVar loc
             lex' <- case lex of
                       AfterConstantLE i lv -> do
                                    lv' <- finalLocVar lv
                                    return $ AfterConstantLE i lv'
                       AfterVariableLE v lv -> do
                                    lv' <- finalLocVar lv
                                    return $ AfterVariableLE v lv'
                       oth -> return oth
             return $ l$ Ext (LetLocE loc' lex' e1')
      _ -> err $ "Unhandled case in finishExp: " ++ (show e)

-- | Remove unused location bindings
-- Returns pair of (new exp, set of free locations)
-- TODO: avoid generating location bindings for immediate values
cleanExp :: L Exp2 -> (L Exp2, S.Set LocVar)
cleanExp (L i e) =
    let l e = L i e
    in
    case e of
      VarE v -> (l$ VarE v, S.empty)
      LitE v -> (l$ LitE v, S.empty)
      LitSymE v -> (l$ LitSymE v, S.empty)
      AppE v ls e -> let (e',s') = cleanExp e
                     in (l$ AppE v ls e', S.union s' (S.fromList ls))
      PrimAppE pr es -> let (es',ls') = unzip $ L.map cleanExp es
                        in (l$ PrimAppE pr es', S.unions ls')
      LetE (v,ls,t,e1) e2 -> let (e1', s1') = cleanExp e1
                                 (e2', s2') = cleanExp e2
                             in (l$ LetE (v,ls,t,e1') e2', S.unions [s1',s2',S.fromList ls])
      IfE e1 e2 e3 -> let (e1',s1') = cleanExp e1
                          (e2',s2') = cleanExp e2
                          (e3',s3') = cleanExp e3
                      in (l$ IfE e1' e2' e3', S.unions [s1',s2',s3'])
      MkProdE es -> let (es',ls') = unzip $ L.map cleanExp es
                    in (l$ MkProdE es', S.unions ls')
      ProjE i e -> let (e',s') = cleanExp e
                   in (l$ ProjE i e', s')
      CaseE e1 prs -> let (e1',s1') = cleanExp e1
                          (prs', ls2') = unzip $ L.map
                                         (\(dc,lvs,e2) -> let (e2', s2) = cleanExp e2
                                                          in ((dc,lvs,e2'), s2)) prs
                      in (l$ CaseE e1' prs', S.union s1' $ S.unions ls2')
      DataConE lv dc es -> let (es',ls') = unzip $ L.map cleanExp es
                           in (l$ DataConE lv dc es', S.union (S.singleton lv) $ S.unions ls')
      TimeIt e d b -> let (e',s') = cleanExp e
                      in (l$ TimeIt e' d b, s')
      Ext (LetRegionE r e) -> let (e',s') = cleanExp e
                              in (l$ Ext (LetRegionE r e'), s')
      Ext (LetLocE loc lex e) -> let (e',s') = cleanExp e
                                 in if S.member loc s'
                                    then let ls = case lex of
                                                    AfterConstantLE _i lv -> [lv]
                                                    AfterVariableLE _v lv -> [lv]
                                                    oth -> []
                                         in (l$ Ext (LetLocE loc lex e'),
                                              S.delete loc $ S.union s' $ S.fromList ls)
                                    else (e',s')
      _ -> err $ "Unhandled case in cleanExp: " ++ (show e)
                                      
                           
-- | Check if a location is contained in a type.
-- This includes locations afterward in a data structure.
containsLoc :: LocVar -> L2.Ty2 -> [Constraint] -> TiM Bool
containsLoc lv1 ty cs =
    case ty of
      PackedTy _ lv2 ->
          do lv1' <- finalLocVar lv1
             lv2' <- finalLocVar lv2
             if lv1' == lv2'
             then return True
             else do lvs <- associatedLocs lv2 cs
                     return $ elem lv1' lvs
      _ -> return False

-- | Return a list of all locations known to be after a particular
-- location.
associatedLocs :: LocVar -> [Constraint] -> TiM [LocVar]
associatedLocs lv (c:cs) =
    do lv' <- finalLocVar lv
       lvs <- associatedLocs lv cs
       case c of
         AfterConstantL lv1 _v lv2 ->
             do lv1' <- finalLocVar lv1
                lv2' <- finalLocVar lv2   
                if lv' == lv2'
                then do lvs' <- associatedLocs lv1' cs
                        return $ L.nub $ lv1' : (lvs ++ lvs')
                else return lvs
         AfterVariableL lv1 _v lv2 ->
             do lv1' <- finalLocVar lv1
                lv2' <- finalLocVar lv2   
                if lv' == lv2'
                then do lvs' <- associatedLocs lv1' cs
                        return $ L.nub $ lv1' : (lvs ++ lvs')
                else return lvs
         _ -> return lvs
associatedLocs lv [] = return []

-- | Checks that there are no constraints specifying a location
-- after the location passed in.
-- TODO: refactor to only take one list of constraints.
noAfterLoc :: LocVar -> [Constraint] -> [Constraint] -> TiM Bool
noAfterLoc lv fcs (c:cs) =
    case c of
      AfterVariableL lv1 v lv2 ->
          do lv2' <- finalLocVar lv2
             lv' <- finalLocVar lv
             if lv' == lv2' then return False else noAfterLoc lv fcs cs
      AfterTagL lv1 lv2 ->
          do lv2' <- finalLocVar lv2
             lv' <- finalLocVar lv
             if lv' == lv2'
             then do b1 <- noAfterLoc lv fcs cs
                     b2 <- noAfterLoc lv1 fcs fcs
                     return (b1 && b2)
             else noAfterLoc lv fcs cs
      AfterConstantL lv1 v lv2 -> 
          do lv2' <- finalLocVar lv2
             lv' <- finalLocVar lv
             if lv' == lv2' then return False else noAfterLoc lv fcs cs
      _ -> noAfterLoc lv fcs cs
noAfterLoc _ _ [] = return True

noBeforeLoc :: LocVar -> [Constraint] -> TiM Bool
noBeforeLoc lv (c:cs) =
    case c of
      AfterVariableL lv1 v lv2 ->
          do lv1' <- finalLocVar lv1
             lv' <- finalLocVar lv
             if lv' == lv1' then return False else noBeforeLoc lv cs
      AfterConstantL lv1 v lv2 ->
          do lv1' <- finalLocVar lv1
             lv' <- finalLocVar lv
             if lv' == lv1' then return False else noBeforeLoc lv cs
      AfterTagL lv1 lv2 ->
          do lv1' <- finalLocVar lv1
             lv' <- finalLocVar lv
             if lv' == lv1' then return False else noBeforeLoc lv cs      
      _ -> noBeforeLoc lv cs
noBeforeLoc lv [] = return True

noRegionStart :: LocVar -> [Constraint] -> TiM Bool
noRegionStart lv (c:cs) =
    case c of
      StartRegionL lv r -> return False
      _ -> noRegionStart lv cs
noRegionStart lv [] = return True

-- | Unify is a conditional form that takes a "success branch" and
-- "failure branch".  In the case of failure, it makes no change to
-- the store.  In the case of success, the new equalities are placed
-- in the store /before/ executing the success branch.
unify :: LocVar -> LocVar -> TiM a -> TiM a -> TiM a
unify v1 v2 success fail = do
  ut1 <- lookupUnifyLoc v1
  ut2 <- lookupUnifyLoc v2
  case (ut1,ut2) of
    (FixedLoc l1, FixedLoc l2) ->
        if l1 == l2 then success else fail
    (FreshLoc l1, FixedLoc l2) ->
        do assocLoc l1 (FixedLoc l2)
           success
    (FixedLoc l2, FreshLoc l1) -> 
        do assocLoc l1 (FixedLoc l2)
           success
    (FreshLoc l1, FreshLoc l2) ->
        do assocLoc l1 (FreshLoc l2)
           success

freshLocVar :: String -> SyM LocVar
freshLocVar m = gensym (toVar m)

freshRegVar :: SyM Region
freshRegVar = do rv <- gensym (toVar "r")
                 return $ VarR rv

finalUnifyLoc :: LocVar -> TiM UnifyLoc
finalUnifyLoc v = do
  m <- lift $ St.get
  case M.lookup v m of
    Nothing -> return (FreshLoc v)
    Just (FixedLoc v') -> return (FixedLoc v')
    Just (FreshLoc v') -> finalUnifyLoc v'

notFixedLoc :: LocVar -> TiM Bool
notFixedLoc lv = do
  uv <- finalUnifyLoc lv
  case uv of
    FixedLoc _ -> return False
    _ -> return True

regionNotInType :: Region -> Ty2 -> [Constraint] -> TiM Bool
regionNotInType r ty cs =
    case ty of
      PackedTy _ lv -> do
              r' <- regionOfLocVar lv cs
              return $ (Just r) == r'
      _ -> return True

-- TODO: Fix this!! It should return the correct region for *any location*
-- not just the first location in a region.
regionOfLocVar :: LocVar -> [Constraint] -> TiM (Maybe Region)
regionOfLocVar lv1 ((StartRegionL lv2 r) : cs) =
    if lv1 == lv2 then return (Just r) else regionOfLocVar lv1 cs
regionOfLocVar lv1 (_ : cs) = regionOfLocVar lv1 cs
regionOfLocVar _ [] = return Nothing
         
finalLocVar :: LocVar -> TiM LocVar
finalLocVar v = do
  u <- finalUnifyLoc v
  case u of
    FixedLoc v' -> return v'
    FreshLoc v' -> return v'

fresh :: TiM LocVar
fresh = do
  lift $ lift $ freshLocVar "loc"

freshUnifyLoc :: TiM UnifyLoc
freshUnifyLoc = do
  lv <- fresh
  return $ FreshLoc lv

lookupUnifyLoc :: LocVar -> TiM UnifyLoc
lookupUnifyLoc lv = do
  m <- lift $ St.get
  case M.lookup lv m of
    Nothing -> do
      l' <- fresh
      lift $ St.put $ M.insert lv (FreshLoc l') m
      return $ FreshLoc l'
    Just (FreshLoc l') -> finalUnifyLoc l'
    Just (FixedLoc l') -> return $ FixedLoc l'

fixLoc :: LocVar -> TiM UnifyLoc
fixLoc lv = do 
  -- l' <- fresh
  m <- lift $ St.get
  lift $ St.put $ M.insert lv (FixedLoc lv) m
  return $ FixedLoc lv

assocLoc :: LocVar -> UnifyLoc -> TiM ()
assocLoc lv ul = do
  m <- lift $ St.get
  lift $ St.put $ M.insert lv ul m

-- | The copy repair tactic:
copy :: Result -> LocVar -> TiM Result
copy (e,ty,cs) lv1 =
    case ty of
      PackedTy tc lv2 ->
          let copyName = "copy_" ++ tc -- assume a copy function with this name
              eapp = l$ AppE (toVar copyName) [lv1,lv2] e
          in return (eapp, PackedTy tc lv1, [])
      _ -> err $ "Did not expect to need to copy non-packed type: " ++ show ty

-- | For a packed type, get its location.
locOfTy :: Ty2 -> LocVar
locOfTy (PackedTy _ lv) = lv
locOfTy ty2 = err $ "Expected packed type, got "++show ty2 
       
err :: String -> a
err m = error $ "InferLocations: " ++ m

assumeEq :: (Eq a, Show a) => a -> a -> TiM ()
assumeEq a1 a2 =
    if a1 == a2
    then return ()
    else err $ "Expected these to be equal: " ++ (show a1) ++ ", " ++ (show a2)

-- | Convert a prim from L1 to L2
prim :: L1.Prim L1.Ty1 -> L1.Prim Ty2
prim p = case p of
           L1.AddP -> L1.AddP
           L1.SubP -> L1.SubP
           L1.MulP -> L1.MulP
           L1.DivP -> L1.DivP
           L1.ModP -> L1.ModP
           L1.EqSymP -> L1.EqSymP
           L1.EqIntP -> L1.EqIntP
           L1.MkTrue -> L1.MkTrue
           L1.MkFalse -> L1.MkFalse
           L1.SizeParam -> L1.SizeParam
           _ -> err $ "Can't handle this primop yet in InferLocations:\n"++show p

-- | Generate a copy function for a particular data definition.
-- Note: there will be redundant let bindings in the function body which may need to be inlined.
genCopyFn :: DDef L1.Ty1 -> SyM (L1.FunDef L1.Ty1 (L L1.Exp1))
genCopyFn DDef{tyName, dataCons} = do
  arg <- gensym $ "arg"
  casebod <- forM dataCons $ \(dcon, tys) ->
             do xs <- mapM (\_ -> gensym "x") tys
                ys <- mapM (\_ -> gensym "y") tys
                let bod = foldr (\(ty,x,y) acc ->
                                     if L1.isPackedTy ty
                                     then l$ LetE (y, [], ty, l$ AppE (toVar $ "copy_" ++ (tyToDataCon ty)) [] (l$ VarE x)) acc
                                     else l$ LetE (y, [], ty, l$ VarE x) acc)
                          (l$ L1.DataConE () dcon $ map (l . VarE) ys)
                          (zip3 (L.map snd tys) xs ys)
                return (dcon, L.map (\x -> (x,())) xs, bod)
  return $ L1.FunDef { funName = toVar $ "copy_" ++ (fromVar tyName)
                     , funArg = (arg, L1.PackedTy (fromVar tyName) ())
                     , funRetTy = L1.PackedTy (fromVar tyName) ()
                     , funBody = l$ L1.CaseE (l$ L1.VarE arg) casebod
                     }

-- | Get the data constructor type from a type, failing if it's not packed
tyToDataCon :: L1.Ty1 -> DataCon
tyToDataCon (PackedTy dcon _) = dcon
tyToDataCon oth = error $ "tyToDataCon: " ++ show oth ++ " is not packed"

-- | Add copy functions for each data type in a prog
addCopyFns :: L1.Prog -> SyM L1.Prog
addCopyFns (L1.Prog dfs fds me) = do
  newFns <- mapM genCopyFn dfs
  prg <- flattenL1 $ L1.Prog dfs (fds `M.union` (M.mapKeys (toVar . ("copy_" ++) . fromVar) newFns)) me
  return $ inlineTriv $ prg

               
emptyEnv :: FullEnv
emptyEnv = FullEnv { dataDefs = C.emptyDD
                   , valEnv   = M.empty
                   , funEnv   = M.empty }


t0 :: ArrowTy Ty2
t0 = fst$ runSyM 0 $
     convertFunTy (snd (L1.funArg fd), L1.funRetTy fd)
   where fd = L1.fundefs L1.add1Prog M.! "add1"
           
tester1 :: L L1.Exp1 -> L Exp2
tester1 e = case fst $ fst $ runSyM 0 $ St.runStateT (runExceptT (inferExp emptyEnv e NoDest)) M.empty of
              Right a -> (\(a,_,_)->a) a
              Left a -> err $ show a

t1 :: L Exp2
t1 = tester1 (l$ LitE 3)

--  id  :: Tree -> Tree
--  id' :: forall l1 in r1, l2 in r2 . Tree l1 -> Tree l2

t2 :: L Exp2
t2 = tester1 $
     l$ LetE ("x",[],IntTy,l$ LitE 1) $
     l$ LetE ("y",[],IntTy,l$ LitE 2) $
     l$ LetE ("z",[],IntTy,l$ PrimAppE L1.AddP [l$ VarE "x", l$ VarE "y"]) $
     l$ VarE "z"

ddtree :: DDefs Ty2
ddtree = fromListDD [DDef (toVar "Tree")
                      [ ("Leaf",[(False,IntTy)])
                      , ("Node",[ (False,PackedTy "Tree" "l")
                                , (False,PackedTy "Tree" "l")])
                      ]]

treeEnv :: FullEnv
treeEnv = FullEnv { dataDefs = ddtree
                  , valEnv   = M.empty
                  , funEnv   = M.empty }


tester2 :: L L1.Exp1 -> L Exp2
tester2 e = case fst $ fst $ runSyM 0 $ St.runStateT (runExceptT (inferExp' treeEnv e NoDest)) M.empty of
              Right a -> fst a
              Left a -> err $ show a

t3 :: L Exp2
t3 = tester2 $
     l$ LetE ("x",[],IntTy,l$ LitE 1) $
     l$ LetE ("y",[],IntTy,l$ LitE 2) $
     l$ LetE ("z",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x", l$ VarE "y"]) $
     l$ LitE 0

t4 :: L Exp2
t4 = tester2 $
     l$ LetE ("x1",[],IntTy,l$ LitE 1) $
     l$ LetE ("y1",[],IntTy,l$ LitE 2) $
     l$ LetE ("z1",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x1", l$ VarE "y1"]) $
     l$ LetE ("x2",[],IntTy,l$ LitE 3) $
     l$ LetE ("y2",[],IntTy,l$ LitE 4) $
     l$ LetE ("z2",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x2", l$ VarE "y2"]) $
     l$ LitE 0

t5 :: L Exp2
t5 = tester2 $
     l$ LetE ("x1",[],IntTy,l$ LitE 1) $
     l$ LetE ("y1",[],IntTy,l$ LitE 2) $
     l$ LetE ("z1",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x1", l$ VarE "y1"]) $
     l$ LetE ("x2",[],IntTy,l$ LitE 3) $
     l$ LetE ("y2",[],IntTy,l$ LitE 4) $
     l$ LetE ("z2",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x2", l$ VarE "y2"]) $
     l$ LetE ("z3",[],PackedTy "Tree" (), l$ DataConE () "Node" [l$ VarE "z1", l$ VarE "z2"]) $
     l$ LitE 0

t6 :: L Exp2
t6 = tester2 $
     l$ LetE ("x1",[],IntTy,l$ LitE 1) $
     l$ LetE ("y1",[],IntTy,l$ LitE 2) $
     l$ LetE ("z1",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x1", l$ VarE "y1"]) $
     l$ LetE ("x2",[],IntTy,l$ LitE 3) $
     l$ LetE ("y2",[],IntTy,l$ LitE 4) $
     l$ LetE ("z2",[],PackedTy "Tree" (), l$ DataConE () "Leaf" [l$ VarE "x2", l$ VarE "y2"]) $
     l$ LetE ("z3",[],PackedTy "Tree" (), l$ DataConE () "Node" [l$ VarE "z1", l$ VarE "z2"]) $
     l$ CaseE (l$ VarE "z3") [("Leaf", [("x",())], l$ VarE "x"),
                              ("Node", [("x",()),("y",())], l$ LitE 1)]


exadd1Bod :: L L1.Exp1
exadd1Bod = l$
    CaseE (l$ VarE "tr") $
      [ ("Leaf", [("n",())],
         l$ LetE ("leaf1",[],L1.Packed "Tree", l$ PrimAppE L1.AddP [l$ VarE "n", l$ LitE 1])
           (l$ DataConE () "Leaf"
             [l$ VarE "leaf1"]))
      , ("Node", [("x",()),("y",())],
         l$ LetE ("node1",[],L1.Packed "Tree", (l$ AppE "add1" [] (l$ VarE "x")))
          (l$ LetE ("node2",[],L1.Packed "Tree", (l$ AppE "add1" [] (l$ VarE "y")))
           (l$ DataConE () "Node"
                [ l$ VarE "node1"
                , l$ VarE "node2"])))
      ]

treeTy :: L1.Ty1
treeTy = L1.Packed "Tree"

treeDD :: DDefs (UrTy ())
treeDD = (fromListDD [L1.DDef "Tree"
                      [ ("Leaf",[(False,IntTy)])
                      , ("Node",[(False,L1.Packed "Tree")
                                ,(False,L1.Packed "Tree")])]])

mkAdd1Prog :: L L1.Exp1 -> Maybe (L L1.Exp1) -> L1.Prog
mkAdd1Prog bod mainExp = L1.Prog treeDD
                                 (M.fromList [("add1",mkAdd1Fun bod)])
                                 mainExp

mkAdd1Fun :: ex -> L1.FunDef L1.Ty1 ex
mkAdd1Fun bod = L1.FunDef "add1" ("tr",treeTy) treeTy bod

exadd1 :: L1.Prog
exadd1 = mkAdd1Prog exadd1Bod Nothing

mkIdProg :: Maybe (L L1.Exp1) -> L1.Prog
mkIdProg mainExp = L1.Prog treeDD
                           (M.fromList [("id",idFun)])
                           mainExp

idFun :: L1.FunDef L1.Ty1 (L L1.Exp1)
idFun = L1.FunDef "id" ("tr",treeTy) treeTy (l$ VarE "tr")
