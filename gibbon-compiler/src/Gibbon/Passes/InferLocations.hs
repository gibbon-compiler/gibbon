{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

-- | Convert from L1 to L2, adding region constructs.

module Gibbon.Passes.InferLocations
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
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Foldable as F
import Data.Maybe
import qualified Control.Monad.Trans.State.Strict as St
import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans (lift)
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L1.Syntax as L1 hiding (extendVEnv, extendsVEnv, lookupVEnv, lookupFEnv)
import Gibbon.L2.Syntax as L2 hiding (extendVEnv, extendsVEnv, lookupVEnv, lookupFEnv)
import Gibbon.Passes.InlineTriv (inlineTriv)
import Gibbon.Passes.Flatten (flattenL1)

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | Combine the different kinds of contextual information in-scope.
data FullEnv = FullEnv
    { dataDefs :: DDefs Ty2 -- ^ Data type definitions
    , valEnv :: TyEnv Ty2   -- ^ Type env for local bindings
    , funEnv :: TyEnv (ArrowTy Ty2)  -- ^ Top level fundef types
    } deriving Show

extendVEnv :: Var -> Ty2 -> FullEnv -> FullEnv
extendVEnv v ty fe@FullEnv{valEnv} = fe { valEnv = M.insert v ty valEnv }

extendsVEnv :: TyEnv Ty2 -> FullEnv -> FullEnv
extendsVEnv env fe@FullEnv{valEnv} = fe { valEnv = valEnv <> env }

lookupVEnv :: Var -> FullEnv -> Ty2
lookupVEnv v FullEnv{valEnv} = valEnv # v

lookupFEnv :: Var -> FullEnv -> ArrowTy2
lookupFEnv v FullEnv{funEnv} = funEnv # v

-- Types
--------------------------------------------------------------------------------

-- | This helper exemplifies the simplicity of our current approach.
-- If we assume output regions are disjoint from input ones, then we
-- can instantiate an L1 function type into a polymorphic L2 one,
-- mechanically.
convertFunTy :: ([Ty1],Ty1) -> PassM ArrowTy2
convertFunTy (from,to) = do
    from' <- mapM convertTy from
    to'   <- convertTy to
    -- For this simple version, we assume every location is in a separate region:
    lrm1 <- concat <$> mapM (toLRM Input) from'
    lrm2 <- toLRM Output to'
    return $ ArrowTy2 { locVars = lrm1 ++ lrm2
                     , arrIns  = from'
                     , arrEffs = S.empty
                     , arrOut  = to'
                     , locRets = [] }
 where
   toLRM md ls =
       mapM (\v -> do r <- freshLocVar "r"
                      return $ LRM v (VarR r) md)
            (F.toList ls)

convertTy :: Ty1 -> PassM Ty2
convertTy ty = traverse (const (freshLocVar "loc")) ty

convertDDefs :: DDefs Ty1 -> PassM (DDefs Ty2)
convertDDefs ddefs = traverse f ddefs
    where f (DDef tyargs n dcs) = do
            dcs' <- forM dcs $ \(dc,bnds) -> do
                             bnds' <- forM bnds $ \(isb,ty) -> do
                                               ty' <- convertTy ty
                                               return (isb, ty')
                             return (dc,bnds')
            return $ DDef tyargs n dcs'

-- Inference algorithm
--------------------------------------------------------------------------------

-- | The location inference monad is a stack of ExceptT and StateT.
type TiM a = ExceptT Failure (St.StateT InferState PassM) a

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
             | FailInfer Exp1
               deriving (Show, Eq)

---------------------------------------

-- | Constraints here mean almost the same thing as they do in the L2 type checker.
-- One difference is the presence of an AfterTag constraint, though I'm not opposed to
-- adding one to the L2 language for symmetry.
data Constraint = AfterConstantL LocVar Int LocVar
                | AfterVariableL LocVar Var LocVar
                | AfterTagL LocVar LocVar
                | StartRegionL LocVar Region
                | AfterCopyL LocVar Var Var LocVar Var [LocVar]
                | FreeL LocVar
                  deriving (Show, Eq, Generic)

instance Out Constraint

-- | The result type for this pass.  Return a new expression and its
-- type, which includes/implies its location.
type Result = (L Exp2, Ty2, [Constraint])

data DCArg = ArgFixed Int
           | ArgVar Var
           | ArgCopy Var Var Var [LocVar]

inferLocs :: Prog1 -> PassM L2.Prog2
inferLocs initPrg = do
  (Prog dfs fds me) <- addRepairFns initPrg
  let m = do
          dfs' <- lift $ lift $ convertDDefs dfs
          fenv <- forM fds $ \(FunDef _ _ (intys, outty) _) ->
                  lift $ lift $ convertFunTy (intys,outty)
          let fe = FullEnv dfs' M.empty fenv
          me' <- case me of
            -- We ignore the type of the main expression inferred in L1..
            -- Probably should add a small check here
            Just (me,_ty) -> do
              (me',ty') <- inferExp' fe me [] NoDest
              return $ Just (me',ty')
            Nothing -> return Nothing
          fds' <- forM fds $ \(FunDef fn fa (intty,outty) fbod) -> do
                                   let arrty = lookupFEnv fn fe
                                       fe' = extendsVEnv (M.fromList $ fragileZip fa (arrIns arrty)) fe
                                       boundLocs = concat $ map locsInTy (arrIns arrty ++ [arrOut arrty])
                                   dest <- destFromType (arrOut arrty)
                                   mapM_ fixType_ (arrIns arrty)
                                   (fbod',_) <- inferExp' fe' fbod boundLocs dest
                                   return $ FunDef fn fa arrty fbod'
          return $ Prog dfs' fds' me'
  prg <- St.runStateT (runExceptT m) M.empty
  case fst prg of
    Right a -> return a
    Left a -> err $ show a

-- | Destination can be a single location var, a tuple of destinations,
-- or nothing (for scalar values)
data Dest = SingleDest LocVar -- TODO: refactor to just be list of locations, or actually enforce invariants of non-empty list, etc
          | TupleDest [Dest]
          | NoDest
            deriving (Show, Generic)

instance Out Dest

locsInDest :: Dest -> [LocVar]
locsInDest d = case d of
                 SingleDest c -> [c]
                 TupleDest ls -> L.concatMap locsInDest ls
                 NoDest -> []

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
    ProdTy tys -> mapM destFromType' tys >>= return . TupleDest
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
inferExp' :: FullEnv -> (L Exp1) -> [LocVar] -> Dest -> TiM (L L2.Exp2, L2.Ty2)
inferExp' env lex0@(L sl1 exp) bound dest =
  let lc = L sl1

      -- TODO: These should not be necessary, eventually

      bindAllUnbound :: L L2.Exp2 -> [LocVar] -> TiM (L L2.Exp2)
      bindAllUnbound e (lv:ls) = do
        r <- lift $ lift $ freshRegVar
        e' <- bindAllUnbound e ls
        return $ lc$ Ext (LetRegionE r (lc$ Ext (LetLocE lv (StartOfLE r) e')))
      bindAllUnbound e _ = return e

      bindAllLocations :: Result -> TiM Result
      bindAllLocations (expr,ty,constrs) = return $ (expr',ty,[])
          where constrs' = L.nub $ constrs
                expr' = foldr addLetLoc expr constrs'
                addLetLoc i a =
                    case i of
                      AfterConstantL lv1 v lv2 -> lc$ Ext (LetLocE lv1 (AfterConstantLE v lv2) a)
                      AfterVariableL lv1 v lv2 -> lc$ Ext (LetLocE lv1 (AfterVariableLE v lv2) a)
                      StartRegionL lv r -> lc$ Ext (LetRegionE r (lc $ Ext (LetLocE lv (StartOfLE r) a)))
                      AfterTagL lv1 lv2 -> lc$ Ext (LetLocE lv1 (AfterConstantLE 1 lv2) a)
                      FreeL lv -> lc$ Ext (LetLocE lv FreeLE a)
                      AfterCopyL lv1 v1 v' lv2 f lvs ->
                        let arrty = arrOut $ lookupFEnv f env
                            -- Substitute the location occurring at the call site
                            -- in place of the one in the function's return type
                            copyRetTy = case arrty of
                                          PackedTy _ loc -> substLoc (M.singleton loc lv2) arrty
                                          _ -> error "bindAllLocations: Not a packed type"
                            a' = subst v1 (lc$ VarE v') a
                        in lc$ LetE (v',[],copyRetTy, lc$ AppE f lvs [lc$ VarE v1]) $
                           lc$ Ext (LetLocE lv1 (AfterVariableLE v' lv2) a')

  in do res <- inferExp env lex0 dest
        (e,ty,cs) <- bindAllLocations res
        e' <- finishExp e
        let (e'',s) = cleanExp e'
            unbound = (s S.\\ S.fromList bound)
        e''' <- bindAllUnbound e'' (S.toList unbound)
        -- dbgTrace 4 (show (s S.\\ S.fromList bound)) $ return ()
        return (e''',ty)

-- | We proceed in a destination-passing style given the target region
-- into which we must produce the resulting value.
inferExp :: FullEnv -> (L Exp1) -> Dest -> TiM Result
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
            AfterCopyL lv1 v1 v' lv2 f lvs ->
                if v == v1
                then do lv1' <- finalLocVar lv1
                        lv2' <- finalLocVar lv2
                        let arrty = lookupFEnv f env
                            -- Substitute the location occurring at the call site
                            -- in place of the one in the function's return type
                            copyRetTy = case arrOut arrty of
                                          PackedTy _ loc -> substLoc (M.singleton loc lv2) (arrOut arrty)
                                          _ -> error "bindAfterLoc: Not a packed type"
                        _ <- dbgTraceIt (show v' ++ " " ++ show v1) $ return ()
                        return (lc$ LetE (v',[],copyRetTy,l$ AppE f lvs [l$ VarE v1]) $
                                lc$ Ext (LetLocE lv1' (AfterVariableLE v' lv2') e), ty, cs)
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

      -- | To handle a case expression, we need to bind locations
      -- appropriately for all the fields.
      doCase :: DDefs Ty2 -> FullEnv -> LocVar -> Dest
             -> (DataCon, [(Var,())],     L Exp1) ->
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
        -- let cs'' = removeLocs (L.map snd vars') cs'
        -- TODO: check constraints are correct and fail/repair if they're not!!!
        return ((con,vars',rhs'),ty',cs')


  in
  case ex0 of
    VarE v ->
      let e' = lc$ VarE v in
      case dest of
        NoDest -> return (e', lookupVEnv v env, [])
        TupleDest ds ->
           let ProdTy tys = lookupVEnv v env
           in unifyAll ds tys
              (return (e', ProdTy tys, []))
              (err$ "TODO: support copying parts of tuples")
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

    ProjE i (L p (VarE v)) ->
        let ProdTy tys = lookupVEnv v env
            ty = tys !! i
            e' = ProjE i (L p (VarE v))
        in case dest of
             NoDest -> return (lc$ e', ty, [])
             TupleDest ds -> err $ "TODO: handle tuple of destinations for ProjE"
             SingleDest d -> do
                  loc <- case ty of
                           PackedTy _ lv -> return lv
                           _ -> lift $ lift $ freshLocVar "imm"
                  let ty' = case ty of
                              PackedTy k lv -> PackedTy k d
                              t -> t
                  unify d loc
                            (return (l$ e',ty',[]))
                            (copy (l$ e',ty,[]) d)

    ProjE{} -> err$ "Invalid tuple projection: " ++ (show ex0)

    MkProdE ls ->
      case dest of
        NoDest -> do results <- mapM (\e -> inferExp env e NoDest) ls
                     let pty = case results of
                                 [(_,ty,_)] -> ty
                                 _ -> ProdTy ([b | (_,b,_) <- results])
                     return (lc$ MkProdE ([a | (a,_,_) <- results]), pty,
                               concat $ [c | (_,_,c) <- results])
        SingleDest d -> case ls of
                          [e] -> do (e',ty,les) <- inferExp env e dest
                                    return (lc$ MkProdE [e'], ty, les)
                          _ -> err $ "Cannot match single destination to tuple"
        TupleDest ds -> do results <- mapM (\(e,d) -> inferExp env e d) $ zip ls ds
                           return (lc$ MkProdE ([a | (a,_,_) <- results]),
                                     ProdTy ([b | (_,b,_) <- results]),
                                     concat $ [c | (_,_,c) <- results])

    -- Location inference for the parallel combinator should work exactly like a regular tuple --
    -- except that the result should be a `ParE` instead of a `MkProdE`.
    -- ParE a b -> do
    --   (L lc1 (MkProdE [a',b']), ty, cs) <- inferExp env (l$ MkProdE [a,b]) dest
    --   return (L lc1 (ParE a' b'), ty, cs)
    ParE{} -> error "inferLocations: TODO ParE"

    LitE n -> return (lc$ LitE n, IntTy, [])

    LitSymE s -> return (lc$ LitSymE s, SymTy, [])

    AppE f _ args ->
        do let arrty = lookupFEnv f env
           valTy    <- freshTyLocs $ arrOut arrty
           -- /cc @vollmerm
           argTys   <- mapM freshTyLocs $ arrIns arrty
           argDests <- mapM destFromType' argTys
           (args', atys, acss) <- L.unzip3 <$> mapM (uncurry $ inferExp env) (zip args argDests)
           let acs = concat acss
           case dest of
             SingleDest d -> do
               case locsInTy valTy of
                 [outloc] -> unify d outloc
                               (return (lc$ L2.AppE f (concatMap locsInTy atys ++ locsInDest dest) args', valTy, acs))
                               (err$ "(AppE) Cannot unify" ++ sdoc d ++ " and " ++ sdoc outloc)
                 _ -> err$ "AppE expected a single output location in type: " ++ sdoc valTy
             TupleDest ds ->
               case valTy of
                 ProdTy tys -> unifyAll ds tys
                                 (return (lc$ L2.AppE f (concatMap locsInTy atys ++ locsInDest dest) args', valTy, acs))
                                 (err$ "(AppE) Cannot unify" ++ sdoc ds ++ " and " ++ sdoc tys)
                 _ -> err$ "(AppE) Cannot unify" ++ sdoc dest ++ " and " ++ sdoc valTy
             NoDest ->
               case locsInTy valTy of
                 [] -> return (lc$ L2.AppE f (concatMap locsInTy atys ++ locsInDest dest) args', valTy, acs)
                 _  -> err$ "(AppE) Cannot unify NoDest with " ++ sdoc valTy ++ ". This might be caused by a main expression having a packed type."

    TimeIt e t b ->
        do (e',ty',cs') <- inferExp env e dest
           return (lc$ TimeIt e' ty' b, ty', cs')

    WithArenaE v e ->
        do (e',ty',cs') <- inferExp (extendVEnv v ArenaTy env) e dest
           return (lc$ WithArenaE v e', ty', cs')

    DataConE () k [] -> do
        case dest of
          NoDest -> err $ "Expected single location destination for DataConE"
          TupleDest _ds -> err $ "Expected single location destination for DataConE"
          SingleDest d ->
              do fakeLoc <- fresh
                 let constrs = [AfterTagL fakeLoc d]
                 return (lc$ DataConE d k [], PackedTy (getTyOfDataCon dataDefs k) d, constrs)

    DataConE () k ls ->
      case dest of
        NoDest -> do
          -- CSK: Should this really be an error ?
          loc <- lift $ lift $ freshLocVar "datacon"
          (e',ty,cs) <- inferExp env (l$ DataConE () k ls) (SingleDest loc)
          fcs <- tryInRegion cs
          tryBindReg (e', ty, fcs)
        TupleDest _ds -> err $ "Expected single location destination for DataConE"
        SingleDest d -> do
                  locs <- sequence $ replicate (length ls) fresh
                  mapM_ fixLoc locs -- Don't allow argument locations to freely unify
                  ls' <- mapM (\(e,lv) -> (inferExp env e $ SingleDest lv)) $ zip ls locs
                  -- let ls'' = L.map unNestLet ls'
                  --     bnds = catMaybes $ L.map pullBnds ls'
                  --     env' = addCopyVarToEnv ls' env
                  -- Arguments are either a fixed size or a variable
                  -- TODO: audit this!
                  argLs <- forM [a | (a,_,_) <- ls'] $ \arg ->
                           case arg of
                             L _ (VarE v) -> case lookupVEnv v env of
                                               CursorTy -> return $ ArgFixed 8
                                               IntTy -> return $ ArgFixed (fromJust $ sizeOfTy IntTy)
                                               SymTy -> return $ ArgFixed (fromJust $ sizeOfTy SymTy)
                                               BoolTy -> return $ ArgFixed (fromJust $ sizeOfTy BoolTy)
                                               _ -> return $ ArgVar v
                             L _ (LitE _) -> return $ ArgFixed (fromJust $ sizeOfTy IntTy)
                             L _ (LitSymE _) -> return $ ArgFixed (fromJust $ sizeOfTy SymTy)
                             L _ (PrimAppE MkTrue []) -> return $ ArgFixed (fromJust $ sizeOfTy BoolTy)
                             L _ (PrimAppE MkFalse []) -> return $ ArgFixed (fromJust $ sizeOfTy BoolTy)
                             L _ (AppE f lvs [L _ (VarE v)]) -> do v' <- lift $ lift $ freshLocVar "cpy"
                                                                   return $ ArgCopy v v' f lvs
                             _ -> err $ "Expected argument to be trivial, got " ++ (show arg)
                  newLocs <- mapM finalLocVar locs
                  let afterVar :: (DCArg, Maybe LocVar, Maybe LocVar) -> Maybe Constraint
                      afterVar ((ArgVar v), (Just loc1), (Just loc2)) =
                          Just $ AfterVariableL loc1 v loc2
                      afterVar ((ArgFixed s), (Just loc1), (Just loc2)) =
                          Just $ AfterConstantL loc1 s loc2
                      afterVar ((ArgCopy v v' f lvs), (Just loc1), (Just loc2)) =
                          Just $ AfterCopyL loc1 v v' loc2 f lvs
                      afterVar _ = Nothing
                      constrs = concat $ [c | (_,_,c) <- ls']
                      constrs' = if null locs
                                 then constrs
                                 else let tmpconstrs = [AfterTagL (L.head locs) d] ++
                                                       (mapMaybe afterVar $ zip3
                                                         -- ((map Just $ L.tail ([a | (a,_,_) <- ls' ])) ++ [Nothing])
                                                        argLs
                                                         -- (map Just locs)
                                                        ((map Just $ L.tail locs) ++ [Nothing])
                                                        (map Just locs))
                                                         -- ((map Just $ L.tail locs) ++ [Nothing])) ++
                                      in tmpconstrs ++ constrs
                  -- traceShow k $ traceShow locs $
                  --let newe = buildLets bnds $ lc$ DataConE d k [ e' | (e',_,_)  <- ls'']
                  ls'' <- forM (zip argLs ls') $ \(arg,(e,ty,cs)) -> do
                            case e of
                              L i (AppE _ _ _) -> case arg of
                                                    ArgCopy _ v' _ _ -> return (l$ VarE v',ty,cs)
                                                    _ -> undefined
                              _ -> return (e,ty,cs)
                  -- bod <- return $ lc$ DataConE d k [ e' | (e',_,_)  <- ls'']
                  bod <- if (length ls) > 0 && (isCpyCall $ last [e | (e,_,_) <- ls'])
                         then case last [e | (e,_,_) <- ls'] of
                                L i (AppE f lvs e) ->
                                    let (ArgCopy _ v' _ copy_locs) = last argLs
                                        arrty = arrOut $ lookupFEnv f env
                                        -- Substitute the location occurring at the call site
                                        -- in place of the one in the function's return type
                                        -- re:last because we want the output location.
                                        copyRetTy = case arrty of
                                          PackedTy _ loc -> substLoc (M.singleton loc (last copy_locs)) arrty
                                          _ -> error "inferExp: Not a packed type"
                                    in return $ lc$ LetE (v',[],copyRetTy, lc$ AppE f lvs e) $
                                       lc$ DataConE d k [ e' | (e',_,_) <- ls'']
                                _ -> error "inferExp: Unexpected pattern <error1>"
                         else return $ lc$ DataConE d k [ e' | (e',_,_)  <- ls'']
                  return (bod, PackedTy (getTyOfDataCon dataDefs k) d, constrs')

    IfE a b c@(L _ ce) -> do
       -- Here we blithely assume BoolTy because L1 typechecking has already passed:
       (a',bty,acs) <- inferExp env a NoDest
       assumeEq bty BoolTy
       -- Here BOTH branches are unified into the destination, so
       -- there is no need to unify with eachother.
       (b',tyb,csb)    <- inferExp env b dest
       (c',tyc,csc)    <- inferExp env c dest
       return (lc$ IfE a' b' c', tyc, L.nub $ acs ++ csb ++ csc)

    PrimAppE (DictInsertP dty) [L sl (VarE var),d,k,v] ->
      case dest of
        SingleDest _ -> err "Cannot unify DictInsert with destination"
        TupleDest _ -> err "Cannot unify DictInsert with destination"
        NoDest -> do (d',SymDictTy ar dty',_dcs) <- inferExp env d NoDest
                     (k',_,_kcs) <- inferExp env k NoDest
                     dty'' <- lift $ lift $ convertTy dty
                     r <- lift $ lift $ freshRegVar
                     loc <- lift $ lift $ freshLocVar "ins"
                     -- _ <- fixLoc loc
                     (v',vty,vcs) <- inferExp env v $ SingleDest loc
                     let cs = vcs -- (StartRegionL loc r) : vcs
                     dummyDty <- dummyTyLocs dty'
                     return (lc$ PrimAppE (DictInsertP dummyDty) [L sl (VarE var),d',k',v'], SymDictTy (Just var) $ stripTyLocs dty'', cs)

    PrimAppE (DictLookupP dty) [d,k] ->
      case dest of
        SingleDest loc -> do (d',SymDictTy _ _dty,_dcs) <- inferExp env d NoDest
                             (k',_,_kcs) <- inferExp env k NoDest
                             dty' <- lift $ lift $ convertTy dty
                             let loc' = locOfTy dty'
                             _ <- fixLoc loc'
                             let e' = lc$ PrimAppE (DictLookupP dty') [d',k']
                                 cs = [FreeL loc']
                             unify loc loc'
                                   (return (e',dty',cs))
                                   (copy (e',dty',cs) loc)
        TupleDest _ -> err "Cannot unify DictLookup with tuple destination"
        NoDest -> err "Cannot unify DictLookup with no destination"

    PrimAppE (DictEmptyP dty) [L sl (VarE var)] ->
      case dest of
        SingleDest _ -> err "Cannot unify DictEmpty with destination"
        TupleDest _ -> err "Cannot unify DictEmpty with destination"
        NoDest -> do dty' <- lift $ lift $ convertTy dty
                     return (lc$ PrimAppE (DictEmptyP dty') [L sl (VarE var)], SymDictTy (Just var) $ stripTyLocs dty', [])

    PrimAppE (DictHasKeyP dty) [d,k] ->
      case dest of
        SingleDest _ -> err "Cannot unify DictEmpty with destination"
        TupleDest _ -> err "Cannot unify DictEmpty with destination"
        NoDest -> do (d',SymDictTy _ dty',_dcs) <- inferExp env d NoDest
                     (k',_,_kcs) <- inferExp env k NoDest
                     dummyDty <- dummyTyLocs dty'
                     return (lc$ PrimAppE (DictHasKeyP dummyDty) [d',k'], BoolTy, [])

    PrimAppE pr es ->
      case dest of
        SingleDest d -> err $ "Cannot unify primop " ++ sdoc pr ++ " with destination " ++ sdoc d ++ " at " ++ show sl1
        TupleDest  d -> err $ "Cannot unify primop " ++ sdoc pr ++ " with destination " ++ sdoc d ++ " at " ++ show sl1
        NoDest -> do results <- mapM (\e -> inferExp env e NoDest) es
                     -- Assume arguments to PrimAppE are trivial
                     -- so there's no need to deal with constraints or locations
                     ty <- lift $ lift $ convertTy $ primRetTy pr
                     pr' <- lift $ lift $ prim pr
                     return (lc$ PrimAppE pr' [a | (a,_,_) <- results], ty, [])

    CaseE ex ls -> do
      -- Case expressions introduce fresh destinations for the scrutinee:
      loc <- lift $ lift $ freshLocVar "scrut"
      (ex',ty2,cs) <- inferExp env ex (SingleDest loc)
      let src = locOfTy ty2
      pairs <- mapM (doCase dataDefs env src dest) ls
      return (lc$ CaseE ex' ([a | (a,_,_) <- pairs]),
              (\(_,b,_)->b) (L.head pairs),
              (concat $ [c | (_,_,c) <- pairs]))

    LetE (vr,locs,bty,L sl2 rhs) bod | [] <- locs ->
      case rhs of
        VarE{} -> err$ "Unexpected variable aliasing: " ++ (show ex0)

        AppE f [] args -> do
          let arrty = lookupFEnv f env
          valTy <- freshTyLocs $ arrOut arrty
          -- /cc @vollmerm
          argTys   <- mapM freshTyLocs $ arrIns arrty
          argDests <- mapM destFromType' argTys
          (args', atys, acss) <- L.unzip3 <$> mapM (uncurry $ inferExp env) (zip args argDests)
          let acs = concat acss
          tupBod <- projTups valTy (l$ VarE vr) bod
          res <- inferExp (extendVEnv vr valTy env) tupBod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr res
          vcs <- tryNeedRegion (locsInTy valTy) ty'' $ acs ++ cs''
          fcs <- tryInRegion vcs
          -- fcs <- tryInRegion $ acs ++ cs''
          res' <- tryBindReg (lc$ L2.LetE (vr,[], valTy, L sl2 $ L2.AppE f (concatMap locsInTy atys ++ locsInTy valTy) args') bod'', ty'', fcs)
          bindImmediateDependentLocs (concatMap locsInTy atys ++ locsInTy valTy) res'

        AppE{} -> err$ "Malformed function application: " ++ (show ex0)

        -- IfE{} -> err$ "Unexpected conditional in let binding: " ++ (show ex0)

        IfE a b c -> do
          (boda,tya,csa) <- inferExp env a NoDest
           -- just assuming tyb == tyc
          (bodb,tyb,csb) <- inferExp env b NoDest
          (bodc,tyc,csc) <- inferExp env c NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr tyc env) bod dest
          let cs = L.nub $ csa ++ csb ++ csc ++ cs'
          return (lc$ L2.LetE (vr,[],tyc,L sl2 $ L2.IfE boda bodb bodc) bod', ty', cs)

        LetE{} -> err $ "Expected let spine, encountered nested lets: " ++ (show lex0)

        LitE i -> do
          (bod',ty',cs') <- inferExp (extendVEnv vr IntTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],IntTy,L sl2 $ L2.LitE i) bod'', ty'', fcs)

        -- TODO: docs
        PrimAppE (ReadPackedFile fp tycon _ ty) [] -> do
          r <- lift $ lift $ gensym "r"
          loc <- lift $ lift $ freshLocVar "mmap_file"
          let rhs' = l$ PrimAppE (ReadPackedFile fp tycon (Just r) (PackedTy tycon loc)) []
          (bod',ty',cs') <- inferExp (extendVEnv vr (PackedTy tycon loc) env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs'
          tryBindReg ( (l$ Ext$ LetRegionE (MMapR r) $ l$ Ext $ LetLocE loc (StartOfLE (MMapR r)) $
                        l$ L2.LetE (vr,[],PackedTy tycon loc,rhs') bod'')
                     , ty', fcs)

        -- Don't process the EndOf operation at all, just recur through it
        PrimAppE RequestEndOf [L la (VarE v)] -> do
          (bod',ty',cs') <- inferExp (extendVEnv vr CursorTy env) bod dest
          return (lc$ L2.LetE (vr,[],CursorTy,L sl2 $ L2.PrimAppE RequestEndOf [L la (L2.VarE v)]) bod', ty', cs')

        PrimAppE (DictInsertP dty) ls -> do
          (e,ty,cs) <- inferExp env (L sl2 $ PrimAppE (DictInsertP dty) ls) NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod',ty', L.nub $ cs' ++ cs)
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[],ty,e) bod'', ty'', fcs)

        PrimAppE (DictLookupP dty) ls -> do
          loc <- lift $ lift $ freshLocVar "dict"
          (e,ty,cs) <- inferExp env (L sl2 $ PrimAppE (DictLookupP dty) ls) $ SingleDest loc
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs ++ cs')
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[],ty,e) bod'',ty'', fcs)

        PrimAppE (DictEmptyP dty) ls -> do
          (e,ty,cs) <- inferExp env (L sl2 $ PrimAppE (DictEmptyP dty) ls) NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod',ty',L.nub $ cs' ++ cs)
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[],ty,e) bod'', ty'', fcs)

        PrimAppE (DictHasKeyP dty) ls -> do
          (e,ty,cs) <- inferExp env (L sl2 $ PrimAppE (DictHasKeyP dty) ls) NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod',ty',L.nub $ cs' ++ cs)
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[],ty,e) bod'', ty'', fcs)

        PrimAppE p ls -> do
          lsrec <- mapM (\e -> inferExp env e NoDest) ls
          ty <- lift $ lift $ convertTy bty
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          let ls' = [a | (a,_,_) <- lsrec]
              cs'' = concat $ [c | (_,_,c) <- lsrec]
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs' ++ cs'')
          fcs <- tryInRegion cs'''
          p' <- lift $ lift $ prim p
          tryBindReg (lc$ L2.LetE (vr,[],ty,L sl2 $ L2.PrimAppE p' ls') bod'',
                    ty'', fcs)

        DataConE _loc k ls  -> do
          loc <- lift $ lift $ freshLocVar "datacon"
          (rhs',rty,rcs) <- inferExp env (L sl2 $ DataConE () k ls) $ SingleDest loc
          (bod',ty',cs') <- inferExp (extendVEnv vr (PackedTy (getTyOfDataCon dataDefs k) loc) env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs' ++ rcs)
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],PackedTy (getTyOfDataCon dataDefs k) loc,rhs') bod'',
                    ty', fcs)

        LitSymE x       -> do
          (bod',ty',cs') <- inferExp (extendVEnv vr IntTy env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],IntTy,L sl2 $ L2.LitSymE x) bod'', ty'', fcs)

        ProjE i arg     -> do
          (e,ProdTy tys,cs) <- inferExp env arg NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr (tys !! i) env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs ++ cs')
          fcs <- tryInRegion cs''
          tryBindReg (lc$ L2.LetE (vr,[],tys !! i,L sl2 $ L2.ProjE i e) bod'',
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
          let ccs  = L.nub $ cs ++ fcs ++ (concat $ [c | (_,_,c) <- pairs])
              cexp = L sl2 $ L2.CaseE ex' ([a | (a,_,_) <- pairs])
          tryBindReg (lc$ L2.LetE (vr,locsInTy rhsTy,rhsTy, cexp) bod'',
                        ty'', ccs)

        MkProdE ls    -> do
          lsrec <- mapM (\e -> inferExp env e NoDest) ls
          ty <- lift $ lift $ convertTy bty
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          let als = [a | (a,_,_) <- lsrec]
              acs = concat $ [c | (_,_,c) <- lsrec]
              aty = [b | (_,b,_) <- lsrec]
          (bod'',ty'',cs''') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs' ++ acs)
          fcs <- tryInRegion cs'''
          tryBindReg (lc$ L2.LetE (vr,[], ProdTy aty, L sl2 $ L2.MkProdE als) bod'', ty'', fcs)

        -- Location inference for the parallel combinator should work exactly like a regular tuple --
        -- except that the result should be a `ParE` instead of a `MkProdE`.
        -- ParE a b -> do
        --    res <- inferExp env (l$ LetE (vr,locs,bty, l$ MkProdE [a,b]) bod) dest
        --    case res of
        --      (L lc1 (LetE (vr',locs', ty', L lc2 (MkProdE [a',b'])) bod), ty'', cs'') ->
        --        return (L lc1 (LetE (vr',locs', ty', L lc2 (ParE a' b')) bod), ty'', cs'')
        --      _  -> err$ "ParE -- unexpected result: " ++ sdoc res
        ParE{} -> error "inferLocations: TODO ParE"

        WithArenaE v e -> do
          (e',ty,cs) <- inferExp (extendVEnv v ArenaTy env) e NoDest
          (bod',ty',cs') <- inferExp (extendVEnv vr ty env) bod dest
          (bod'',ty'',cs'') <- handleTrailingBindLoc vr (bod', ty', L.nub $ cs ++ cs')
          vcs <- tryNeedRegion (locsInTy ty) ty'' cs''
          fcs <- tryInRegion vcs
          tryBindReg (lc$ L2.LetE (vr,[],ty,L sl2 $ WithArenaE v e') bod'',
                        ty'', fcs)

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

        MapE{} -> err$ "MapE unsupported"
        FoldE{} -> err$ "FoldE unsupported"

        -- Ext (AddCursor cur i) -> do
        --   (bod',ty',cs') <- inferExp env bod dest
        --   tryBindReg (lc$ Ext $ LetLocE vr (AfterConstantLE i cur) bod', ty', cs')

    LetE{} -> err$ "Malformed let expression: " ++ (show ex0)
    MapE{} -> err$ "MapE unsupported"
    FoldE{} -> err$ "FoldE unsupported"
    Ext{} -> err$ "Not expecting an Ext here: " ++ sdoc ex0


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
      AppE v ls es -> do
             es' <- mapM finishExp es
             ls' <- mapM finalLocVar ls
             return $ l$ AppE v ls' es'
      PrimAppE pr es -> do
             es' <- mapM finishExp es
             pr' <- finishPr pr
             return $ l$ PrimAppE pr' es'
      LetE (v,ls,t,e1) e2 -> do
             e1' <- finishExp e1
             e2' <- finishExp e2
             ls' <- mapM finalLocVar ls
             t' <- finishTy t
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

      -- ParE a b -> do
      --     a' <- finishExp a
      --     b' <- finishExp b
      --     return (l$ ParE a' b')
      ParE{} -> error "finishExp: TODO ParE"

      WithArenaE v e -> do
             e' <- finishExp e
             return $ l$ WithArenaE v e'

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
      Ext{} -> err$ "Unexpected Ext: " ++ (show e)
      MapE{} -> err$ "MapE not supported"
      FoldE{} -> err$ "FoldE not supported"

finishTy :: Ty2 -> TiM Ty2
finishTy t =
    case t of
      PackedTy tc lv ->
          do lv' <- finalLocVar lv
             return $ PackedTy tc lv'
      ProdTy pls ->
           do pls' <- mapM finishTy pls
              return $ ProdTy pls'
      _ -> return t

finishPr :: Prim Ty2 -> TiM (Prim Ty2)
finishPr pr =
    case pr of
      DictInsertP bty -> finishTy bty >>= return . DictInsertP
      DictLookupP bty -> finishTy bty >>= return . DictLookupP
      DictEmptyP bty  -> finishTy bty >>= return . DictEmptyP
      DictHasKeyP bty -> finishTy bty >>= return . DictHasKeyP
      _ -> return pr

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
      AppE v ls e -> let (e',s') = unzip $ map cleanExp e
                     in (l$ AppE v ls e', (S.unions s') `S.union` (S.fromList ls))
      PrimAppE (DictInsertP ty) es -> let (es',ls') = unzip $ L.map cleanExp es
                        in (l$ PrimAppE (DictInsertP ty) es',
                             S.union (S.unions ls') (S.fromList $ locsInTy ty))
      PrimAppE (DictLookupP ty) es -> let (es',ls') = unzip $ L.map cleanExp es
                        in (l$ PrimAppE (DictLookupP ty) es',
                             S.union (S.unions ls') (S.fromList $ locsInTy ty))
      PrimAppE (DictEmptyP ty) es -> let (es',ls') = unzip $ L.map cleanExp es
                        in (l$ PrimAppE (DictEmptyP ty) es',
                             S.union (S.unions ls') (S.fromList $ locsInTy ty))
      PrimAppE (DictHasKeyP ty) es -> let (es',ls') = unzip $ L.map cleanExp es
                        in (l$ PrimAppE (DictHasKeyP ty) es',
                             S.union (S.unions ls') (S.fromList $ locsInTy ty))
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
                                                          in ((dc,lvs,e2'), s2 S.\\ S.fromList (map snd lvs))) prs
                      in (l$ CaseE e1' prs', S.union s1' $ S.unions ls2')
      DataConE lv dc es -> let (es',ls') = unzip $ L.map cleanExp es
                           in (l$ DataConE lv dc es', S.union (S.singleton lv) $ S.unions ls')
      TimeIt e d b -> let (e',s') = cleanExp e
                      in (l$ TimeIt e' d b, s')

      -- ParE a b -> let (a', s1) = cleanExp a
      --                 (b', s2) = cleanExp b
      --             in (l$ ParE a' b', s1 `S.union` s2)
      ParE{} -> error "cleanExp: TODO ParE"

      WithArenaE v e -> let (e',s) = cleanExp e
                        in (l$ WithArenaE v e', s)

      Ext (LetRegionE r e) -> let (e',s') = cleanExp e
                              in (l$ Ext (LetRegionE r e'), s')
      Ext (LetLocE loc FreeLE e) -> let (e', s') = cleanExp e
                                    in if S.member loc s'
                                       then (l$ Ext (LetLocE loc FreeLE e'), S.delete loc s')
                                       else (e',s')
      Ext (LetLocE loc lex e) -> let (e',s') = cleanExp e
                                 in if S.member loc s'
                                    then let ls = case lex of
                                                    AfterConstantLE _i lv -> [lv]
                                                    AfterVariableLE _v lv -> [lv]
                                                    oth -> []
                                         in (l$ Ext (LetLocE loc lex e'),
                                              S.delete loc $ S.union s' $ S.fromList ls)
                                    else (e',s')
      Ext{} -> err$ "Unexpected Ext: " ++ (show e)
      MapE{} -> err$ "MapE not supported"
      FoldE{} -> err$ "FoldE not supported"

projTups :: Ty2 -> L Exp1 -> L Exp1 -> TiM (L Exp1)
projTups t proj e =
    case t of
      ProdTy ts -> foldM (\e (t,i) ->
                   case t of
                     ProdTy ts ->
                          do v <- lift $ lift $ gensym (toVar "proj")
                             e' <- projTups t (l$ ProjE i proj) e
                             let ty = stripTyLocs $ ProdTy ts
                             return $ l$ LetE (v,[],ty,l$ ProjE i proj) e'
                     PackedTy tc lv ->
                          do v <- lift $ lift $ gensym (toVar "proj")
                             let ty = stripTyLocs $ PackedTy tc lv
                             return $ l$ LetE (v,[],ty,l$ ProjE i proj) $ fixProj M.empty v (l$ ProjE i proj) e
                     _ -> return e) e $ zip ts [0..]
      _ -> return e

fixProj :: M.Map Var Var -> Var -> L Exp1 -> L Exp1 -> L Exp1
fixProj renam pvar proj (L i e) =
    let l e = L i e
        eEq (L _ e1) (L _ e2) = e1 == e2
    in
    case e of
      VarE v -> case M.lookup v renam of
                  Nothing -> l$ VarE v
                  Just v' -> l$ VarE v'
      LitE v -> l$ LitE v
      LitSymE v -> l$ LitSymE v
      AppE v ls es -> let es' = map (fixProj renam pvar proj) es
                      in l$ AppE v ls es'
      PrimAppE pr es -> let es' = map (fixProj renam pvar proj) es
                        in l$ PrimAppE pr es'
      LetE (v,ls,t,e1) e2 ->
          if e1 `eEq` proj
          then fixProj (M.insert v pvar renam) pvar proj e2
          else let e1' = fixProj renam pvar proj e1
                   e2' = fixProj renam pvar proj e2
               in l$ LetE (v,ls,t,e1') e2'
      IfE e1 e2 e3 -> let e1' = fixProj renam pvar proj e1
                          e2' = fixProj renam pvar proj e2
                          e3' = fixProj renam pvar proj e3
                      in l$ IfE e1' e2' e3'
      MkProdE es -> let es' = map (fixProj renam pvar proj) es
                    in l$ MkProdE es'
      ProjE i e1 -> if (l e) `eEq` proj then l$ VarE pvar else
                        let e1' = fixProj renam pvar proj e1
                        in l$ ProjE i e1'
      CaseE e1 prs -> let e1' = fixProj renam pvar proj e1
                          prs' = map (\(dc,lvs,e2) ->
                                          (dc,lvs,fixProj renam pvar proj e2)) prs
                      in l$ CaseE e1' prs'
      DataConE lv dc es -> let es' = map (fixProj renam pvar proj) es
                           in l$ DataConE lv dc es'
      TimeIt e1 d b -> let e1' = fixProj renam pvar proj e1
                       in l$ TimeIt e1' d b
      -- ParE e1 e2 -> let e1' = fixProj renam pvar proj e1
      --                   e2' = fixProj renam pvar proj e2
      --               in l$ ParE e1' e2'
      ParE{} -> error "fixProj: TODO ParE"
      WithArenaE v e -> l$ WithArenaE v $ fixProj renam pvar proj e
      Ext{} -> err$ "Unexpected Ext: " ++ (show e)
      MapE{} -> err$ "MapE not supported"
      FoldE{} -> err$ "FoldE not supported"


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
             then return False
                 -- do b1 <- noAfterLoc lv fcs cs
                 --    b2 <- noAfterLoc lv1 fcs fcs
                 --    return (b1 && b2)
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
      StartRegionL lv2 _r -> ((lv /= lv2) &&) <$> noRegionStart lv cs
      _ -> noRegionStart lv cs
noRegionStart lv [] = return True

-- | Unify is a conditional form that takes a "success branch" and
-- "failure branch".  In the case of failure, it makes no change to
-- the store.  In the case of success, the new equalities are placed
-- in the store /before/ executing the success branch.
unify :: LocVar -> LocVar -> TiM a -> TiM a -> TiM a
unify v1 v2 successA failA = do
  ut1 <- lookupUnifyLoc v1
  ut2 <- lookupUnifyLoc v2
  case (ut1,ut2) of
    (FixedLoc l1, FixedLoc l2) ->
        if l1 == l2 then successA else failA
    (FreshLoc l1, FixedLoc l2) ->
        do assocLoc l1 (FixedLoc l2)
           successA
    (FixedLoc l2, FreshLoc l1) ->
        do assocLoc l1 (FixedLoc l2)
           successA
    (FreshLoc l1, FreshLoc l2) ->
        do assocLoc l1 (FreshLoc l2)
           successA

unifyAll :: [Dest] -> [Ty2] -> TiM a -> TiM a -> TiM a
unifyAll (d:ds) (ty:tys) successA failA =
    case (d,ty) of
      (SingleDest lv1, PackedTy _ lv2) -> unify lv1 lv2 (unifyAll ds tys successA failA) failA
      (TupleDest ds', ProdTy tys') -> unifyAll ds' tys' (unifyAll ds tys successA failA) failA
      (NoDest, PackedTy _ _) -> err$ "Expected destination for packed type"
      (SingleDest _, ProdTy _ ) -> err$ "Expected prod destination for prod type: " ++ (show (d,ty))
      (SingleDest _, _) -> unifyAll ds tys successA failA
      (TupleDest _, PackedTy _ _) -> err$ "Expected prod type for prod destination: " ++ (show (d,ty))
      (TupleDest _, _) -> unifyAll ds tys successA failA
      (NoDest, _) -> unifyAll ds tys successA failA
unifyAll (_:_) [] _ _ = err$ "Mismatched destination and product type arity"
unifyAll [] (_:_) _ _ = err$ "Mismatched destination and product type arity"
unifyAll [] [] successA _ = successA

isCpyVar :: Var -> Bool
isCpyVar v = (take 3 (fromVar v)) == "cpy"

isCpyCall :: L Exp2 -> Bool
isCpyCall (L _ (AppE f _ _)) = True -- TODO: check if it's a real copy call, to be safe
isCpyCall _ = False

freshLocVar :: String -> PassM LocVar
freshLocVar m = gensym (toVar m)

freshRegVar :: PassM Region
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
-- CSK: If operating in Gibbon2 mode, can we add an IndirectionE here, and
-- get rid of RemoveCopies?
copy (e,ty,cs) lv1 =
    case ty of
      PackedTy tc lv2 -> do
          let copyName = mkCopyFunName tc -- assume a copy function with this name
              eapp = l$ AppE copyName [lv2,lv1] [e]
          return (eapp, PackedTy tc lv1, cs)
      _ -> err $ "Did not expect to need to copy non-packed type: " ++ show ty

unNestLet :: Result -> Result
unNestLet (L _ (LetE _ e),ty,cs) = (e,ty,cs)
unNestLet (e,ty,cs) = (e,ty,cs)

pullBnds :: Result -> Maybe (Var, [LocVar], Ty2, L Exp2)
pullBnds (L _ (LetE bnd _),_ty,_cs) = Just bnd
pullBnds (_e,_ty,_cs) = Nothing

buildLets :: [(Var, [LocVar], Ty2, L Exp2)] -> L Exp2 -> L Exp2
buildLets (bnd:bnds) e =
    let e' = buildLets bnds e
    in l$ LetE bnd e'
buildLets [] e = e

addCopyVarToEnv :: [(L (PreExp t2 t1 t), Ty2, t3)] -> FullEnv -> FullEnv
addCopyVarToEnv ((L _ (LetE (v,_,_,_) _),ty,_cs):ls) env =
    let env' = extendVEnv v ty env
    in addCopyVarToEnv ls env'
addCopyVarToEnv (r:ls) env = addCopyVarToEnv ls env
addCopyVarToEnv [] env = env

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
prim :: Prim Ty1 -> PassM (Prim Ty2)
prim p = case p of
           AddP -> return AddP
           SubP -> return SubP
           MulP -> return MulP
           DivP -> return DivP
           ModP -> return ModP
           ExpP -> return ExpP
           RandP-> return RandP
           LtP  -> return LtP
           GtP  -> return GtP
           LtEqP-> return LtEqP
           GtEqP-> return GtEqP
           OrP  -> return OrP
           AndP -> return AndP
           EqSymP -> return EqSymP
           EqIntP -> return EqIntP
           MkTrue -> return MkTrue
           MkFalse -> return MkFalse
           Gensym  -> return Gensym
           SizeParam -> return SizeParam
           RequestEndOf    -> return RequestEndOf
           DictEmptyP dty  -> convertTy dty >>= return . DictEmptyP
           DictInsertP dty -> convertTy dty >>= return . DictInsertP
           DictLookupP dty -> convertTy dty >>= return . DictLookupP
           DictHasKeyP dty -> convertTy dty >>= return . DictHasKeyP
           SymAppend{} -> err $ "Can't handle this primop yet in InferLocations:\n"++show p
           ReadPackedFile{} -> err $ "Can't handle this primop yet in InferLocations:\n"++show p
           ErrorP{} -> err $ "Can't handle this primop yet in InferLocations:\n"++show p

-- | Generate a copy function for a particular data definition.
-- Note: there will be redundant let bindings in the function body which may need to be inlined.
genCopyFn :: DDef Ty1 -> PassM FunDef1
genCopyFn DDef{tyName, dataCons} = do
  arg <- gensym $ "arg"
  casebod <- forM dataCons $ \(dcon, tys) ->
             do xs <- mapM (\_ -> gensym "x") tys
                ys <- mapM (\_ -> gensym "y") tys
                let bod = foldr (\(ty,x,y) acc ->
                                     if isPackedTy ty
                                     then l$ LetE (y, [], ty, l$ AppE (mkCopyFunName (tyToDataCon ty)) [] [l$ VarE x]) acc
                                     else l$ LetE (y, [], ty, l$ VarE x) acc)
                          (l$ DataConE () dcon $ map (l . VarE) ys)
                          (zip3 (L.map snd tys) xs ys)
                return (dcon, L.map (\x -> (x,())) xs, bod)
  return $ FunDef { funName = mkCopyFunName (fromVar tyName)
                  , funArgs = [arg]
                  , funTy   = ( [PackedTy (fromVar tyName) ()]
                              , PackedTy (fromVar tyName) () )
                  , funBody = l$ CaseE (l$ VarE arg) casebod
                  }

-- | Traverses a packed data type and always returns 42.
genTravFn :: DDef Ty1 -> PassM FunDef1
genTravFn DDef{tyName, dataCons} = do
  arg <- gensym $ "arg"
  casebod <- forM dataCons $ \(dcon, tys) ->
             do xs <- mapM (\_ -> gensym "x") tys
                ys <- mapM (\_ -> gensym "y") tys
                let bod = L.foldr (\(ty,x,y) acc ->
                                     if isPackedTy ty
                                     then l$ LetE (y, [], IntTy, l$ AppE (mkTravFunName (tyToDataCon ty)) [] [l$ VarE x]) acc
                                     else l$ LetE (y, [], ty, l$ VarE x) acc)
                          (l$ LitE 42)
                          (zip3 (L.map snd tys) xs ys)
                return (dcon, L.map (\x -> (x,())) xs, bod)
  return $ FunDef { funName = mkTravFunName (fromVar tyName)
                  , funArgs = [arg]
                  , funTy   = ( [PackedTy (fromVar tyName) ()] , IntTy )
                  , funBody = l$ CaseE (l$ VarE arg) casebod
                  }


-- | Add copy & traversal functions for each data type in a prog
addRepairFns :: Prog1 -> PassM Prog1
addRepairFns (Prog dfs fds me) = do
  newFns <- concat <$>
              mapM (\d -> do
                    copy_fn <- genCopyFn d
                    trav_fn <- genTravFn d
                    return [copy_fn, trav_fn])
              (filter (not . isVoidDDef) (M.elems dfs))
  let fds' = fds `M.union` (M.fromList $ L.map (\f -> (funName f, f)) newFns)
  prg <- flattenL1 $ Prog dfs fds' me
  inlineTriv prg

emptyEnv :: FullEnv
emptyEnv = FullEnv { dataDefs = emptyDD
                   , valEnv   = M.empty
                   , funEnv   = M.empty }

{--

t0 :: ArrowTy Ty2
t0 = fst$ runPassM 0 $
     convertFunTy (snd (L1.funArg fd), L1.funRetTy fd)
   where fd = L1.fundefs L1.add1Prog M.! "add1"

tester1 :: L L1.Exp1 -> L Exp2
tester1 e = case fst $ fst $ runPassM 0 $ St.runStateT (runExceptT (inferExp emptyEnv e NoDest)) M.empty of
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
tester2 e = case fst $ fst $ runPassM 0 $ St.runStateT (runExceptT (inferExp' treeEnv e NoDest)) M.empty of
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

treeTy :: Ty1
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

mkAdd1Fun :: ex -> L1.FunDef Ty1 ex
mkAdd1Fun bod = L1.FunDef "add1" ("tr",treeTy) treeTy bod

exadd1 :: L1.Prog
exadd1 = mkAdd1Prog exadd1Bod Nothing

mkIdProg :: Maybe (L L1.Exp1) -> L1.Prog
mkIdProg mainExp = L1.Prog treeDD
                           (M.fromList [("id",idFun)])
                           mainExp

idFun :: L1.FunDef Ty1 (L L1.Exp1)
idFun = L1.FunDef "id" ("tr",treeTy) treeTy (l$ VarE "tr")

--}
