{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- | An intermediate language with an effect system that captures traversals.
--
-- GRAMMAR: takes an L1 program to an L2 program.
-- ASSUMES that the flatten pass has run, and thus we have trivial AppE operands.
--

module Gibbon.Passes.InferEffects
    ( inferEffects, inferFunDef
     -- * For other passes that perform similar location-trackinga
    , instantiateApp, freshLoc, freshenArrowSchema, zipLT, zipTL
    )
    where
import Control.Monad (when)
import Control.DeepSeq
import qualified Gibbon.Common as C
import           Gibbon.L2.Syntax
import Gibbon.Passes.Flatten (typeExp)
import Gibbon.Common hiding (FunDef)
import qualified Gibbon.L1.Syntax as L1
-- import Gibbon.L1.Syntax (UrTy(..), SymTy)
import Gibbon.L1.Syntax hiding (Ty, FunDef, Prog, mapExprs, progToEnv, fundefs)
import Data.List as L
import Data.Set as S
import Data.Map as M
import Text.PrettyPrint.GenericPretty
-- import Debug.Trace
-- import GHC.Stack (errorWithStackTrace)

--------------------------------------------------------------------------------

-- | Chatter level for this module:
lvl :: Int
lvl = 5

type OldFuns = FunDefs L1.Ty L1.Exp

type FunEnv = M.Map Var (ArrowTy Ty)

-- | We initially populate all functions with MAXIMUM effect signatures.
--   Subsequently, these monotonically SHRINK until a fixpoint.
--   We also associate fresh location variables with packed types.
initialEnv :: OldFuns -> FunEnv
initialEnv mp = M.map (\x -> fst $ runSyM 0 (go x))  mp
  where
    go :: C.FunDef L1.Ty L1.Exp -> SyM (ArrowTy Ty)
    go (C.FunDef _ (_,argty) ret _)  =
        do argTy <- tyWithFreshLocs argty
           retTy <- tyWithFreshLocs ret
           let maxEffects = S.map Traverse
                            (S.union (getTyLocs argTy) (getTyLocs retTy))
           return $ ArrowTy argTy maxEffects retTy


inferEffects :: L1.Prog -> SyM Prog
inferEffects (L1.Prog dd fds mainE) = do
  finalFunTys <- fixpoint 1 fds (initialEnv fds)
  let funs = (M.intersectionWith (\ (C.FunDef nm (arg,_) _ bod) arrTy ->
                                  FunDef nm arrTy arg bod)
              fds finalFunTys)

      mainE' = fmap addTy mainE
      addTy e = (e, typeExp (dd,progToEnv (Prog dd funs Nothing)) e)

  return $ force finalFunTys `seq`
           Prog dd funs mainE'
 where
   fixpoint :: Int -> OldFuns -> FunEnv -> SyM FunEnv
   fixpoint iter funs env =
    do funtys <- M.fromList <$>
                 mapM (\(k,v) -> (k,) <$> inferFunDef (dd,env) v)
                     (M.toList funs)
       if env == funtys
        then dbgTrace 4 ("\n<== Fixpoint completed after iteration "++show iter++" ==>") $
             return env
        else fixpoint (iter+1) funs funtys

freshenVar :: LocVar -> SyM LocVar
freshenVar = gensym

freshenArrowSchema :: ArrowTy Ty -> SyM (ArrowTy Ty)
freshenArrowSchema (ArrowTy inT effs outT) = do
    let lvs = allLocVars inT ++ allLocVars outT
    lvs' <- mapM freshenVar lvs
    let subst = M.fromList (zip lvs lvs')
    return $ ArrowTy (substTy subst inT)
                     (substEffs subst effs)
                     (substTy subst outT)

-- | Take a polymorphic ArrowTy, instantiate its location variables
--   and traversal effects with the given (input) locations.
--   Return the location that the result of the application will occupy.
instantiateApp :: ArrowTy Ty -> Loc -> SyM (Set Effect, Loc)
instantiateApp arrty0 loc = do
    (ArrowTy inT effs outT) <- freshenArrowSchema arrty0
    let subst = zipTL inT loc
    dbgTrace lvl ("\n  instantiateApp: Came up with subst: "++show subst) $
     return (substEffs subst effs,
            dbgTraceIt "   instantiate result loc" $ rettyToLoc (substTy subst outT))
  where
   -- Question: when computing the return location, which variables are Fresh?
   -- Conversely, when would we need to use Fixed?
   rettyToLoc :: Ty -> Loc
   rettyToLoc t =
     case t of
       IntTy  -> Bottom
       SymTy  -> Bottom
       BoolTy -> Bottom
       SymDictTy _  -> Top
       ProdTy ls    -> TupLoc $ L.map rettyToLoc ls
       PackedTy _ l -> Fresh l
       ListTy _ -> error "rettyToLoc: FINISHME lists"

-- | Unify type and locaion , creating a mapping between variables in
-- the former to the latter.
zipTL :: Ty -> Loc -> M.Map LocVar LocVar
zipTL _ Bottom                 = M.empty
zipTL (PackedTy _ v) (Fixed l) = M.singleton v l
zipTL (PackedTy _ v) (Fresh l) = M.singleton v l
zipTL (ProdTy l1) (TupLoc l2)  = M.unions (zipWith zipTL l1 l2)

-- Here is a tricky one.
zipTL (PackedTy l v) Top =
    error $ "zipTL: don't yet know what to do with Packed/Top case: "++
          show (PackedTy l v)
    -- M.empty -- M.singleton v l
zipTL ty loc = error$ "zipTL: argument type "++show(doc ty)
                   ++"does not have matching structure to location: "++show(doc loc)

-- | Unify location and type, creating a mapping between variables in
-- the former to the latter.
zipLT :: Loc -> Ty -> M.Map LocVar LocVar
zipLT Bottom _                 = M.empty
zipLT (Fixed l) (PackedTy _ v) = M.singleton l v
zipLT (Fresh l) (PackedTy _ v) = M.singleton l v
zipLT (TupLoc l1) (ProdTy l2)  = M.unions (zipWith zipLT l1 l2)
-- Here is a tricky one.
zipLT Top       (PackedTy l v) =
    error $ "zipLT: don't yet know what to do with Top/Packed case: "++
          show (PackedTy l v)
    -- M.empty -- M.singleton v l
zipLT loc ty = error$ "zipLT: argument type "++show(doc ty)
                   ++"does not have matching structure to location: "++show(doc loc)


--------------------------------------------------------------------------------


freshLoc :: String -> SyM Loc
freshLoc m = Fresh <$> gensym (toVar m)

-- | Infer the traversal effects for a function.
inferFunDef :: (DDefs L1.Ty,FunEnv) -> C.FunDef L1.Ty L1.Exp -> SyM (ArrowTy Ty)
inferFunDef (ddefs,fenv) (C.FunDef name (arg,argty) _retty bod) =
    -- For this pass we don't need to know the output location:
    do argty' <- tyWithFreshLocs argty -- Temp.
       let ArrowTy inTy _ outTy = fenv # name
           env0    = M.singleton arg argLoc
           argLoc  = argtyToLoc (mangle arg) argty'

       (effs1,bodLoc) <- inferExp (ddefs,fenv) env0 bod

       -- Unify resulting location with the output type to create equalities between input and output locations.
       -- Then substitute into the return type using the resulting equalities.
       -- This helps to infer the right type signature for identity functions ; (tests 18c, 18d, 18e, 18f).
       let argIn   = zipLT argLoc inTy
           bodOut  = zipLT bodLoc outTy
           eqs     = M.fromList $ M.foldrWithKey
                                 (\k v acc -> if M.member k argIn
                                              then (v, (argIn # k)):acc
                                              else (v,v):acc)
                                 [] bodOut
           outTy'  = substTy eqs outTy

       when (outTy' /= outTy) $ do
         dbgTrace lvl ("\nInput/Output location equalities: " ++ show (M.toList eqs)) return()
         dbgTrace lvl ("\nOutput type for " ++ show (fromVar name) ++ " changed from: " ++ show outTy ++ " to: " ++ show outTy') return()

       -- Finally, restate the effects in terms of the type schema for the fun:
       let allEffs = substEffs argIn effs1
           externalLocs = S.fromList $ allLocVars inTy ++ allLocVars outTy'
           finalEffs = S.filter (\(Traverse v) -> S.member v externalLocs) allEffs
       return $ ArrowTy inTy finalEffs outTy'


-- | Infer the traversal effects and abstract return value location for an expression.
inferExp :: (DDefs L1.Ty, FunEnv) -> LocEnv -> L1.Exp -> SyM (Set Effect, Loc)
inferExp (ddefs,fenv) env e = exp env e
  where
  -- We have one location for the destination, and another for each lexical binding.
  exp :: LocEnv -> L1.Exp -> SyM (Set Effect, Loc)
  exp env e =
    dbgTrace lvl ("\nProcessing exp: "++show e++"\n  with env: "++show env) $
    case e of
     -- QUESTION: does a variable reference count as traversing to the end?
     -- If so, the identity function has the traverse effect.
     -- I'd prefer that the identity function get type (Tree_p -{}-> Tree_p).
     L1.VarE v    -> return (S.empty, env # v)
     L1.LitE    _ -> return (S.empty, Bottom)
     L1.LitSymE _ -> return (S.empty, Bottom)
     L1.CaseE e1 mp ->
      do (eff1,loc1) <- exp env e1
         (bools,effs,locs) <- unzip3 <$>
           mapM (\(dcon,patVs,erhs) -> caserhs env (toVar dcon,patVs,erhs)) mp
         -- Critical policy point!  We only get to the end if ALL
         -- branches get to the end.
         let end = if all id bools
                   then case getLocVar loc1 of
                          Just v  -> S.singleton (Traverse v)
                          Nothing -> S.empty
                   else S.empty
         let (locFin,cnstrts) = joins locs

         when (not (L.null cnstrts)) $
           dbgTrace 1 ("Warning: FINISHME: process these constraints: "++show cnstrts) (return ())

         return $ dbgTrace lvl ("\n==>Results on subcases: "++show (doc(bools,effs,locs))) $
                (S.union (S.union eff1 end)
                         (L.foldl1 S.intersection effs),
                 locFin)

     L1.IfE a b c ->
         do (eff1,_loc1) <- exp env a
            (eff2,loc2) <- exp env b
            (eff3,loc3) <- exp env c
            return (S.union eff1 (S.intersection eff2 eff3),
                    fst (join loc2 loc3))

     L1.TimeIt e _ _ -> exp env e

     -- Construct output packed data.  We will always "scroll to the end" of
     -- output values, so they are not interesting for this effect analysis.
     L1.DataConE k ls -> L1.assertTrivs ls $
        -- And because it's freshly allocated, it has unconstrained location:
        do l <- freshLoc $ "mk"++k
           return (S.empty,l)

     -- Here we UNION the end-points that are reached in the RHS and the BOD:
     L1.LetE (v,_t,rhs) bod ->
      do (reff,rloc) <- exp env rhs
         let env' = M.insert v rloc env
         (beff,bloc) <- exp env' bod
         return (S.union beff reff, bloc)

     -- We need to reach a fixed point where we jointly infer effects
     -- for all functions.
     L1.AppE rat rand -> -- rand guaranteed to be trivial here.
      let getloc (VarE v) = env # v
          getloc (MkProdE trvz) = TupLoc (L.map getloc trvz)
          getloc (ProjE ix trv) = let TupLoc ls = getloc trv
                                  in ls !! ix
          getloc (LitSymE _)    = Bottom
          getloc oth | isTriv oth = error$ "InferEffects/FINISHME: handle this trivial rand: "++show oth
                     | otherwise  = error$ "InferEffects: expected flattened program found non-trivial operand: "++show oth
          arrTy = fenv # rat
      in instantiateApp arrTy (getloc rand)

     -- If rands are already trivial, no traversal effects can occur here.
     L1.PrimAppE _ rands -> L1.assertTrivs rands $
         return (S.empty, Bottom) -- All primitives operate on non-packed data.

     -- If any sub-expression reaches a destination, we can reach the destination:
     L1.MkProdE ls -> do (effs,locs) <- unzip <$> mapM (exp env) ls
                         return (S.unions effs, TupLoc locs)
     L1.ProjE n e -> do
       (eff, loc) <- exp env e
       let loc' = case loc of
                    TupLoc ls -> ls !! n
                    _ -> error $ "inferExp: ProjE "++ show e ++ " expects a TupLoc, but got: " ++ show loc
       return (eff, loc')

     L1.MapE{}  -> error "FINISHLISTS"
     L1.FoldE{} -> error "FINISHLISTS"

--     L1.MkPacked k ls ->

  -- Returns true if this particular case reaches the end of the scrutinee.
  caserhs :: LocEnv -> (Var,[Var],L1.Exp) -> SyM (Bool, Set Effect, Loc)
  caserhs env (_dcon,[],erhs) = do
     (effs,loc) <- exp env erhs
     return $ ( True, effs, loc)

  caserhs env (dcon,patVs,erhs) =
   -- Subtlety: if the rhs expression consumes the RIGHTMOST
   -- pattern variable, then the later code transformations MUST
   -- ensure that it consumes everything.
   do let tys    = lookupDataCon ddefs (fromVar dcon)
          zipped = fragileZip' patVs tys ("Error in "++ (fromVar dcon) ++" case: "
                                         ++"pattern vars, "++show patVs++
                                         ", do not match the number of types "++show tys)
          freeRHS = L1.freeVars erhs

          packedOnly = L.filter (\(_,t) -> L1.hasPacked t) zipped

      env' <- extendLocEnv zipped env
          -- WARNING: we may need to generate "nested inside of" relation
          -- between the patVs and the scrutinee.
      (eff,rloc) <- exp env' erhs
      let winner =
           dbgTrace lvl ("\nInside caserhs, for "++show (dcon,patVs,tys)
                        ++ "\n  freevars "++show freeRHS
                        ++",\n  env "++show env'++",\n  eff "++show eff) $
           -- We've gotten "to the end" of a nullary constructor just by matching it:
           (L.null patVs) ||
           -- If there is NO packed child data, then our object has static size:
           (L.all (not . L1.hasPacked) tys) ||
             -- Or if the last non-static item was in fact traversed:
             (case packedOnly of
                [] -> False
                _:_ -> S.member (Traverse (fst$ last packedOnly)) eff) ||

             -- Or maybe the last-use rule applies:
             (let (lastV,lastTy) = last zipped
                  isUsed = S.member lastV freeRHS
              in
              case lastTy of
                -- If the last field is packed, then we better have
                -- traversed it in the RHS:
                L1.PackedTy{}    -> S.member (Traverse lastV) eff
                -- ANY usage of a fixed-sized last field requires
                -- traversal of packed data in the middle fields:
                L1.IntTy  -> isUsed
                L1.SymTy  -> isUsed
                L1.BoolTy -> isUsed
                L1.SymDictTy{} -> error "no SymDictTy allowed inside Packed"
                L1.ProdTy{}    -> error "no ProdTy allowed inside Packed"
                L1.ListTy{} -> error "FINISHLISTS")

          -- Also, in any binding form we are obligated to not return
          -- our local bindings in traversal side effects:
          isLocal (Traverse v) = L.elem v patVs -- FIXME... need LocVar
          stripped  = S.filter isLocal eff
      return ( winner, stripped, rloc )
