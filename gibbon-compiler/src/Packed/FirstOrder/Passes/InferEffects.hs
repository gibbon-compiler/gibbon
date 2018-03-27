{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | An intermediate language with an effect system that captures traversals.
--
-- ASSUMES that the flatten pass has run, and thus we have trivial AppE operands.
--

module Packed.FirstOrder.Passes.InferEffects
  (inferEffects) where

import Data.Loc
import Data.List as L
import Data.Set as S
import Data.Map as M

import Packed.FirstOrder.L2.Syntax
import Packed.FirstOrder.Common hiding (FunDef, FunEnv)
import Packed.FirstOrder.L1.Syntax hiding (Prog, FunDef, ddefs, fundefs, mainExp)

--------------------------------------------------------------------------------

-- | Chatter level for this module:
lvl :: Int
lvl = 5

type FunEnv = M.Map Var (ArrowTy Ty2)

locsEffect :: [LocVar] -> Set Effect
locsEffect = S.fromList . L.map Traverse

type LocEnv = M.Map Var LocVar
type TyEnv  = M.Map Var Ty2

-- | We initially populate all functions with MAXIMUM effect signatures.
--   Subsequently, these monotonically SHRINK until a fixpoint.
--   We also associate fresh location variables with packed types.
initialEnv :: NewFuns -> FunEnv
initialEnv mp = M.map go mp
  where
    go :: FunDef -> ArrowTy Ty2
    go FunDef{funty} =
      let locs       = allLocVars funty
          maxEffects = locsEffect locs
      in funty { arrEffs = maxEffects }


inferEffects :: Prog -> SyM Prog
inferEffects prg@Prog{ddefs,fundefs} = do
  let finalFunTys = fixpoint 1 fundefs (initialEnv fundefs)
      funs = M.map (\fn@FunDef{funname} ->
                       fn{ funty = finalFunTys ! funname })
             fundefs
  return $ prg { fundefs = funs }
  where
    fixpoint :: Int -> NewFuns -> FunEnv -> FunEnv
    fixpoint iter funs fenv =
       let funtys = M.map (inferFunDef ddefs fenv) funs
       in
         if fenv == funtys
         then dbgTrace 4 ("\n<== Fixpoint completed after iteration "++show iter++" ==>") $ fenv
         else fixpoint (iter+1) funs funtys


inferFunDef :: DDefs Ty2 -> FunEnv -> FunDef -> ArrowTy Ty2
inferFunDef ddfs fenv FunDef{funarg,funbod,funty} = funty { arrEffs = S.intersection travs eff }
  where
    env0  = M.singleton funarg (arrIn funty)
    travs = S.fromList $ L.map Traverse $ inLocVars funty
    (eff,_outLoc) = inferExp ddfs fenv env0 funbod


inferExp :: DDefs Ty2 -> FunEnv -> TyEnv -> L Exp2 -> (Set Effect, Maybe LocVar)
inferExp ddfs fenv env (L _p exp) =
  case exp of
    -- QUESTION: does a variable reference count as traversing to the end?
    -- If so, the identity function has the traverse effect.
    -- I'd prefer that the identity function get type (Tree_p -{}-> Tree_p).
    VarE v -> case M.lookup v env of
                Just ty -> (S.empty, packedLoc ty)
                Nothing -> error $ "Unknown var: " ++ sdoc v

    LitE _    -> (S.empty, Nothing)
    LitSymE _ -> (S.empty, Nothing)

    AppE v locs _e ->
      -- Substitue locations used at this particular call-site in the function
      -- effects computed so far
      let orgLocs = allLocVars (fenv # v)
          locMap  = M.fromList $ zip orgLocs locs
          eff     = arrEffs (fenv # v)
      in (substEffs locMap eff, Nothing)

    -- If rands are already trivial, no traversal effects can occur here.
    -- All primitives operate on non-packed data.
    PrimAppE _ rands -> assertTrivs rands (S.empty, Nothing)

    -- TODO: what would _locs have here ?
    LetE (v,_locs,ty,rhs) bod ->
      let (effRhs,_rhsLoc) = inferExp ddfs fenv env rhs
          -- TODO: extend env with rhsLoc ? or _locs ?
          (effBod,bLoc) = inferExp ddfs fenv (M.insert v ty env) bod
      in (S.union effRhs effBod, bLoc)

    -- TODO: do we need to join locC and locA
    IfE tst consq alt ->
      let (effT,_locT) = inferExp ddfs fenv env tst
          (effC,locC) = inferExp ddfs fenv env consq
          (effA,locA) = inferExp ddfs fenv env alt
          loc = case (locC,locA) of
                  (Nothing,Nothing)  -> Nothing
                  (Just l', Nothing) -> Just l'
                  (Nothing, Just l') -> Just l'
                  (Just l', Just _m) -> Just l'
      in (S.union effT (S.intersection effC effA), loc)

    -- ignore locations, won't have any effect on the generated effects. ??
    MkProdE ls ->
      let (effs, _locs) = unzip $ L.map (inferExp ddfs fenv env) ls
      in (S.unions effs, Nothing)

    ProjE _n e ->
      let (eff, _loc) = inferExp ddfs fenv env e
      in (eff, Nothing)

    CaseE e mp ->
      let (eff,loc1) = inferExp ddfs fenv env e
          (bools,effsLocs) = unzip $ L.map caserhs mp
          (effs,_) = unzip effsLocs

          -- Should we check that we actually _have_ all cases ? Or are incomplete case
          -- matches enough for traversal ?

          -- Critical policy point!  We only get to the end if ALL
          -- branches get to the end.
          end = if all id bools
                then case loc1 of
                       Just v  -> S.singleton (Traverse v)
                       Nothing -> S.empty
                else S.empty
          ret = S.union (S.union eff end)
                        (L.foldl1 S.intersection effs)
      in (ret, Nothing)

    -- Construct output packed data.  We will always "scroll to the end" of
    -- output values, so they are not interesting for this effect analysis.
    DataConE _loc _dcon es -> assertTrivs es (S.empty, Nothing)

    TimeIt e _ _ -> inferExp ddfs fenv env e

    Ext (LetRegionE _ rhs) -> inferExp ddfs fenv env rhs
    Ext (LetLocE _ _ rhs)  -> inferExp ddfs fenv env rhs
    Ext (RetE _ _)         -> (S.empty, Nothing)
    Ext (FromEndE _ )      -> (S.empty, Nothing)
    Ext (IndirectionE{})   -> (S.empty, Nothing)

    oth -> error $ "FINISHME: inferExp " ++ sdoc oth

  where

    packedLoc :: Ty2 -> Maybe LocVar
    packedLoc ty = case ty of
                     PackedTy _ l -> Just l
                     _ -> Nothing

    caserhs :: (DataCon, [(Var,LocVar)], L Exp2) -> (Bool, (Set Effect, Maybe LocVar))
    -- We've gotten "to the end" of a nullary constructor just by matching it:
    caserhs (_dcon,[],e) = ( True , inferExp ddfs fenv env e )
    caserhs (dcon,patVs,e) =
      let (vars,locs) = L.unzip patVs
          tys    = lookupDataCon ddfs dcon
          zipped = fragileZip' vars tys ("Error in "++ dcon ++" case: "
                                         ++"pattern vars, "++show vars++
                                         ", do not match the number of types "
                                         ++show tys)

          env' = M.union env (M.fromList zipped)

          packedOnly = L.filter (\(_,t) -> hasPacked t) zipped

          (eff,_) = inferExp ddfs fenv env' e
          winner = dbgTrace lvl ("\nInside caserhs, for "++show (dcon,patVs,tys)
                        -- ++ "\n  freevars "++show freeRHS
                        -- ++",\n  env "++show env'++",\n  eff "++show eff
                                ) $
                   -- If there is NO packed child data, then our object has static size:
                   (L.all (not . hasPacked) tys) ||

                   -- Or if the last non-static item was in fact traversed:
                   (case packedOnly of
                         []  -> False
                         _:_ -> let patVMap       = M.fromList patVs
                                    lastPackedLoc = case M.lookup (fst$last packedOnly) patVMap of
                                                      Just loc -> loc
                                                      Nothing -> error $
                                                                 sdoc patVMap ++ "does not contain"
                                                                 ++  sdoc (fst$last packedOnly)
                                in S.member (Traverse lastPackedLoc) eff)
                   -- Or maybe the last-use rule applies:
                   -- TODO

          -- Also, in any binding form we are obligated to not return
          -- our local bindings in traversal side effects:
          isNotLocal (Traverse v) = not $ L.elem v locs
          stripped = S.filter isNotLocal eff
      in ( winner, (stripped,Nothing) )
