-- | An intermediate language with an effect system that captures traversals.
--
-- ASSUMES that the flatten pass has run, and thus we have trivial AppE operands.
--

module Gibbon.Passes.InferEffects
  (inferEffects, inferExp) where

import Data.Loc
import Data.List as L
import Data.Set as S
import Data.Map as M

import Gibbon.Common
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

-- | Chatter level for this module:
lvl :: Int
lvl = 5

type FunEnv2 = M.Map Var ArrowTy2

locsEffect :: [LocVar] -> Set Effect
locsEffect = S.fromList . L.map Traverse

-- | We initially populate all functions with MAXIMUM effect signatures.
--   Subsequently, these monotonically SHRINK until a fixpoint.
--   We also associate fresh location variables with packed types.
initialEnv :: FunDefs2 -> FunEnv2
initialEnv mp = M.map go mp
  where
    go :: FunDef2 -> ArrowTy2
    go FunDef{funTy} =
      let locs       = allLocVars funTy
          maxEffects = locsEffect locs
      in funTy { arrEffs = maxEffects }


inferEffects :: Prog2 -> PassM Prog2
inferEffects prg@Prog{ddefs,fundefs} = do
  let finalFunTys = fixpoint 1 fundefs (initialEnv fundefs)
      funs = M.map (\fn@FunDef{funName} ->
                       fn{ funTy = finalFunTys ! funName })
             fundefs
  return $ prg { fundefs = funs }
  where
    fixpoint :: Int -> FunDefs2 -> FunEnv2 -> FunEnv2
    fixpoint iter funs fenv =
       let funtys = M.map (inferFunDef ddefs fenv) funs
       in
         if fenv == funtys
         then dbgTrace 4 ("\n<== Fixpoint completed after iteration "++show iter++" ==>") $ fenv
         else fixpoint (iter+1) funs funtys


inferFunDef :: DDefs Ty2 -> FunEnv2 -> FunDef2 -> ArrowTy2
inferFunDef ddfs fenv FunDef{funArgs,funBody,funTy} = funTy { arrEffs = S.intersection travs eff }
  where
    env0  = M.fromList $ zip funArgs (arrIns funTy)
    travs = S.fromList $ L.map Traverse $ inLocVars funTy
    (eff,_outLoc) = inferExp ddfs fenv env0 funBody


inferExp :: DDefs Ty2 -> FunEnv2 -> TyEnv Ty2 -> L Exp2 -> (Set Effect, Maybe LocVar)
inferExp ddfs fenv env (L _p expr) =
  case expr of
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

    SpawnE _ fn locs args -> inferExp ddfs fenv env (l$ AppE fn locs args)

    SyncE -> (S.empty, Nothing)

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

    WithArenaE v e -> inferExp ddfs fenv env e

    Ext (LetRegionE _ rhs) -> inferExp ddfs fenv env rhs
    Ext (LetLocE _ _ rhs)  -> inferExp ddfs fenv env rhs
    Ext (RetE _ _)         -> (S.empty, Nothing)
    Ext (FromEndE _ )      -> (S.empty, Nothing)
    Ext (IndirectionE{})   -> (S.empty, Nothing)

    oth -> error $ "FINISHME: inferExp " ++ sdoc oth

  where
    packedLoc :: Ty2 -> Maybe LocVar
    packedLoc ty = case ty of
                     PackedTy _ loc -> Just loc
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
          winner = -- If there is NO packed child data, then our object has static size:
                   (L.all (not . hasPacked) tys) ||

                   -- Or if all non-static items were traversed:
                   (case packedOnly of
                      [] -> False
                      ls -> let patVMap = M.fromList patVs
                                packedlocs = L.map (\(a,_) -> patVMap # a) ls
                            in all (\x -> S.member (Traverse x) eff) packedlocs)

                   -- Or maybe the last-use rule applies:
                   -- TODO

          -- Also, in any binding form we are obligated to not return
          -- our local bindings in traversal side effects:
          isNotLocal (Traverse v) = not $ L.elem v locs
          stripped = S.filter isNotLocal eff
      in ( winner, (stripped,Nothing) )
