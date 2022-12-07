{-|

With the new location calculus and `inferLocations`, this pass should've been
redundant. But not quite.. We still need it to reorder location variables bound
in case expressions.

For example, after running the add1 program through the pipeline till `RouteEnds`,
this is what the `Node` case looks like:

    ("Node",
     [("x9", "l10"),("y11", "l12")],
        ...)

To "unpack" these fields, `Cursorize` just binds `x9` to `l10` and `y11` to `l12`.
But, the cursor `l12` is not bound (or known) until we call `(add1 x9)` and
get the end_of_read cursor it returns. This happens later in the program.
Thus, `y11` refers to an unbound cursor `l12` here.
FindWitnesses fixes this by moving the `let y11 = l12` binding to its proper place.

Another strategy would be to actually handle this properly in Cursorize.

-}

module Gibbon.Passes.FindWitnesses
  (findWitnesses) where


import Data.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

import Gibbon.Common
-- import Gibbon.L3.Syntax
import Gibbon.L2.Syntax hiding (mapMExprs)

--------------------------------------------------------------------------------

data DelayedBind = DelayVar (Var,[LocVar], Ty2, Exp2)
                 | DelayLoc (LocVar, LocExp)
  deriving (Eq, Show, Ord)

bigNumber :: Int
bigNumber = 10 -- limit number of loops

-- | This pass must find witnesses if they exist in the lexical
-- environment, and it must *reorder* let bindings to bring start/end
-- witnesses into scope.
--
-- Phase Ordering: This must run after flatten.
findWitnesses :: Prog2 -> PassM Prog2
findWitnesses p@Prog{fundefs} = mapMExprs fn p
 where
  fn Env2{vEnv,fEnv} boundlocs ex = return (goFix (Map.keysSet vEnv `Set.union` Map.keysSet fEnv
                                                  `Set.union` boundlocs
                                                  )
                                            ex bigNumber)
  goFix _    ex 0 = error $ "timeout in findWitness on " ++ (show ex)
  goFix bound0 ex0 n = let ex1 = goE bound0 Map.empty ex0
                           ex2 = goE bound0 Map.empty ex1
                       in if ex1 == ex2 then ex2
                          else goFix bound0 ex2 (n - 1)

  docase bound mp (k,vs,e) =
    let (vars,locs) = unzip vs
        bound' = Set.fromList (vars ++ locs) `Set.union` bound
    in (k,vs,goE bound' mp e)

  goE :: Set.Set Var -> Map.Map Var DelayedBind -> Exp2 -> Exp2
  goE bound mp ex =
    let go      = goE bound -- Shorthand.
        goClear = goE (bound `Set.union` Map.keysSet mp) Map.empty
        -- shorthand for applying (L p)
        handle' e = handle bound fundefs mp e
    in
      case ex of
        LetE (v,locs,t, (TimeIt e ty b)) bod ->
            handle' $ LetE (v,locs,t, TimeIt (go Map.empty e) ty b)
                      (goE (Set.insert v (bound `Set.union` Map.keysSet mp)) Map.empty bod)

        Ext ext ->
          case ext of
            LetLocE loc locexp bod ->
              let freelocs = gFreeVars locexp `Set.difference` bound
                  chk = Set.null freelocs
              in if chk
                 -- dbgTraceIt (if loc == "loc_17052" then (sdoc (loc, locexp, freelocs, chk)) else "")
                 then Ext $ LetLocE loc locexp $ goE (Set.insert loc bound) mp bod
                 else
                   case locexp of
                     AfterVariableLE v loc2 b ->
                       (go (Map.insert loc (DelayLoc (loc, (AfterVariableLE v loc2 b))) mp) bod)
                     AfterConstantLE i loc2 ->
                       go (Map.insert loc (DelayLoc (loc, (AfterConstantLE i loc2))) mp) bod
                     _ -> Ext $ LetLocE loc locexp $ goE (Set.insert loc bound) mp bod
            LetRegionE r sz ty bod -> Ext $ LetRegionE r sz ty $ go mp bod
            LetParRegionE r sz ty bod -> Ext $ LetParRegionE r sz ty $ go mp bod
            _ -> handle' $ ex

        LetE (v,locs,t,rhs) bod ->
          let rhs' = go Map.empty rhs -- recur on rhs, but flatten makes these pretty boring.
              freelocs = ex_freeVars rhs' `Set.difference` bound
              chk = Set.null freelocs
          in if chk
             then LetE (v,locs,t,rhs') $ goE (Set.insert v bound) mp (handle (Set.insert v bound) fundefs mp bod)
             else go (Map.insert v (DelayVar (v,locs,t,rhs')) mp) bod

        VarE v         -> handle' $ VarE v
        LitE n         -> handle' $ LitE n
        CharE c        -> handle' $ CharE c
        FloatE n       -> handle' $ FloatE n
        LitSymE v      -> handle' $ LitSymE v
        AppE v locs ls -> handle' $ AppE v locs (map goClear ls)

        SpawnE v locs ls -> handle' $ SpawnE v locs (map goClear ls)
        SyncE            -> SyncE

        PrimAppE pr ls -> handle' $ PrimAppE pr (map goClear ls)
        ProjE i e      -> handle' $ ProjE i (goClear e)

        -- It's ok that we don't go deeper on scrutinees, subexpressions
        -- of tuples, and so on, because flatten should have done
        -- let-lifting out of these contexts:
        MkProdE ls     -> handle' $ MkProdE (map goClear ls)
        DataConE loc k ls -> handle' $ DataConE loc k (map goClear ls)
        TimeIt e t b   -> handle' $ TimeIt (goClear e) t b -- prevent pushing work into timeit

        -- FIXME: give CaseE a treatment like IfE:
        CaseE scrt ls  -> handle' $ CaseE scrt (map (docase bound mp) ls)

        IfE a b c ->
            -- If we have "succeeded" in accumulating all the bindings
            -- we need, then we can discharge their topological sort
            -- here, without duplicating bindings:
            if closed bound mp
            then handle' $ IfE a (goClear b) (goClear c)
            else IfE (go mp a) -- Otherwise we duplicate...
                     (go mp b)
                     (go mp c)
        -- Like MkProdE
        MapE  (v,t,rhs) bod -> handle' $ MapE (v,t,rhs) (goClear bod)
        FoldE (v1,t1,r1) (v2,t2,r2) bod -> handle' $ FoldE (v1,t1,r1) (v2,t2,r2) (goClear bod)
        WithArenaE{} -> error "findWitnesses: WithArenaE not handled."


-- TODO: this needs to preserve any bindings that have TimeIt forms (hasTimeIt).
-- OR we can only match a certain pattern like (Let (_,_,TimeIt _ _) _)
handle :: Set.Set Var -> FunDefs2 -> Map.Map Var DelayedBind -> Exp2 -> Exp2
handle bound fundefs mp expr =
    dbgTrace 6 (" [findWitnesses] building lets using vars "++show vs++" for expr: "++ take 80 (show expr)) $
    -- dbgTraceIt (if vars /= [] then "binding: " ++ sdoc vars else "")
    buildLets mp vars expr
    where freeInBind v = case Map.lookup (view v) mp of
                           Nothing -> []
                           Just (DelayVar (_v,_locs,_t,e)) -> Set.toList $ (ex_freeVars e) `Set.difference` (Map.keysSet fundefs)
                           Just (DelayLoc (_loc, locexp)) -> Set.toList $ (gFreeVars locexp) `Set.difference` (Map.keysSet fundefs)

          (g,vf,_) = graphFromEdges $ zip3 vs vs $ map freeInBind vs
          vars = reverse $ map (\(x,_,_) -> x) $ map vf $ topSort g
          vs = Map.keys $ Map.filterWithKey (\k _v -> Set.member k bound) mp




-- withWitnesses :: [LocVar] -> [LocVar]
-- withWitnesses ls = concatMap f ls
--     where f v = if isWitnessVar v
--                 then [v]
--                 else [v,toWitnessVar v] -- maybe?

-- From the point of view of this pass, we "see through" witness markerS:
view :: Var -> Var
view v = v  -- RRN: actually, coming up with a good policy here is problematic.

-- view v | isWitnessVar v = let Just v' = fromWitnessVar v in v'
--        | otherwise      = v


buildLets :: Map.Map Var DelayedBind -> [Var] -> Exp2-> Exp2
buildLets _mp [] bod = bod
buildLets mp (v:vs) bod =
    case Map.lookup (view v) mp of
      Nothing -> buildLets mp vs bod
      Just (DelayVar bnd) -> LetE bnd $ buildLets mp vs bod
      Just (DelayLoc (loc, bnd)) -> Ext $ LetLocE loc bnd (buildLets mp vs bod)


-- | Are all the free variables currently bound (transitively) in the
-- environment?
closed :: Set.Set Var -> Map.Map Var DelayedBind -> Bool
closed bound mp = Set.null (allBound `Set.difference` allUsed)
  where
   allBound = bound `Set.union` Map.keysSet mp
   -- allUsed = Set.unions [ gFreeVars rhs | (_,_,_,rhs) <- Map.elems mp ]
   allUsed = Set.unions $ map (\db -> case db of
                                  DelayVar (_,_,_,rhs) -> ex_freeVars rhs
                                  DelayLoc (_,locexp)  -> gFreeVars locexp)
                          (Map.elems mp)

mapMExprs :: Monad m => (Env2 Ty2 -> Set.Set LocVar -> Exp2 -> m Exp2) -> Prog2 -> m Prog2
mapMExprs fn (Prog ddfs fundefs mainExp) =
  Prog ddfs <$>
    (mapM (\f@FunDef{funArgs,funTy,funBody} ->
              let env = Env2 (Map.fromList $ zip funArgs (inTys funTy)) funEnv
                  boundlocs = Set.fromList (allLocVars funTy) `Set.union`
                              Set.fromList funArgs
              in do
                bod' <- fn env boundlocs funBody
                return $ f { funBody =  bod' })
     fundefs)
    <*>
    (mapM (\ (e,t) -> (,t) <$> fn (Env2 Map.empty funEnv) Set.empty e) mainExp)
  where funEnv = Map.map funTy fundefs

ex_freeVars :: Exp2 -> Set.Set Var
ex_freeVars = allFreeVars
-- ex_freeVars = gFreeVars
