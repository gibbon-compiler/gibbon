{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Gibbon.Passes.RepairProgram
  (repairProgram, needsRepair) where

import Data.Set as S
import Data.Map as M
import Data.List as L
import Data.Loc

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.GenericOps
import Gibbon.L2.Syntax as L2
import Gibbon.L1.Syntax as L1

import Gibbon.Passes.InferLocations (inferLocs)
import Gibbon.Passes.InferEffects   (inferEffects)
import Gibbon.Passes.RemoveCopies   (removeCopies)
import Gibbon.Passes.Flatten        (flattenL2)
import Gibbon.Passes.AddTraversals  (addTraversals)
import Gibbon.Passes.AddLayout      (addLayout)

--------------------------------------------------------------------------------

{- Note [Repairing programs]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need a program analysis that decides whether a L2 program needs to be repaired.
Why ? Because, when we pattern match on a packed value, L2 assumes that *every*
variable in that pattern is in scope. However, this is not always true.
Consider the rightmost fn (which does not traverse it's input):

   (Node [(x, loc_x), (y, loc_y)] BODY)

Here, since the input is not traversed, we won't have an end-witness for x. And we
cannot access y without it. We need to fix such programs. Effectively, what we're
looking for in this analyis is if we can unpack all the pattern matched variables
in case expressions occurring in the program. For functions, it means that either
the function should traverse it's input, or the un-reachable elements in the pattern
match must remain unused (eg. 'leftmost'). On the other hand, we always have to
repair the main expression.

The compiler has access to 2 program repair strategies -- dummy traversals or
layout information. If we're operating in gibbon1 mode, it uses the former. However,
this changes the asymptotic complexity of the functions. In gibbon2 mode, we compile
such programs using layout information (indirections) instead.
This basically allows O(1) random access to any element of the node.

Also see Note [Adding dummy traversals] and Note [Adding layout information].

-}


-- | Add layout information to the program, but only if required
repairProgram :: Prog1 -> L2.Prog2 -> PassM L2.Prog2
repairProgram oldl1 prg = do
  isGibbon1 <- gopt Opt_Gibbon1 <$> getDynFlags

  if isGibbon1
  -- addTraversals can figure out where/if to add traversals. So we don't need to
  -- run the 'needsRepair' analysis before that.
  then repairGibbon1
  else if repair
       then repairGibbon2
       else return prg

  where
    (repair,_fns) = needsRepair prg

    repairGibbon1 =
      dbgTrace 5 ("Running AddTraversals") <$> do
        l2 <- addTraversals prg
        l2 <- inferEffects l2
        return l2

    repairGibbon2 =
      dbgTrace 5 ("Running AddLayout") <$> do
        l1 <- addLayout oldl1
        l2 <- inferLocs l1
        l2 <- flattenL2 l2
        l2 <- removeCopies l2
        l2 <- inferEffects l2
        return l2


-- | If a program needs to be repaired, it returns the functions that
-- need traversals [TODO: or the data types that need indirections so
-- that we can selectively enable indirections].
needsRepair :: L2.Prog2 -> (Bool, S.Set Var)
needsRepair (Prog ddefs fundefs mainExp) =
  let env2 = Env2 M.empty (L2.initFunEnv fundefs)
      specialfns = L.foldl' (\acc fn -> if isSpecialFn ddefs fn
                                        then S.insert (funName fn) acc
                                        else acc)
                   S.empty (M.elems fundefs)
      mainExp' = case mainExp of
                   Nothing -> False
                   Just (mn, _) -> needsRepairExp ddefs fundefs False specialfns S.empty env2 mn
      fnsneedlayout = M.map (\FunDef{funName,funBody} ->
                               if funName `S.member` specialfns
                               then False
                               else needsRepairExp ddefs fundefs False specialfns S.empty env2 funBody)
                      fundefs
  in (mainExp' || (L.any id (M.elems fnsneedlayout)), (S.fromList $ M.keys $ M.filter id fnsneedlayout))

needsRepairExp :: DDefs L2.Ty2 -> L2.FunDefs2 -> Bool -> S.Set Var -> S.Set LocVar
               -> Env2 L2.Ty2 -> L L2.Exp2 -> Bool
needsRepairExp ddefs fundefs base special traversed env2 (L _ ex) = base ||
  case ex of
    VarE{}    -> base
    LitE{}    -> base
    LitSymE{} -> base
    AppE f _ arg  ->
      let argty = gTypeExp ddefs env2 arg
          g = if f `S.member` special then specialTraversal else fnTraversal
          (traversed', base') = g traversed (fundefs # f) (L2.locsInTy argty)
          base'' = base || base'
      in (needsRepairExp ddefs fundefs base'' special traversed' env2 arg)
    PrimAppE{} -> base
    LetE (v,_,ty, L _ (AppE f _ arg)) bod ->
      let argty = gTypeExp ddefs env2 arg
          g = if f `S.member` special then specialTraversal else fnTraversal
          (traversed', base') = g traversed (fundefs # f) (L2.locsInTy argty)
          base'' = base || base'
      in (needsRepairExp ddefs fundefs base'' special traversed' env2 arg) ||
         (needsRepairExp ddefs fundefs base'' special traversed' (extendVEnv v ty env2) bod)
    LetE (v,_,ty,rhs) bod ->
      go env2 rhs ||  go (extendVEnv v ty env2) bod
    IfE a b c   -> (go env2 a) || (go env2 b) || (go env2 c)
    MkProdE{}   -> base
    ProjE _ e   -> go env2 e
    CaseE _ brs -> any id (L.map (docase traversed env2) brs)
    DataConE _ _ ls -> all (go env2) ls
    TimeIt e _ _ -> go env2 e
    Ext ext ->
      case ext of
        L2.LetRegionE _ bod ->  go env2 bod
        L2.LetLocE _ _ bod -> go env2 bod
        _ -> False
    MapE{}  -> error $ "needsRepairExp: TODO MapE"
    FoldE{} -> error $ "needsRepairExp: TODO FoldE"
  where
    go = needsRepairExp ddefs fundefs base special traversed

    docase :: S.Set LocVar -> Env2 L2.Ty2
           -> (DataCon, [(Var,LocVar)], L L2.Exp2) -> Bool
    docase traversed1 env21 (dcon,vlocs,bod) =
      let (vars,locs) = unzip vlocs
          tys = lookupDataCon ddefs dcon
          tys' = substLocs' locs tys
          env2' = extendsVEnv (M.fromList $ zip vars tys') env21
      in (needsRepairExp ddefs fundefs base special traversed1 env2' bod)

isSpecialFn :: DDefs L2.Ty2 -> L2.FunDef2 -> Bool
isSpecialFn ddefs FunDef{funTy, funBody} =
  if traversesAllInputs
  then True
  else go (S.fromList $ L2.inLocVars funTy) funBody
  where
    traversesAllInputs =
      length (L2.inLocVars funTy) == length (S.toList $ L2.arrEffs funTy)

    go :: S.Set LocVar -> L L2.Exp2 -> Bool
    go need (L _ e) =
      case e of
        CaseE _ brs -> all docase brs
        -- Straightforward recursion
        VarE{} -> S.null need
        LitE{} -> S.null need
        LitSymE{}  -> S.null need
        AppE{}     -> S.null need
        PrimAppE{} -> S.null need
        LetE (_,_,_,(L _ (Ext (L2.IndirectionE _ _ _ (a,_) _)))) bod ->
          go (S.delete a need) bod
        LetE (_,_,_,rhs) bod -> (go need rhs) || (go need bod)
        IfE a b c  -> (go need a) || (go need b) || (go need c)
        MkProdE ls -> any (go need) ls
        ProjE _ e  -> go need e
        DataConE _ _ ls -> any (go need) ls
        TimeIt e _ _    -> go need e
        Ext ext ->
          case ext of
            L2.LetLocE _ _ bod   -> go need bod
            L2.LetRegionE _ bod  -> go need bod
            _ -> False
        MapE{}  -> error "isSpecialFn: MapE"
        FoldE{} -> error "isSpecialFn: FoldE"

    docase :: (DataCon, [(Var,LocVar)], L L2.Exp2) -> Bool
    docase (dcon,vlocs,bod) =
      let (vars,_) = unzip vlocs
          tys = lookupDataCon ddefs dcon
          needtraversal = cantunpack False tys vars []
      -- It's special if it has some elements which cannot be accessed,
      -- but those are unused
      in all (\v -> not $ L2.occurs (S.singleton v) bod) needtraversal

    cantunpack :: Bool -> [L2.Ty2] -> [Var] -> [Var] -> [Var]
    cantunpack _ [] [] acc = acc
    cantunpack wasPacked (ty:tys) (v:vs) acc  =
      case (hasPacked ty, wasPacked) of
        -- This is not the first packed element. Add it to the acc
        (True, True)  -> cantunpack wasPacked tys vs (v:acc)
        -- First packed element. Record that fact
        (True, False) -> cantunpack True tys vs acc
        (False, _)    -> cantunpack wasPacked tys vs acc
    cantunpack _ _ _ _ = error "cantunpack: error"

fnTraversal :: S.Set Var -> L2.FunDef2 -> [LocVar] -> (S.Set LocVar, Bool)
fnTraversal traversed FunDef{funTy} locs =
  let funeff = L2.arrEffs funTy
      inlocs = L2.inLocVars funTy
      substMap = M.fromList $ zip inlocs locs
      funeff' = L2.substEffs substMap funeff
  in ( S.union (S.map (\(L2.Traverse a) -> a) funeff') traversed
     , length inlocs /= length (S.toList funeff')
     )

-- Some functions are special (eg. leftmost). They don't traverse their input,
-- but they can be compiled without adding any layout information to the program.
-- To return the correct value from `needsRepairExp`, we mark all input
-- locations at the call site of such functions as "traversed".
specialTraversal :: S.Set Var -> L2.FunDef2 -> [LocVar] -> (S.Set LocVar, Bool)
specialTraversal traversed FunDef{funTy} locs =
  let fninlocs = L2.inLocVars funTy
      inlocs = L.take (length fninlocs) locs
  in (S.union (S.fromList inlocs) traversed, False)
