{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Gibbon.Passes.AddLayout
  (repairProgram, needsLayout) where

import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Set as S
import Text.PrettyPrint.GenericPretty

import Gibbon.GenericOps
import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L1.Syntax as L1
import qualified Gibbon.L2.Syntax as L2

import Gibbon.Passes.InferLocations (inferLocs)
import Gibbon.Passes.InferEffects   (inferEffects)
import Gibbon.Passes.RemoveCopies   (removeCopies)
import Gibbon.Passes.Flatten        (flattenL2)

--------------------------------------------------------------------------------

{- Note [Adding layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass runs afetr InferEffects.

Instead of using "dummy_traversals" as another program repair strategy in
InferLocations, it's easier to annotate the program first, and
then repair it later if required. `needsLayout` makes this decision.

Consider this example:

    main = add1 . buildtree

This example doesn't need to be repaired, and can be compiled in it's current form.
But on the other hand,

    main =  add1 . rightmost . buildtree

...won't, because `rightmost` doesn't traverse the left element of a node.
Instead of adding the traversal to `rightmost`, we take a step back, and add
layout information to the program. This basically allows O(1) random
access to any element of the node.

Note that we can't add layout information to an L2 program, as it would distort
the the location arithmetic. Instead, (1) we transform the program to L1 and
add layout information to that, (2) then run location inference on this updated
version.

Adding layout information involves 3 steps:

(1) Convert DDefs to `WithLayout DDefs` (we don't have a separate type for those yet).

(2) All data constructors that should have indirection pointers are updated.
    And the indirections are added at appropriate places (before all other arguments so that they're
    written immediately after the tag).

(3) Case expressions are modified to work with the modified data constructors.
    Pattern matches for these constructors now bind the additional size fields too.

For example,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                          [ ("Leaf",[(False,IntTy)])
                          , ("Node",[ (False,PackedTy "Tree" ())
                                    , (False,PackedTy "Tree" ())])
                          ]]

becomes,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                         [ ("Leaf"   ,[(False,IntTy)])
                         , ("Node",  [ (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         , ("Node^", [ (False, CursorTy) -- indirection pointer
                                     , (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         ]]
-}

--------------------------------------------------------------------------------

-- | Add layout information to the program, but only if required
repairProgram :: DynFlags -> Prog -> L2.Prog -> SyM L2.Prog
repairProgram dflags oldl1 prg =
  if repair
  then if (gopt Opt_Gibbon1 dflags)
       then repairGibbon1
       else repairGibbon2
  else return prg
  where
    (repair,fns) = needsLayout prg

    repairGibbon1 =
      dbgTrace 5 ("Runing AddTraversals") <$> do
        l1 <- addTraversals fns oldl1
        l2 <- inferLocs l1
        l2 <- flattenL2 l2
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

-- Maybe we should use the Continuation monad here..
needsLayout :: L2.Prog -> (Bool, S.Set Var)
needsLayout (L2.Prog ddefs fundefs mainExp) =
  let env2 = Env2 M.empty (L2.initFunEnv fundefs)
      specialfns = L.foldl' (\acc fn -> if isSpecialFn ddefs fn
                                        then S.insert (L2.funname fn) acc
                                        else acc)
                   S.empty (M.elems fundefs)
      mainExp' = case mainExp of
                   Nothing -> False
                   Just (mn, _) -> needsLayoutExp ddefs fundefs False specialfns S.empty env2 mn
      fnsneedlayout = M.map (\L2.FunDef{L2.funname,L2.funbod} ->
                               if funname `S.member` specialfns
                               then False
                               else needsLayoutExp ddefs fundefs False specialfns S.empty env2 funbod)
                      fundefs
  in (mainExp' || (L.any id (M.elems fnsneedlayout)), (S.fromList $ M.keys $ M.filter id fnsneedlayout))

needsLayoutExp :: DDefs L2.Ty2 -> L2.NewFuns -> Bool -> S.Set Var -> S.Set LocVar
               -> Env2 L2.Ty2 -> L L2.Exp2 -> Bool
needsLayoutExp ddefs fundefs base special traversed env2 (L _ ex) = base ||
  case ex of
    VarE{}    -> base
    LitE{}    -> base
    LitSymE{} -> base
    AppE f _ arg  ->
      let argty = gTypeExp ddefs env2 arg
          g = if f `S.member` special then specialTraversal else fnTraversal
          (traversed', base') = g traversed (fundefs # f) (L2.getTyLocs argty)
          base'' = base || base'
      in (needsLayoutExp ddefs fundefs base'' special traversed' env2 arg)
    PrimAppE{} -> base
    LetE (v,_,ty, L _ (AppE f _ arg)) bod ->
      let argty = gTypeExp ddefs env2 arg
          g = if f `S.member` special then specialTraversal else fnTraversal
          (traversed', base') = g traversed (fundefs # f) (L2.getTyLocs argty)
          base'' = base || base'
      in (needsLayoutExp ddefs fundefs base'' special traversed' env2 arg) ||
         (needsLayoutExp ddefs fundefs base'' special traversed' (extendVEnv v ty env2) bod)
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
    MapE{}  -> error $ "needsLayoutExp: TODO MapE"
    FoldE{} -> error $ "needsLayoutExp: TODO FoldE"
  where
    go = needsLayoutExp ddefs fundefs base special traversed

    docase :: S.Set LocVar -> Env2 L2.Ty2
           -> (DataCon, [(Var,LocVar)], L L2.Exp2) -> Bool
    docase traversed1 env21 (dcon,vlocs,bod) =
      let (vars,locs) = unzip vlocs
          tys = lookupDataCon ddefs dcon
          tys' = substLocs locs tys []
          env2' = extendsVEnv (M.fromList $ zip vars tys') env21
      in (needsLayoutExp ddefs fundefs base special traversed1 env2' bod)

    substLocs :: [LocVar] -> [L2.Ty2] -> [L2.Ty2] -> [L2.Ty2]
    substLocs locs tys acc =
      case (locs,tys) of
        ([],[]) -> acc
        (lc':rlocs, ty:rtys) ->
          case ty of
            PackedTy tycon _ -> substLocs rlocs rtys (acc ++ [PackedTy tycon lc'])
            ProdTy tys' -> error $ "substLocs: Unexpected type: " ++ sdoc tys'
            _ -> substLocs rlocs rtys (acc ++ [ty])
        _ -> error $ "substLocs: " ++ sdoc (locs,tys)

isSpecialFn :: DDefs L2.Ty2 -> L2.FunDef -> Bool
isSpecialFn ddefs L2.FunDef{L2.funty, L2.funbod} =
  if traversesAllInputs
  then True
  else go (S.fromList $ L2.inLocVars funty) funbod
  where
    traversesAllInputs =
      length (L2.inLocVars funty) == length (S.toList $ L2.arrEffs funty)

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
      -- It's special if it has some packed elements which cannot be accessed,
      -- but those are unused
      in all (\v -> not $ L2.occurs v bod) needtraversal

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

fnTraversal :: S.Set Var -> L2.FunDef -> [LocVar] -> (S.Set LocVar, Bool)
fnTraversal traversed L2.FunDef{L2.funty} locs =
  let funeff = L2.arrEffs funty
      inlocs = L2.inLocVars funty
      substMap = M.fromList $ zip inlocs locs
      funeff' = L2.substEffs substMap funeff
  in ( S.union (S.map (\(L2.Traverse a) -> a) funeff') traversed
     , length inlocs /= length (S.toList funeff')
     )

-- Some functions are special (eg. leftmost). They don't traverse their input,
-- but they can be compiled without adding any layout information to the program.
-- To return the correct value from `needsLayoutExp`, we mark all input
-- locations at the call site of such functions as "traversed".
specialTraversal :: S.Set Var -> L2.FunDef -> [LocVar] -> (S.Set LocVar, Bool)
specialTraversal traversed L2.FunDef{L2.funty} locs =
  let fninlocs = L2.inLocVars funty
      inlocs = L.take (length fninlocs) locs
  in (S.union (S.fromList inlocs) traversed, False)

--------------------------------------------------------------------------------

-- Operates on an L1 program, and updates it to have layout information

addLayout :: Prog -> SyM Prog
addLayout prg@Prog{ddefs,fundefs,mainExp} = do
  let iddefs = toIndrDDefs ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just ex -> fmap Just (addLayoutExp iddefs ex)
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: DDefs Ty1 -> L1.FunDef -> SyM L1.FunDef
addLayoutFun ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp ddfs funBody
  return $ fd{funBody = bod}

addLayoutExp :: Out a => DDefs (UrTy a) -> L Exp1 -> SyM (L Exp1)
addLayoutExp ddfs (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        Just n  -> do
          let tys = lookupDataCon ddfs dcon
              packedOnly = L.map snd $
                           L.filter (\(ty,_) -> isPackedTy ty) (zip tys args)
              needSizeOf = L.take n packedOnly
          szs <- mapM (\arg -> do
                         v <- gensym "indr"
                         return (v,[],CursorTy, l$ PrimAppE PEndOf [arg]))
                 needSizeOf
          let szVars = L.map (\(v,_,_,_) -> v) szs
              szExps = L.map (l . VarE) szVars
          return $ unLoc $ mkLets szs (l$ DataConE loc (toIndrDataCon dcon) (szExps ++ args))
        Nothing -> return ex

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> addLayoutExp ddfs bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    CaseE scrt mp -> CaseE scrt <$> mapM docase mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    Ext _ -> return ex
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addLayoutExp ddfs

    docase :: (DataCon, [(Var,())], L Exp1) -> SyM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numIndrsDataCon ddfs dcon of
        Just n -> do
          szVars <- mapM (\_ -> (, ()) <$> gensym "sz") [1..n]
          (toIndrDataCon dcon, szVars ++ vs,) <$> go bod
        Nothing -> (dcon,vs,) <$> go bod

-- | Add "sized" constructors to the data definition
toIndrDDefs :: Out a => DDefs (UrTy a) -> Map Var (DDef (UrTy a))
toIndrDDefs ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef a
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numIndrsDataCon ddfs dcon of
                                Just n -> let tys'  = [(False,CursorTy) | _ <- [1..n]] ++ tys
                                              dcon' = toIndrDataCon dcon
                                          in [(dcon,tys), (dcon',tys')] ++ acc
                                Nothing -> (dcon,tys) : acc
                              )
                   [] dataCons
      in dd {dataCons = dcons'}


--------------------------------------------------------------------------------
-- Old repair strategy: Add traversals

addTraversals :: S.Set Var -> Prog -> SyM Prog
addTraversals unsafeFns prg@Prog{ddefs,fundefs,mainExp} =
  dbgTrace 5 ("AddTraversals: Fixing functions:" ++ sdoc unsafeFns) <$> do
    funs <- mapM (\(nm,f) -> (nm,) <$> addTraversalsFn unsafeFns ddefs f) (M.toList fundefs)
    mainExp' <-
      case mainExp of
        Just ex -> fmap Just (addTraversalsExp ddefs ex)
        Nothing -> return Nothing
    return prg { ddefs = ddefs
               , fundefs = M.fromList funs
               , mainExp = mainExp'
               }


-- Process body and reset traversal effects.
addTraversalsFn :: S.Set Var -> DDefs Ty1 -> L1.FunDef -> SyM L1.FunDef
addTraversalsFn unsafeFns ddefs f@FunDef{funName, funBody} =
  if funName `S.member` unsafeFns
  then do
    bod' <- addTraversalsExp ddefs funBody
    return $ f {funBody = bod'}
  else return f

-- Generate traversals for the first (n-1) packed elements
addTraversalsExp :: DDefs Ty1-> L Exp1 -> SyM (L Exp1)
addTraversalsExp ddefs (L p ex) = L p <$>
  case ex of
    CaseE scrt brs -> CaseE scrt <$> mapM docase brs

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    LitSymE{} -> return ex
    AppE f locs arg -> AppE f locs <$> go arg
    PrimAppE f args -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> go bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    DataConE{} -> return ex
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    Ext _ -> return ex
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addTraversalsExp ddefs
    docase (dcon,vlocs,rhs) = do
      let tys = lookupDataCon ddefs dcon
          (vars,_) = unzip vlocs
          -- First (n-1) packed elements
          packedOnly = L.filter (\(_,ty) -> isPackedTy ty) (zip vars tys)
      case packedOnly of
        [] -> (dcon,vlocs,) <$> go rhs
        _ -> do
          let ls = init packedOnly
          travbinds <- mapM (\(v,ty) -> do
                               let PackedTy dc _ = ty
                                   copyfn = mkCopyFunName dc
                               v' <- gensym v
                               return (v',[], ty, l$ AppE copyfn [] (l$ VarE v)))
                       ls
          (dcon,vlocs,) <$> mkLets travbinds <$> go rhs
