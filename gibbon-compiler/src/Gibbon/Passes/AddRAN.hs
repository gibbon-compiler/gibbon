module Gibbon.Passes.AddRAN
  (addRAN, numRANsDataCon, needsRAN) where

import Control.Monad ( when )
import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Maybe ( fromJust )
import Data.Set as S
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Passes.AddTraversals ( needsTraversal )
import Gibbon.L1.Syntax
import Gibbon.L2.Syntax

{-

Note [Adding random access nodes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot add RAN's to an L2 program, as it would distort the locations
inferred by the previous analysis. Instead, (1) we use the old L1 program and
add RAN's to that, (2) then run location inference again.

Adding RAN's requires 3 steps:

(1) Convert DDefs to `WithRAN DDefs` (we don't have a separate type for those yet).

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
                         , ("Node^", [ (False, CursorTy) -- random access node
                                     , (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         ]]

(2) Update all data constructors that now need to write additional random access nodes
    (before all other arguments so that they're written immediately after the tag).

(3) Case expressions are modified to work with these updated data constructors.
    Pattern matches for these constructors now bind the additional
    random access nodes too.


Note [Reusing RAN's in case expressions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a data constructor occurs inside a case expression, we might already have a
random access node for a variable that was bound in the pattern. In that case, we don't want
to request yet another one using PEndOf. Consider this example:

    (fn ...
      (case tr
        [(Node^ [(indr_y, _) (x, _), (y, _)]
           (DataConE __HOLE x (fn y)))]))

Here, we don't want to fill the HOLE with (PEndOf x). Instead, we should reuse indr_y.


Note [When does a type 'needsRAN']
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(1) If any pattern 'needsTraversal' so that we can unpack it, we mark the type of the
    scrutinee as something that needs RAN's.

-OR-

(2) Consider the following prgram which uses the parallel tuple combinator to
    parallelize the 'sumtree' function:

        sumtree :: Tree -> Int
        sumtree tr = case tr of
                       Leaf n   -> n
                       Node l r -> let tup : (Int, Int) = (sumtree l) || (sumtree r)
                                   in (#0 tup) + (#1 tup)

   To execute sumtree on both sub-trees in parallel, the program should be able
   access them simultaneously (which is not possbile without RAN's). In general,
   if the tuple combinator functions operate on values that reside in the same
   region, RAN's are required for those values.

-}

--------------------------------------------------------------------------------

type IndrEnv = M.Map Var Var

-- | Operates on an L1 program, and updates it to have random access nodes.
--
-- Previous analysis determines which data types require it ('needsLRAN).
addRAN :: S.Set TyCon -> Prog1 -> PassM Prog1
addRAN tycons prg@Prog{ddefs,fundefs,mainExp} = do
  dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags
  when dump_op $
    dbgTrace 2 ("Adding random access nodes: " ++ sdoc (S.toList tycons)) (return ())
  let iddefs = withRANDDefs tycons ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addRANFun tycons iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addRANExp tycons iddefs M.empty ex
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addRANFun :: S.Set TyCon -> DDefs Ty1 -> FunDef1 -> PassM FunDef1
addRANFun tycons ddfs fd@FunDef{funBody} = do
  bod <- addRANExp tycons ddfs M.empty funBody
  return $ fd{funBody = bod}

addRANExp :: S.Set TyCon -> DDefs Ty1 -> IndrEnv -> L Exp1 -> PassM (L Exp1)
addRANExp tycons ddfs ienv (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numRANsDataCon ddfs dcon of
        0 -> return ex
        n ->
          let tycon = getTyOfDataCon ddfs dcon
          -- Only add random access nodes to the data types that need it.
          in if not (tycon `S.member` tycons)
             then return ex
             else do
          let tys = lookupDataCon ddfs dcon
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              -- n elements after the first packed one require RAN's.
              needIndrsFor = L.take n $ L.drop firstPacked args

          rans <- mapM (\arg -> do
                           i <- gensym "indr"
                           -- See Note [Reusing RAN's in case expressions]
                           let rhs = case unLoc arg of
                                       VarE x -> case M.lookup x ienv of
                                                   Just v -> VarE v
                                                   Nothing -> PrimAppE PEndOf [arg]
                                       _ -> PrimAppE PEndOf [arg]
                           return (i,[],CursorTy, l$ rhs))
                   needIndrsFor

          let indrArgs = L.map (\(v,_,_,_) -> l$ VarE v) rans
          return $ unLoc $ mkLets rans (l$ DataConE loc (toIndrDataCon dcon) (indrArgs ++ args))

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
    CaseE scrt mp -> CaseE scrt <$> mapM docase mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    ParE a b -> ParE <$> (go a) <*> go b
    Ext _ -> return ex
    MapE{}  -> error "addRANExp: TODO MapE"
    FoldE{} -> error "addRANExp: TODO FoldE"

  where
    go = addRANExp tycons ddfs ienv

    docase :: (DataCon, [(Var,())], L Exp1) -> PassM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numRANsDataCon ddfs dcon of
        0 -> (dcon,vs,) <$> go bod
        n ->
          let tycon = getTyOfDataCon ddfs dcon
          -- Not all types have random access nodes.
          in if not (tycon `S.member` tycons)
             then (dcon,vs,) <$> go bod
             else do
          ranVars <- mapM (\_ -> gensym "ran") [1..n]
          let tys = lookupDataCon ddfs dcon
              -- See Note [Reusing RAN's in case expressions]
              -- We update the environment to track RAN's of the
              -- variables bound by this pattern.
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              haveIndrsFor = L.take n $ L.drop firstPacked $ L.map fst vs
              ienv' = M.union ienv (M.fromList $ zip haveIndrsFor ranVars)
          (toIndrDataCon dcon, (L.map (,()) ranVars) ++ vs,) <$> addRANExp tycons ddfs ienv' bod

-- | Update data type definitions to include random access nodes.
withRANDDefs :: Out a => S.Set TyCon -> DDefs (UrTy a) -> Map Var (DDef (UrTy a))
withRANDDefs tycons ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef b
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numRANsDataCon ddfs dcon of
                                0 -> (dcon,tys) : acc
                                n -> -- Not all types have random access nodes.
                                     if not (getTyOfDataCon ddfs dcon `S.member` tycons)
                                     then (dcon,tys) : acc
                                     else
                                       let tys'  = [(False,CursorTy) | _ <- [1..n]] ++ tys
                                           dcon' = toIndrDataCon dcon
                                       in [(dcon,tys), (dcon',tys')] ++ acc)
                   [] dataCons
      in dd {dataCons = dcons'}


-- | The number of nodes needed by a 'DataCon' for full random access
-- (which is equal the number of arguments occurring after the first packed type).
--
numRANsDataCon :: Out a => DDefs (UrTy a) -> DataCon -> Int
numRANsDataCon ddfs dcon =
  case L.findIndex isPackedTy tys of
    Nothing -> 0
    Just firstPacked -> (length tys) - firstPacked - 1
  where tys = lookupDataCon ddfs dcon

--------------------------------------------------------------------------------

-- See Note [When does a type 'needsLRAN]
-- | Collect all types that need random access nodes to be compiled.
needsRAN :: Prog2 -> S.Set TyCon
needsRAN Prog{ddefs,fundefs,mainExp} =
  let funenv = initFunEnv fundefs
      dofun FunDef{funArg,funTy,funBody} =
        let tyenv = M.singleton funArg (inTy funTy)
            env2 = Env2 tyenv funenv
            renv = M.fromList $ L.map (\lrm -> (lrmLoc lrm, regionToVar (lrmReg lrm)))
                                      (locVars funTy)
        in needsRANExp ddefs fundefs env2 renv funBody

      funs = M.foldr (\f acc -> acc `S.union` dofun f) S.empty fundefs

      mn   = case mainExp of
               Nothing -> S.empty
               Just (e,_ty) -> let env2 = Env2 M.empty funenv
                               in needsRANExp ddefs fundefs env2 M.empty e
  in S.union funs mn

-- Maps a location to a region
type RegEnv = M.Map LocVar Var

needsRANExp :: DDefs Ty2 -> FunDefs2 -> Env2 Ty2 -> RegEnv -> L Exp2 -> S.Set TyCon
needsRANExp ddefs fundefs env2 renv (L _p ex) =
  case ex of
    CaseE (L _ (VarE scrt)) brs -> let PackedTy tycon tyloc = lookupVEnv scrt env2
                                       reg = renv # tyloc
                                   in S.unions $ L.map (docase tycon reg env2 renv) brs

    CaseE scrt _ -> error $ "needsRANExp: Scrutinee is not flat " ++ sdoc scrt

    -- Standard recursion here (ASSUMPTION: everything is flat)
    VarE{}     -> S.empty
    LitE{}     -> S.empty
    LitSymE{}  -> S.empty
    -- We do not process the function body here, assuming that the main analysis does it.
    AppE{}     -> S.empty
    PrimAppE{} -> S.empty
    LetE(v,_,ty,rhs) bod -> go rhs `S.union`
                            needsRANExp ddefs fundefs (extendVEnv v ty env2) renv bod
    IfE _a b c -> go b `S.union` go c
    MkProdE{}  -> S.empty
    ProjE{}    -> S.empty
    DataConE{} -> S.empty
    TimeIt{}   -> S.empty
    -- See (2) in Note [When does a type 'needsLRAN].
    ParE a b   -> let mp1 = parAppLoc env2 a
                      mp2 = parAppLoc env2 b
                      locs1 = M.keys mp1
                      locs2 = M.keys mp2
                      regs1 = S.fromList (L.map (renv #) locs1)
                      regs2 = S.fromList (L.map (renv #) locs2)
                      -- The regions used in BOTH parts of the tuple combinator --
                      -- all values residing in these regions would need RAN's.
                      common_regs = S.intersection regs1 regs2
                  in if S.null common_regs
                     then S.empty
                     else let -- Get all the locations in 'common_regs'.
                              want_ran_locs = L.filter (\lc -> (renv # lc) `S.member` common_regs) (locs1 ++ locs2)
                              common_mp = mp1 `M.union` mp2
                          in S.fromList $ L.map (\lc -> common_mp # lc) want_ran_locs
    Ext ext ->
      case ext of
        LetRegionE _ bod -> go bod
        LetLocE loc rhs bod  ->
            let reg = case rhs of
                        StartOfLE r  -> regionToVar r
                        InRegionLE r -> regionToVar r
                        AfterConstantLE _ lc -> renv # lc
                        AfterVariableLE _ lc -> renv # lc
                        FromEndLE lc         -> renv # lc -- TODO: This needs to be fixed
            in needsRANExp ddefs fundefs env2 (M.insert loc reg renv) bod
        _ -> S.empty
    MapE{}     -> S.empty
    FoldE{}    -> S.empty
  where
    go = needsRANExp ddefs fundefs env2 renv

    -- Collect all the 'Tycon's which might random access nodes
    docase tycon reg env21 renv1 br@(dcon,vlocs,bod) =
      let (vars,locs) = unzip vlocs
          renv' = L.foldr (\lc acc -> M.insert lc reg acc) renv1 locs
          tys = lookupDataCon ddefs dcon
          tys' = substLocs' locs tys
          env2' = extendsVEnv (M.fromList $ zip vars tys') env21
          ran_for_scrt = if L.null (needsTraversal ddefs fundefs env2 br)
                            then S.empty
                            else S.singleton tycon
      in ran_for_scrt `S.union` needsRANExp ddefs fundefs env2' renv' bod

    -- Return the location and tycon of an argument to a function call.
    parAppLoc :: Env2 Ty2 -> L Exp2 -> M.Map LocVar TyCon
    parAppLoc env21 (L _ (AppE _ _ arg)) =
      let fn (PackedTy dcon loc) = [(loc, dcon)]
          fn (ProdTy tys) = L.concatMap fn tys
          fn _ = []
      in M.fromList (fn $ gRecoverType ddefs env21 arg)
    parAppLoc _ oth = error $ "parAppLoc: Cannot handle "  ++ sdoc oth
