module Gibbon.Passes.AddLayout
  (addLayout, numIndrsDataCon, needsLayout) where

import Control.Monad (when)
import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Maybe (fromJust)
import Data.Set as S
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Passes.AddTraversals (needsTraversal)
import Gibbon.L1.Syntax as L1
import Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

{- Note [Adding layout information]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot add layout information to an L2 program, as it would distort the locations
inferred by the previous analysis. Instead, (1) we use the old L1 program and
add layout information to that, (2) then run location inference again.

Adding layout information involves 3 steps:

(1) Convert DDefs to `WithLayout DDefs` (we don't have a separate type for those yet).

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

-}

{- Note [Reusing random access nodes in case expressions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a data constructor occurs inside a case expression, we might already have a
random access node for a variable that was bound in the pattern. In that case, we don't want
to request yet another one using PEndOf. Consider this example:

    (fn ...
      (case tr
        [(Node^ [(indr_y, _) (x, _), (y, _)]
           (DataConE __HOLE x (fn y)))]))

Here, we don't want to fill the HOLE with (PEndOf x). Instead, we should reuse indr_y.

-}

--------------------------------------------------------------------------------

type IndrEnv = M.Map Var Var

-- | Operates on an L1 program, and updates it to have random access nodes.
--
-- Previous analysis determines which data types require it ('needsLayout').
addLayout :: S.Set TyCon -> Prog1 -> PassM Prog1
addLayout tycons prg@Prog{ddefs,fundefs,mainExp} = do
  dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags
  when dump_op $
    dbgTrace 2 ("Adding random access nodes: " ++ sdoc (S.toList tycons)) (return ())
  let iddefs = withRanDDefs tycons ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addLayoutFun tycons iddefs f) (M.toList fundefs)
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addLayoutExp tycons iddefs M.empty ex
      Nothing -> return Nothing
  return prg { ddefs = iddefs
             , fundefs = M.fromList funs
             , mainExp = mainExp'
             }

addLayoutFun :: S.Set TyCon -> DDefs Ty1 -> L1.FunDef1 -> PassM L1.FunDef1
addLayoutFun tycons ddfs fd@FunDef{funBody} = do
  bod <- addLayoutExp tycons ddfs M.empty funBody
  return $ fd{funBody = bod}

addLayoutExp :: S.Set TyCon -> DDefs Ty1 -> IndrEnv -> L Exp1 -> PassM (L Exp1)
addLayoutExp tycons ddfs ienv (L p ex) = L p <$>
  case ex of
    DataConE loc dcon args ->
      case numIndrsDataCon ddfs dcon of
        0 -> return ex
        n ->
          let tycon = getTyOfDataCon ddfs dcon
          -- Only add random access nodes to the data types that need it.
          in if not (tycon `S.member` tycons)
             then return ex
             else do
          let tys = lookupDataCon ddfs dcon
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              -- n elements after the first packed one require indirections.
              needIndrsFor = L.take n $ L.drop firstPacked args

          indrs <- mapM (\arg -> do
                           i <- gensym "indr"
                           -- See Note [Reusing indirections in case expressions]
                           let rhs = case unLoc arg of
                                       VarE x -> case M.lookup x ienv of
                                                   Just v -> VarE v
                                                   Nothing -> PrimAppE PEndOf [arg]
                                       _ -> PrimAppE PEndOf [arg]
                           return (i,[],CursorTy, l$ rhs))
                   needIndrsFor

          let indrArgs = L.map (\(v,_,_,_) -> l$ VarE v) indrs
          return $ unLoc $ mkLets indrs (l$ DataConE loc (toIndrDataCon dcon) (indrArgs ++ args))

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
    MapE{}  -> error "addLayoutExp: TODO MapE"
    FoldE{} -> error "addLayoutExp: TODO FoldE"

  where
    go = addLayoutExp tycons ddfs ienv

    docase :: (DataCon, [(Var,())], L Exp1) -> PassM (DataCon, [(Var,())], L Exp1)
    docase (dcon,vs,bod) = do
      case numIndrsDataCon ddfs dcon of
        0 -> (dcon,vs,) <$> go bod
        n ->
          let tycon = getTyOfDataCon ddfs dcon
          -- Not all types have random access nodes.
          in if not (tycon `S.member` tycons)
             then (dcon,vs,) <$> go bod
             else do
          indrVars <- mapM (\_ -> gensym "indr") [1..n]
          let tys = lookupDataCon ddfs dcon
              -- See Note [Reusing indirections in case expressions]
              -- We update the environment to track indirections of the
              -- variables bound by this pattern.
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              haveIndrsFor = L.take n $ L.drop firstPacked $ L.map fst vs
              ienv' = M.union ienv (M.fromList $ zip haveIndrsFor indrVars)
          (toIndrDataCon dcon, (L.map (,()) indrVars) ++ vs,) <$> addLayoutExp tycons ddfs ienv' bod

-- | Update data type definitions to include random access nodes.
withRanDDefs :: Out a => S.Set TyCon -> DDefs (UrTy a) -> Map Var (DDef (UrTy a))
withRanDDefs tycons ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef b
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numIndrsDataCon ddfs dcon of
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
numIndrsDataCon :: Out a => DDefs (UrTy a) -> DataCon -> Int
numIndrsDataCon ddfs dcon =
  case L.findIndex isPackedTy tys of
    Nothing -> 0
    Just firstPacked -> (length tys) - firstPacked - 1
  where tys = lookupDataCon ddfs dcon

--------------------------------------------------------------------------------

-- | Collect all data types that need layout information to be compiled.
--
-- If any pattern 'needsTraversal' so that we can unpack it, we mark the type of the
-- scrutinee as something that needs layout information.
needsLayout :: Prog2 -> S.Set TyCon
needsLayout Prog{ddefs,fundefs,mainExp} =
  let dofun FunDef{funArg,funTy,funBody} =
        let tyenv = M.singleton funArg (inTy funTy)
        in needsLayoutExp ddefs fundefs tyenv funBody

      funs = M.foldr (\f acc -> acc `S.union` dofun f) S.empty fundefs

      mn   = case mainExp of
               Nothing -> S.empty
               Just (e,_ty) -> needsLayoutExp ddefs fundefs M.empty e
  in S.union funs mn

needsLayoutExp :: DDefs Ty2 -> FunDefs2 -> TyEnv Ty2 -> L Exp2 -> S.Set TyCon
needsLayoutExp ddefs fundefs tyenv (L _p ex) =
  case ex of
    CaseE (L _ (VarE scrt)) brs -> if docase brs
                                   then let PackedTy tycon _ = tyenv # scrt
                                        in S.singleton tycon
                                   else S.empty
    CaseE scrt _ -> error $ "needsLayoutExp: Scrutinee is not flat " ++ sdoc scrt

    -- Standard recursion here (ASSUMPTION: everything is flat)
    VarE{}     -> S.empty
    LitE{}     -> S.empty
    LitSymE{}  -> S.empty
    -- We do not process the function body here, assuming that the main analysis does it.
    AppE{}     -> S.empty
    PrimAppE{} -> S.empty
    LetE(v,_,ty,rhs) bod -> go rhs `S.union`
                            needsLayoutExp ddefs fundefs (M.insert v ty tyenv) bod
    IfE _a b c -> go b `S.union` go c
    MkProdE{}  -> S.empty
    ProjE{}    -> S.empty
    DataConE{} -> S.empty
    TimeIt{}   -> S.empty
    ParE a b   -> go a `S.union` go b
    Ext ext ->
      case ext of
        LetRegionE _ bod -> go bod
        LetLocE _ _ bod  -> go bod
        _ -> S.empty
    MapE{}     -> S.empty
    FoldE{}    -> S.empty
  where
    go = needsLayoutExp ddefs fundefs tyenv

    -- Short circuit the computation if any of the branches needs traversals.
    docase [] = False
    docase (br:brs) = case needsTraversal ddefs fundefs tyenv br of
                        Just _ls -> True
                        Nothing  -> docase brs
