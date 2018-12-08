{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- | An intermediate language with an effect system that captures traversals.

module Gibbon.L2.Syntax
    (
    -- * Extended language L2 with location types.
      E2Ext(..)
    , Prog2, FunDef2, FunDefs2, Exp2, E2, Ty2
    , Effect(..), ArrowTy2(..) , LocRet(..), LocExp, PreLocExp(..)

    -- * Regions and locations
    , LocVar, Region(..), Modality(..), LRM(..), dummyLRM
    , Multiplicity(..), regionToVar

    -- * Operations on types
    , allLocVars, inLocVars, outLocVars, outRegVars, inRegVars, substLoc
    , substLoc', substLocs, substLocs', substEffs, prependArgs, stripTyLocs
    , locsInTy

    -- * Other helpers
    , revertToL1, occurs, mapPacked, depList

    , module Gibbon.Language
    )
    where

import Control.DeepSeq
import Data.List as L
import Data.Loc
import Data.Set as S
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.Language
import Text.PrettyPrint.HughesPJ
import Gibbon.L1.Syntax

--------------------------------------------------------------------------------

type Prog2 = Prog (L Exp2)

type FunDef2 = FunDef (L Exp2)

type FunDefs2 = FunDefs (L Exp2)

-- | Function types know about locations and traversal effects.
instance FunctionTy Ty2 where
  type ArrowTy Ty2 = ArrowTy2
  inTy = arrIn
  outTy = arrOut

-- | Extended expressions, L2.
--
--   By adding a `LocVar` decoration, all data constructors,
--   applications, and bindings gain a location annotation.
type Exp2 = E2 LocVar Ty2

-- | L1 Types extended with abstract Locations.
type Ty2 = UrTy LocVar

--------------------------------------------------------------------------------

-- | Shorthand for recursions.
type E2 l d = PreExp E2Ext l d

-- | The extension that turns L1 into L2.
data E2Ext loc dec =
    LetRegionE Region                 (L (E2 loc dec)) -- ^ Not used until later on.
  | LetLocE    loc    (PreLocExp loc) (L (E2 loc dec)) -- ^ Bind a new location.
  | RetE [loc] Var     -- ^ Return a value together with extra loc values.
  | FromEndE loc -- ^ Bind a location from an EndOf location (for RouteEnds and after)
  | BoundsCheck Int loc loc  -- ^ Bytes required, region, write cursor
  | IndirectionE TyCon DataCon (loc,Var) (loc,Var) (L (E2 loc dec)) -- ^ An tagged indirection node
 deriving (Show, Ord, Eq, Read, Generic, NFData)

-- | Define a location in terms of a different location.
data PreLocExp loc = StartOfLE Region
                   | AfterConstantLE Int -- Number of bytes after.
                                    loc  -- Location which this location is offset from.
                   | AfterVariableLE Var -- Name of variable v. This loc is size(v) bytes after.
                                    loc  -- Location which this location is offset from.
                   | InRegionLE Region
                   | FromEndLE  loc
                     deriving (Read, Show, Eq, Ord, Generic, NFData)

type LocExp = PreLocExp LocVar

-- | Locations (end-witnesses) returned from functions after RouteEnds.
data LocRet = EndOf LRM
              deriving (Read, Show, Eq, Ord, Generic, NFData)


instance FreeVars (E2Ext l d) where
  gFreeVars e =
    case e of
     LetRegionE _ bod   -> gFreeVars bod
     LetLocE _ _rhs bod -> -- gFreeVars rhs `S.union`
                           gFreeVars bod
     RetE _ vr          -> S.singleton vr
     FromEndE _         -> S.empty
     BoundsCheck{}      -> S.empty
     IndirectionE{}     -> S.empty


instance (Out l, Out d, Show l, Show d) => Expression (E2Ext l d) where
  type LocOf (E2Ext l d) = l
  type TyOf (E2Ext l d)  = d
  isTrivial e =
    case e of
      LetRegionE{} -> False
      LetLocE{}    -> False
      RetE{}       -> False -- Umm... this one could be potentially.
      FromEndE{}   -> True
      BoundsCheck{}-> False
      IndirectionE{} -> False

instance (Out l, Show l, Typeable (L (E2 l (UrTy l)))) => Typeable (E2Ext l (UrTy l)) where
  gTypeExp ddfs env2 ex =
    case ex of
      LetRegionE _r bod   -> gTypeExp ddfs env2 bod
      LetLocE _l _rhs bod -> gTypeExp ddfs env2 bod
      RetE _loc var       -> case M.lookup var (vEnv env2) of
                               Just ty -> ty
                               Nothing -> error $ "gTypeExp: unbound variable " ++ sdoc var
      FromEndE _loc       -> error $ "Shouldn't enconter FromEndE in tail position"
      BoundsCheck{}       -> error $ "Shouldn't enconter BoundsCheck in tail position"
      IndirectionE tycon _ _ (to,_) _ -> PackedTy tycon to


instance (Out l, Show l, Typeable (L (E2 l (UrTy l))),
          TyOf (E2Ext l (UrTy l)) ~ TyOf (L (E2Ext l (UrTy l))),
          Expression (L (E2Ext l (UrTy l))))
         => Typeable (L (E2Ext l (UrTy l))) where
  gTypeExp ddfs env2 (L _ ex) = gTypeExp ddfs env2 ex


instance (Typeable (E2Ext l (UrTy l)),
          Expression (E2Ext l (UrTy l)),
          Flattenable (L (E2 l (UrTy l))))
      => Flattenable (E2Ext l (UrTy l)) where

  gFlattenGatherBinds ddfs env ex =
      case ex of
          LetRegionE r bod -> do (bnds,bod') <- go bod
                                 return $ ([], LetRegionE r $ flatLets bnds bod')

          LetLocE l rhs bod -> do (bnds,bod') <- go bod
                                  return $ ([], LetLocE l rhs $ flatLets bnds bod')

          RetE{}        -> return ([],ex)
          FromEndE{}    -> return ([],ex)
          BoundsCheck{} -> return ([],ex)
          IndirectionE{}-> return ([],ex)

    where go = gFlattenGatherBinds ddfs env

  gFlattenExp ddfs env ex = do (_b,e') <- gFlattenGatherBinds ddfs env ex
                               return e'

-- | Our type for functions grows to include effects, and explicit universal
-- quantification over location/region variables.
data ArrowTy2 = ArrowTy2
    { locVars :: [LRM]       -- ^ Universally-quantified location params.
                             -- Only these should be referenced in arrIn/arrOut.
    , arrIn :: Ty2           -- ^ Input type for the function.
    , arrEffs:: (Set Effect) -- ^ These are present-but-empty initially,
                             -- and the populated by InferEffects.
    , arrOut:: Ty2           -- ^ Output type for the function.
    , locRets :: [LocRet]    -- ^ L2B feature: multi-valued returns.
    }
  deriving (Read,Show,Eq,Ord, Generic, NFData)

-- | The side-effect of evaluating a function.
data Effect = Traverse LocVar
              -- ^ The function, during its execution, traverses all
              -- of the value living at this location.
  deriving (Read,Show,Eq,Ord, Generic, NFData)

--------------------------------------------------------------------------------
--
-- See https://github.com/iu-parfunc/gibbon/issues/79 for more details
-- | Region variants (multiplicities)
data Multiplicity
    = Bounded     -- ^ Contain a finite number of values and can be
                  --   stack-allocated.

    | Infinite    -- ^ Consist of a linked list of buffers, spread
                  --   throughout memory (though possible constrained
                  --   to 4GB regions). Writing into these regions requires
                  --   bounds-checking. The buffers can start very small
                  --   at the head of the list, but probably grow
                  --   geometrically in size, making the cost of traversing
                  --   all of them logarithmic.

    | BigInfinite -- ^ These regions are infinite, but also have the
                  --   expectation of containing many values. Thus we give
                  --   them large initial page sizes. This is also could be
                  --   the appropriate place to use mmap to grow the region
                  --   and to establish guard places.
  deriving (Read,Show,Eq,Ord,Generic)

instance Out Multiplicity where
  doc = text . show

instance NFData Multiplicity where
  rnf _ = ()

-- | An abstract region identifier.  This is used inside type signatures and elsewhere.
data Region = GlobR Var Multiplicity -- ^ A global region with lifetime equal to the
                                     --   whole program.
            | DynR Var Multiplicity  -- ^ A dynamic region that may be created or
                                     --   destroyed, tagged by an identifier.
            | VarR Var               -- ^ A region metavariable that can range over
                                     --   either global or dynamic regions.
            | MMapR Var              -- ^ A region that doesn't result in an (explicit)
                                     --   memory allocation. It merely ensures that there
                                     --   are no free locations in the program.
  deriving (Read,Show,Eq,Ord, Generic)

instance Out Region

instance NFData Region where
  rnf (GlobR v _) = rnf v
  rnf (DynR v _)  = rnf v
  rnf (VarR v)    = rnf v
  rnf (MMapR v)   = rnf v

-- | The modality of locations and cursors: input/output, for reading
-- and writing, respectively.
data Modality = Input | Output
  deriving (Read,Show,Eq,Ord, Generic)
instance Out Modality
instance NFData Modality where
  rnf Input  = ()
  rnf Output = ()

-- | A location and region, together with modality.
data LRM = LRM { lrmLoc :: LocVar
               , lrmReg :: Region
               , lrmMode :: Modality }
  deriving (Read,Show,Eq,Ord, Generic)

instance Out LRM

instance NFData LRM where
  rnf (LRM a b c)  = rnf a `seq` rnf b `seq` rnf c

-- | A designated doesn't-really-exist-anywhere location.
dummyLRM :: LRM
dummyLRM = LRM "l_dummy" (VarR "r_dummy") Input

regionToVar :: Region -> Var
regionToVar r = case r of
                  GlobR v _ -> v
                  DynR  v _ -> v
                  VarR  v   -> v
                  MMapR v   -> v

--------------------------------------------------------------------------------
-- Do this manually to get prettier formatting: (Issue #90)

instance Out ArrowTy2
instance Out Effect
instance Out a => Out (Set a) where
  docPrec n x = docPrec n (S.toList x)
  doc x = doc (S.toList x)
instance Out Prog2
instance (Out l, Out d) => Out (E2Ext l d)
instance Out l => Out (PreLocExp l)
instance Out LocRet

-------------------------------------------------------------------------------

-- | Retrieve all LocVars from a fn type (Arrow)
allLocVars :: ArrowTy2 -> [LocVar]
allLocVars ty = L.map (\(LRM l _ _) -> l) (locVars ty)


inLocVars :: ArrowTy2 -> [LocVar]
inLocVars ty = L.map (\(LRM l _ _) -> l) $
               L.filter (\(LRM _ _ m) -> m == Input) (locVars ty)

outLocVars :: ArrowTy2 -> [LocVar]
outLocVars ty = L.map (\(LRM l _ _) -> l) $
                L.filter (\(LRM _ _ m) -> m == Output) (locVars ty)

outRegVars :: ArrowTy2 -> [LocVar]
outRegVars ty = L.map (\(LRM _ r _) -> regionToVar r) $
                L.filter (\(LRM _ _ m) -> m == Output) (locVars ty)

inRegVars :: ArrowTy2 -> [LocVar]
inRegVars ty = nub $ L.map (\(LRM _ r _) -> regionToVar r) $
               L.filter (\(LRM _ _ m) -> m == Input) (locVars ty)

-- TODO: error handling in these subst* functions.

-- | Apply a location substitution to a type.
substLoc :: Map LocVar LocVar -> Ty2 -> Ty2
substLoc mp ty =
  case ty of
   SymDictTy te -> SymDictTy (go te)
   ProdTy    ts -> ProdTy (L.map go ts)
   PackedTy k l ->
       case M.lookup l mp of
             Just v  -> PackedTy k v
             Nothing -> PackedTy k l
   _ -> ty
  where go = substLoc mp

-- | Like 'substLoc', but constructs the map for you..
substLoc' :: LocVar -> Ty2 -> Ty2
substLoc' loc ty =
  case locsInTy ty of
    [loc2] -> substLoc (M.singleton loc2 loc) ty
    _ -> substLoc M.empty ty

-- | List version of 'substLoc'.
substLocs :: Map LocVar LocVar -> [Ty2] -> [Ty2]
substLocs mp tys = L.map (substLoc mp) tys

-- | Like 'substLocs', but constructs the map for you.
substLocs' :: [LocVar] -> [Ty2] -> [Ty2]
substLocs' locs tys = substLocs (M.fromList $ go tys locs) tys
  where
    go tys locs =
      case (tys, locs) of
        ([],[]) -> []
        (ty:rtys, lc:rlocs) ->
           case ty of
             PackedTy _ loc -> [(loc,lc)] ++ go rtys rlocs
             ProdTy{} -> error $ "substLocs': Unexpected type " ++ sdoc ty
             _ -> go rtys rlocs
        (_,_) -> error $ "substLocs': Unexpected args, " ++ sdoc (tys,locs)

-- | Apply a substitution to an effect set.
substEffs :: Map LocVar LocVar -> Set Effect -> Set Effect
substEffs mp ef =
    S.map (\(Traverse v) ->
               case M.lookup v mp of
                 Just v2 -> Traverse v2
                 Nothing -> Traverse v) ef

-- | Injected cursor args go first in input and output:
prependArgs :: [UrTy l] -> UrTy l -> UrTy l
prependArgs [] t = t
prependArgs ls t = ProdTy $ ls ++ [t]

-- | Remove the extra location annotations.
stripTyLocs :: UrTy a -> UrTy ()
stripTyLocs ty =
  case ty of
    IntTy     -> IntTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map stripTyLocs ls
    SymDictTy ty'    -> SymDictTy $ stripTyLocs ty'
    PackedTy tycon _ -> PackedTy tycon ()
    ListTy ty'       -> ListTy $ stripTyLocs ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy

-- | Collect all the locations mentioned in a type.
locsInTy :: Ty2 -> [LocVar]
locsInTy ty =
    case ty of
      PackedTy _ lv -> [lv]
      ProdTy tys -> concatMap locsInTy tys
      _ -> []

-- Because L2 just adds a bit of metadata and enriched types, it is
-- possible to strip it back down to L1.
revertToL1 :: Prog2 -> Prog1
revertToL1 Prog{ddefs,fundefs,mainExp} =
  Prog ddefs' funefs' mainExp'
  where
    ddefs'   = M.map revertDDef ddefs
    funefs'  = M.map revertFunDef fundefs
    mainExp' = case mainExp of
                 Nothing -> Nothing
                 Just (e,ty) -> Just (revertExp e, stripTyLocs ty)

    revertDDef :: DDef Ty2 -> DDef Ty1
    revertDDef (DDef a b) =
      DDef a (L.filter (\(dcon,_) -> not $ isIndirectionTag dcon) $
              L.map (\(dcon,tys) -> (dcon, L.map (\(x,y) -> (x, stripTyLocs y)) tys)) b)

    revertFunDef :: FunDef2 -> FunDef1
    revertFunDef FunDef{funName,funArg,funTy,funBody} =
      FunDef { funName = funName
             , funArg  = funArg
             , funTy   = (stripTyLocs (arrIn funTy), stripTyLocs (arrOut funTy))
             , funBody = revertExp funBody
             }

    revertExp :: L Exp2 -> L Exp1
    revertExp (L p ex) = L p $
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v _ arg    -> AppE v [] (revertExp arg)
        PrimAppE p args -> PrimAppE (revertPrim p) $ L.map revertExp args
        LetE (v,_,ty, L _ (Ext (IndirectionE _ _ _ _ arg))) bod ->
          let PackedTy tycon _ =  ty in
          LetE (v,[],(stripTyLocs ty), l$ AppE (mkCopyFunName tycon) [] (revertExp arg)) (revertExp bod)
        LetE (v,_,ty,rhs) bod ->
          LetE (v,[], stripTyLocs ty, revertExp rhs) (revertExp bod)
        IfE a b c  -> IfE (revertExp a) (revertExp b) (revertExp c)
        MkProdE ls -> MkProdE $ L.map revertExp ls
        ProjE i e  -> ProjE i (revertExp e)
        CaseE scrt brs     -> CaseE (revertExp scrt) (L.map docase brs)
        DataConE _ dcon ls -> DataConE () dcon $ L.map revertExp ls
        TimeIt e ty b -> TimeIt (revertExp e) (stripTyLocs ty) b
        ParE a b -> ParE (revertExp a) (revertExp b)
        Ext ext ->
          case ext of
            LetRegionE _ bod -> unLoc $ revertExp bod
            LetLocE _ _ bod  -> unLoc $ revertExp bod
            RetE _ v -> VarE v
            FromEndE{} -> error "revertExp: TODO FromEndLE"
            BoundsCheck{} -> error "revertExp: TODO BoundsCheck"
            IndirectionE{} -> error "revertExp: TODO IndirectionE"
        MapE{}  -> error $ "revertExp: TODO MapE"
        FoldE{} -> error $ "revertExp: TODO FoldE"

    -- Ugh .. this is bad. Can we remove the identity cases here ?
    -- TODO: Get rid of this (and L3.toL3Prim) soon.
    revertPrim :: Prim Ty2 -> Prim Ty1
    revertPrim pr =
      case pr of
        AddP      -> AddP
        SubP      -> SubP
        MulP      -> MulP
        DivP      -> DivP
        ModP      -> ModP
        ExpP      -> ExpP
        RandP     -> RandP
        EqSymP    -> EqSymP
        EqIntP    -> EqIntP
        LtP       -> LtP
        GtP       -> GtP
        LtEqP     -> LtEqP
        GtEqP     -> GtEqP
        OrP       -> OrP
        AndP      -> AndP
        MkTrue    -> MkTrue
        MkFalse   -> MkFalse
        SizeParam -> SizeParam
        SymAppend -> SymAppend
        DictInsertP ty -> DictInsertP (stripTyLocs ty)
        DictLookupP ty -> DictLookupP (stripTyLocs ty)
        DictEmptyP  ty -> DictEmptyP  (stripTyLocs ty)
        DictHasKeyP ty -> DictHasKeyP (stripTyLocs ty)
        ErrorP s ty    -> ErrorP s (stripTyLocs ty)
        ReadPackedFile fp tycon reg ty -> ReadPackedFile fp tycon reg (stripTyLocs ty)
        PEndOf -> error "Do not use PEndOf after L2."

    docase :: (DataCon, [(Var,LocVar)], L Exp2) -> (DataCon, [(Var,())], L Exp1)
    docase (dcon,vlocs,rhs) =
      let (vars,_) = unzip vlocs
      in (dcon, zip vars (repeat ()), revertExp rhs)

-- | Does a variable occur in an expression ?
occurs :: S.Set Var -> L Exp2 -> Bool
occurs w (L _ ex) =
  case ex of
    VarE v -> v `S.member` w
    LitE{}    -> False
    LitSymE{} -> False
    AppE _ _ arg -> occurs w arg
    PrimAppE _ ls -> any (occurs w) ls
    LetE (_,_,_,rhs) bod -> occurs w rhs || occurs w bod
    IfE a b c -> occurs w a || occurs w b || occurs w c
    MkProdE ls -> any (occurs w) ls
    ProjE _ e  -> occurs w e
    CaseE e brs -> occurs w e || any (\(_,_,bod) -> occurs w bod) brs
    DataConE _ _ ls -> any (occurs w) ls
    TimeIt e _ _ -> occurs w e
    ParE a b -> occurs w a || occurs w b
    Ext ext ->
      case ext of
        LetRegionE _ bod -> occurs w bod
        LetLocE _ _ bod  -> occurs w bod
        _ -> False
    MapE{} -> error "occurs: TODO MapE"
    FoldE{} -> error "occurs: TODO FoldE"

mapPacked :: (Var -> l -> UrTy l) -> UrTy l -> UrTy l
mapPacked fn t =
  case t of
    IntTy  -> IntTy
    BoolTy -> BoolTy
    SymTy  -> SymTy
    (ProdTy x)    -> ProdTy $ L.map (mapPacked fn) x
    (SymDictTy x) -> SymDictTy $ mapPacked fn x
    PackedTy k l  -> fn (toVar k) l
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    ListTy{} -> error "FINISHLISTS"

-- | Build a dependency list which can be later converted to a graph
depList :: L Exp2 -> [(Var, Var, [Var])]
-- The `acc` is a map so that all dependencies are properly grouped, without any
-- duplicate keys. But we later convert it into a form expected by `graphFromEdges`.
-- The `reverse` makes it easy to peek at the return value of this AST.
depList = reverse . L.map (\(a,b) -> (a,a,b)) . M.toList . go M.empty
    where
      go acc (L _ ex) =
        case ex of
          LetE (v,_,_,rhs) bod ->
              let acc_rhs = go acc rhs
              in go (M.insertWith (++) v (allFreeVars rhs) acc_rhs) bod
          CaseE _ mp -> L.foldr (\(_,_,e) acc' -> go acc' e) acc mp
          Ext ext ->
            case ext of
              LetRegionE r rhs ->
                let v = regionToVar r
                in go (M.insertWith (++) v (allFreeVars rhs) acc) rhs
              LetLocE loc phs rhs  ->
                go (M.insertWith (++) loc (dep phs ++ allFreeVars rhs) acc) rhs
              RetE{}     -> acc
              FromEndE{} -> acc
              BoundsCheck{} -> acc
              IndirectionE{} -> acc
          VarE v -> M.insertWith (++) v [v] acc
          IfE _ b c -> go (go acc b) c
          -- The "dummy" annotation is a small trick to properly handle AST's with a
          -- trivial expression at the end. The first element of `acc` (after it's
          -- converted to a list and reversed) marks the return value of the AST.
          -- If we just return `acc` here, the last thing added to `acc` becomes
          -- the return value, which is incorrect. The "dummy" is just a placeholder
          -- to mark trivial expressions. There will never be a path from any region
          -- variable to "dummy".
          _ -> M.insertWith (++) "dummy" [] acc

      dep :: PreLocExp LocVar -> [Var]
      dep ex =
        case ex of
          StartOfLE r -> [regionToVar r]
          AfterConstantLE _ loc -> [loc]
          AfterVariableLE v loc -> [v,loc]
          InRegionLE r  -> [regionToVar r]
          FromEndLE loc -> [loc]

      -- gFreeVars ++ locations ++ region variables
      allFreeVars :: L Exp2 -> [Var]
      allFreeVars (L _ ex) = S.toList $
        case ex of
          AppE _ locs _       -> S.fromList locs `S.union` gFreeVars ex
          LetE (_,locs,_,_) _ -> S.fromList locs `S.union` gFreeVars ex
          DataConE loc _ _    -> S.singleton loc `S.union` gFreeVars ex
          Ext ext ->
            case ext of
              LetRegionE r _  -> S.singleton (regionToVar r) `S.union` gFreeVars ex
              LetLocE loc _ _ -> S.singleton loc `S.union` gFreeVars ex
              RetE locs _     -> S.fromList locs `S.union` gFreeVars ex
              FromEndE loc    -> S.singleton loc
              BoundsCheck _ reg cur -> S.fromList [reg,cur]
              IndirectionE _ _ (a,b) (c,d) _ -> S.fromList $ [a,b,c,d]
          _ -> gFreeVars ex
