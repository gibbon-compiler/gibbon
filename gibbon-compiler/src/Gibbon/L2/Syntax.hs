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
    , Prog2, DDefs2, DDef2, FunDef2, FunDefs2, Exp2, E2, Ty2
    , Effect(..), ArrowTy2(..) , LocRet(..), LocExp, PreLocExp(..)

    -- * Regions and locations
    , LocVar, Region(..), Modality(..), LRM(..), dummyLRM
    , Multiplicity(..), regionToVar

    -- * Operations on types
    , allLocVars, inLocVars, outLocVars, outRegVars, inRegVars, substLoc
    , substLocs, substEffs, extendPatternMatchEnv
    , locsInTy, dummyTyLocs, allFreeVars

    -- * Other helpers
    , revertToL1, occurs, mapPacked, constPacked, depList, changeAppToSpawn

    , module Gibbon.Language
    )
    where

import           Control.DeepSeq
import           Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import           GHC.Stack (HasCallStack)
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.Language
import           Text.PrettyPrint.HughesPJ
import           Gibbon.L1.Syntax hiding (AddFixed)

--------------------------------------------------------------------------------

type Prog2    = Prog Exp2
type DDef2    = DDef Ty2
type DDefs2   = DDefs Ty2
type FunDef2  = FunDef Exp2
type FunDefs2 = FunDefs Exp2

-- | Function types know about locations and traversal effects.
instance FunctionTy Ty2 where
  type ArrowTy Ty2 = ArrowTy2
  inTys = arrIns
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
data E2Ext loc dec
  = LetRegionE Region                 (E2 loc dec) -- ^ Allocate a new region.
  | LetLocE    loc    (PreLocExp loc) (E2 loc dec) -- ^ Bind a new location.
  | RetE [loc] Var          -- ^ Return a value together with extra loc values.
  | FromEndE loc            -- ^ Bind a location from an EndOf location (for RouteEnds and after).
  | BoundsCheck Int -- Bytes required
                loc -- Region
                loc -- Write cursor
  | AddFixed Var Int
  | IndirectionE TyCon
                 DataCon
                 (loc,Var) -- Pointer
                 (loc,Var) -- Pointee (the thing that the pointer points to)
                 (E2 loc dec) -- If this indirection was added to get rid
                                  -- of a copy_Foo call, we keep the fn call
                                  -- around in case we want to go back to it.
                                  -- E.g. reverting from L2 to L1.
    -- ^ A tagged indirection node.
  deriving (Show, Ord, Eq, Read, Generic, NFData)

-- | Define a location in terms of a different location.
data PreLocExp loc = StartOfLE Region
                   | AfterConstantLE Int -- Number of bytes after.
                                    loc  -- Location which this location is offset from.
                   | AfterVariableLE Var -- Name of variable v. This loc is size(v) bytes after.
                                    loc  -- Location which this location is offset from.
                   | InRegionLE Region
                   | FreeLE
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
     AddFixed vr _      -> S.singleton vr
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
      AddFixed{}     -> True
      BoundsCheck{}  -> False
      IndirectionE{} -> False

instance (Out l, Show l, Typeable (E2 l (UrTy l))) => Typeable (E2Ext l (UrTy l)) where
  gRecoverType ddfs env2 ex =
    case ex of
      LetRegionE _r bod   -> gRecoverType ddfs env2 bod
      LetLocE _l _rhs bod -> gRecoverType ddfs env2 bod
      RetE _loc var       -> case M.lookup var (vEnv env2) of
                               Just ty -> ty
                               Nothing -> error $ "gRecoverType: unbound variable " ++ sdoc var
      FromEndE _loc       -> error $ "Shouldn't enconter FromEndE in tail position"
      BoundsCheck{}       -> error $ "Shouldn't enconter BoundsCheck in tail position"
      IndirectionE tycon _ _ (to,_) _ -> PackedTy tycon to
      AddFixed{}          -> error $ "Shouldn't enconter AddFixed in tail position"


instance (Typeable (E2Ext l (UrTy l)),
          Expression (E2Ext l (UrTy l)),
          Flattenable (E2 l (UrTy l)))
      => Flattenable (E2Ext l (UrTy l)) where

  gFlattenGatherBinds ddfs env ex =
      case ex of
          LetRegionE r bod -> do (bnds,bod') <- go bod
                                 return $ ([], LetRegionE r $ flatLets bnds bod')

          LetLocE l rhs bod -> do (bnds,bod') <- go bod
                                  return $ ([], LetLocE l rhs $ flatLets bnds bod')

          RetE{}        -> return ([],ex)
          FromEndE{}    -> return ([],ex)
          AddFixed{}    -> return ([],ex)
          BoundsCheck{} -> return ([],ex)
          IndirectionE{}-> return ([],ex)

    where go = gFlattenGatherBinds ddfs env

  gFlattenExp ddfs env ex = do (_b,e') <- gFlattenGatherBinds ddfs env ex
                               return e'

instance HasSimplifiableExt E2Ext l d => SimplifiableExt (PreExp E2Ext l d) (E2Ext l d) where
  gInlineTrivExt env ext =
    case ext of
      LetRegionE r bod   -> LetRegionE r (gInlineTrivExp env bod)
      LetLocE loc le bod -> LetLocE loc le (gInlineTrivExp env bod)
      RetE{}         -> ext
      FromEndE{}     -> ext
      BoundsCheck{}  -> ext
      IndirectionE{} -> ext
      AddFixed{}     -> ext


instance HasSubstitutableExt E2Ext l d => SubstitutableExt (PreExp E2Ext l d) (E2Ext l d) where
  gSubstExt old new ext =
    case ext of
      LetRegionE r bod -> LetRegionE r (gSubst old new bod)
      LetLocE l le bod -> LetLocE l le (gSubst old new bod)
      RetE{}           -> ext
      FromEndE{}       -> ext
      BoundsCheck{}    -> ext
      IndirectionE{}   -> ext
      AddFixed{}       -> ext

  gSubstEExt old new ext =
    case ext of
      LetRegionE r bod -> LetRegionE r (gSubstE old new bod)
      LetLocE l le bod -> LetLocE l le (gSubstE old new bod)
      RetE{}           -> ext
      FromEndE{}       -> ext
      BoundsCheck{}    -> ext
      IndirectionE{}   -> ext
      AddFixed{}       -> ext

instance HasRenamable E2Ext l d => Renamable (E2Ext l d) where
  gRename env ext =
    case ext of
      LetRegionE r bod -> LetRegionE r (gRename env bod)
      LetLocE l le bod -> LetLocE l le (gRename env bod)
      RetE{}           -> ext
      FromEndE{}       -> ext
      BoundsCheck{}    -> ext
      IndirectionE{}   -> ext
      AddFixed{}       -> ext

-- | Our type for functions grows to include effects, and explicit universal
-- quantification over location/region variables.
data ArrowTy2 = ArrowTy2
    { locVars :: [LRM]          -- ^ Universally-quantified location params.
                                -- Only these should be referenced in arrIn/arrOut.
    , arrIns  :: [Ty2]          -- ^ Input type for the function.
    , arrEffs :: (S.Set Effect) -- ^ These are present-but-empty initially,
                                -- and the populated by InferEffects.
    , arrOut  :: Ty2            -- ^ Output type for the function.
    , locRets :: [LocRet]       -- ^ L2B feature: multi-valued returns.
    , hasParallelism :: Bool        -- ^ Does this function have parallelism
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


-- | The 'gRecoverType' instance defined in Language.Syntax is incorrect for L2.
-- For the AppE case, it'll just return the type with with the function was
-- defined. However, we want the recovered type to have the locations actually
-- used at the callsites! For example,
--
--     add1 :: Tree @ a -> Tree @ b
--     add1 = _
--
--     ... (add1 [loc1, loc2] tr1) ..
--
-- in this case, we want the type of (add1 tr1) to be (Tree @ loc2)
-- and NOT (Tree @ b). We have to do something similar for variables bound by
-- a pattern match.
instance Typeable (PreExp E2Ext LocVar (UrTy LocVar)) where
  gRecoverType ddfs env2 ex =
    case ex of
      VarE v       -> M.findWithDefault (error $ "Cannot find type of variable " ++ show v ++ " in " ++ show (vEnv env2)) v (vEnv env2)
      LitE _       -> IntTy
      LitSymE _    -> SymTy
      AppE v locs _ -> let fnty  = fEnv env2 # v
                           outty = arrOut fnty
                           mp = M.fromList $ zip (allLocVars fnty) locs
                       in substLoc mp outty

      PrimAppE (DictInsertP ty) ((VarE v):_) -> SymDictTy (Just v) $ stripTyLocs ty
      PrimAppE (DictEmptyP  ty) ((VarE v):_) -> SymDictTy (Just v) $ stripTyLocs ty
      PrimAppE p _ -> primRetTy p

      LetE (v,_,t,_) e -> gRecoverType ddfs (extendVEnv v t env2) e
      IfE _ e _        -> gRecoverType ddfs env2 e
      MkProdE es       -> ProdTy $ L.map (gRecoverType ddfs env2) es
      DataConE loc c _ -> PackedTy (getTyOfDataCon ddfs c) loc
      TimeIt e _ _     -> gRecoverType ddfs env2 e
      MapE _ e         -> gRecoverType ddfs env2 e
      FoldE _ _ e      -> gRecoverType ddfs env2 e
      Ext ext          -> gRecoverType ddfs env2 ext
      ProjE i e ->
        case gRecoverType ddfs env2 e of
          (ProdTy tys) -> tys !! i
          oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
                        ++"\nExpression:\n  "++ sdoc ex
                        ++"\nEnvironment:\n  "++sdoc (vEnv env2)
      SpawnE v locs _ -> let fnty  = fEnv env2 # v
                             outty = arrOut fnty
                             mp = M.fromList $ zip (allLocVars fnty) locs
                         in substLoc mp outty
      SyncE -> voidTy
      IsBigE{} -> BoolTy
      WithArenaE _v e -> gRecoverType ddfs env2 e
      CaseE _ mp ->
        let (c,vlocs,e) = head mp
            (vars,locs) = unzip vlocs
            env2' = extendPatternMatchEnv c ddfs vars locs env2
        in gRecoverType ddfs env2' e

--------------------------------------------------------------------------------
-- Do this manually to get prettier formatting: (Issue #90)

instance Out ArrowTy2
instance Out Effect
instance Out a => Out (S.Set a) where
  docPrec n x = docPrec n (S.toList x)
  doc x = doc (S.toList x)
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

-- | Apply a location substitution to a type.
substLoc :: M.Map LocVar LocVar -> Ty2 -> Ty2
substLoc mp ty =
  case ty of
   SymDictTy v te -> SymDictTy v te -- (go te)
   ProdTy    ts -> ProdTy (L.map go ts)
   PackedTy k l ->
       case M.lookup l mp of
             Just v  -> PackedTy k v
             Nothing -> PackedTy k l
   _ -> ty
  where go = substLoc mp

-- | List version of 'substLoc'.
substLocs :: M.Map LocVar LocVar -> [Ty2] -> [Ty2]
substLocs mp tys = L.map (substLoc mp) tys

-- | Extend an environment for a pattern match. E.g.
--
--     data Foo = MkFoo Int Foo | ...
--
--     case foo1 of
--        MkFoo (i:loc1) (f:loc2) ->
--          new_env2 = extendPatternMatchEnv [loc1,loc2] old_env2
extendPatternMatchEnv :: HasCallStack => DataCon -> DDefs Ty2 -> [Var] -> [LocVar]
                      -> Env2 Ty2 -> Env2 Ty2
extendPatternMatchEnv dcon ddefs vars locs env2 =
  let tys  = lookupDataCon ddefs dcon
      tys' = foldr
               (\(loc,ty) acc ->
                  case locsInTy ty of
                    []     -> ty:acc
                    [loc2] -> (substLoc (M.singleton loc2 loc) ty) : acc
                    _  -> error $ "extendPatternMatchEnv': Found more than 1 location in type: " ++ sdoc ty)
               []
               (fragileZip locs tys)
  in extendsVEnv (M.fromList $ fragileZip vars tys') env2

-- | Apply a substitution to an effect set.
substEffs :: M.Map LocVar LocVar -> S.Set Effect -> S.Set Effect
substEffs mp ef =
    S.map (\(Traverse v) ->
               case M.lookup v mp of
                 Just v2 -> Traverse v2
                 Nothing -> Traverse v) ef

dummyTyLocs :: Applicative f => UrTy () -> f (UrTy LocVar)
dummyTyLocs ty = traverse (const (pure (toVar "dummy"))) ty

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
    revertDDef (DDef tyargs a b) =
      DDef tyargs a
        (L.filter (\(dcon,_) -> not $ isIndirectionTag dcon) $
         L.map (\(dcon,tys) -> (dcon, L.map (\(x,y) -> (x, stripTyLocs y)) tys)) b)

    revertFunDef :: FunDef2 -> FunDef1
    revertFunDef FunDef{funName,funArgs,funTy,funBody} =
      FunDef { funName = funName
             , funArgs = funArgs
             , funTy   = (L.map stripTyLocs (arrIns funTy), stripTyLocs (arrOut funTy))
             , funBody = revertExp funBody
             }

    revertExp :: Exp2 -> Exp1
    revertExp ex =
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v _ args   -> AppE v [] (L.map revertExp args)
        PrimAppE p args -> PrimAppE (revertPrim p) $ L.map revertExp args
        LetE (v,_,ty, (Ext (IndirectionE _ _ _ _ arg))) bod ->
          let PackedTy tycon _ =  ty in
          LetE (v,[],(stripTyLocs ty), AppE (mkCopyFunName tycon) [] [revertExp arg]) (revertExp bod)
        LetE (v,_,ty,rhs) bod ->
          LetE (v,[], stripTyLocs ty, revertExp rhs) (revertExp bod)
        IfE a b c  -> IfE (revertExp a) (revertExp b) (revertExp c)
        MkProdE ls -> MkProdE $ L.map revertExp ls
        ProjE i e  -> ProjE i (revertExp e)
        CaseE scrt brs     -> CaseE (revertExp scrt) (L.map docase brs)
        DataConE _ dcon ls -> DataConE () dcon $ L.map revertExp ls
        TimeIt e ty b -> TimeIt (revertExp e) (stripTyLocs ty) b
        SpawnE v _ args -> SpawnE v [] (L.map revertExp args)
        SyncE -> SyncE
        IsBigE e -> IsBigE (revertExp e)
        WithArenaE v e -> WithArenaE v (revertExp e)
        Ext ext ->
          case ext of
            LetRegionE _ bod -> revertExp bod
            LetLocE _ _ bod  -> revertExp bod
            RetE _ v -> VarE v
            AddFixed{} -> error "revertExp: AddFixed not handled."
            FromEndE{} -> error "revertExp: TODO FromEndLE"
            BoundsCheck{} -> error "revertExp: TODO BoundsCheck"
            IndirectionE{} -> error "revertExp: TODO IndirectionE"
        MapE{}  -> error $ "revertExp: TODO MapE"
        FoldE{} -> error $ "revertExp: TODO FoldE"

    -- Ugh .. this is bad. Can we remove the identity cases here ?
    -- TODO: Get rid of this (and L3.toL3Prim) soon.
    revertPrim :: Prim Ty2 -> Prim Ty1
    revertPrim pr = fmap stripTyLocs pr

    docase :: (DataCon, [(Var,LocVar)], Exp2) -> (DataCon, [(Var,())], Exp1)
    docase (dcon,vlocs,rhs) =
      let (vars,_) = unzip vlocs
      in (dcon, zip vars (repeat ()), revertExp rhs)

-- | Does a variable occur in an expression ?
--
-- N.B. it only looks for actual variables, not LocVar's or RegionVar's.
occurs :: S.Set Var -> Exp2 -> Bool
occurs w ex =
  case ex of
    VarE v -> v `S.member` w
    LitE{}    -> False
    LitSymE{} -> False
    AppE _ _ ls   -> any go ls
    PrimAppE _ ls -> any go ls
    LetE (_,_,_,rhs) bod -> go rhs || go bod
    IfE a b c   -> go a || go b || go c
    MkProdE ls  -> any go ls
    ProjE _ e   -> go e
    CaseE e brs -> go e || any (\(_,_,bod) -> go bod) brs
    DataConE _ _ ls  -> any go ls
    TimeIt e _ _     -> go e
    SpawnE _ _ ls    -> any go ls
    SyncE            -> False
    IsBigE e         -> go e
    WithArenaE v rhs -> v `S.member` w || go rhs
    Ext ext ->
      case ext of
        LetRegionE _ bod  -> go bod
        LetLocE _ le bod  ->
          let oc_bod = go bod in
          case le of
            AfterVariableLE v _ -> v `S.member` w || oc_bod
            StartOfLE{}         -> oc_bod
            AfterConstantLE{}   -> oc_bod
            InRegionLE{}        -> oc_bod
            FreeLE{}            -> oc_bod
            FromEndLE{}         -> oc_bod
        RetE _ v      -> v `S.member` w
        FromEndE{}    -> False
        BoundsCheck{} -> False
        AddFixed v _  -> v `S.member` w
        IndirectionE _ _ (_,v1) (_,v2) ib ->
          v1 `S.member` w  || v2 `S.member` w || go ib
    MapE{}  -> error "occurs: TODO MapE"
    FoldE{} -> error "occurs: TODO FoldE"
  where
    go = occurs w


mapPacked :: (Var -> l -> UrTy l) -> UrTy l -> UrTy l
mapPacked fn t =
  case t of
    IntTy  -> IntTy
    BoolTy -> BoolTy
    SymTy  -> SymTy
    (ProdTy x)    -> ProdTy $ L.map (mapPacked fn) x
    (SymDictTy v x) -> SymDictTy v x
    PackedTy k l  -> fn (toVar k) l
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    ArenaTy  -> ArenaTy
    ListTy ty-> ListTy ty
    SymSetTy -> SymSetTy
    SymHashTy-> SymHashTy

constPacked :: UrTy a1 -> UrTy a2 -> UrTy a1
constPacked c t =
  case t of
    IntTy  -> IntTy
    BoolTy -> BoolTy
    SymTy  -> SymTy
    (ProdTy x)    -> ProdTy $ L.map (constPacked c) x
    (SymDictTy v _x) -> SymDictTy v $ stripTyLocs c
    PackedTy _k _l  -> c
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    ArenaTy  -> ArenaTy
    ListTy ty-> ListTy (constPacked c ty)
    SymSetTy -> SymSetTy
    SymHashTy-> SymHashTy

-- | Build a dependency list which can be later converted to a graph
depList :: Exp2 -> [(Var, Var, [Var])]
-- The helper function, go, works with a map rather than list so that all
-- dependencies are properly grouped, without any duplicate keys. But we
-- convert it back to a list so that we can hand it off to 'graphFromEdges'.
-- Reversing the list makes it easy to peek at the return value of this AST later.
depList = L.map (\(a,b) -> (a,a,b)) . M.toList . go M.empty
    where
      go :: M.Map Var [Var] -> Exp2 -> M.Map Var [Var]
      go acc ex =
        case ex of
          VarE v    -> M.insertWith (++) v [v] acc
          LitE{}    -> acc
          LitSymE{} -> acc
          AppE _ _ args   -> foldl go acc args
          PrimAppE _ args -> foldl go acc args
          LetE (v,_,_,rhs) bod ->
            let acc_rhs = go acc rhs
            in go (M.insertWith (++) v (allFreeVars rhs) acc_rhs) bod
          IfE _ b c  -> go (go acc b) c
          MkProdE ls -> foldl go acc ls
          ProjE _ e  -> go acc e
          CaseE _ mp -> L.foldr (\(_,_,e) acc' -> go acc' e) acc mp
          DataConE _ _ args -> foldl go acc args
          TimeIt e _ _ -> go acc e
          WithArenaE _ e -> go acc e
          SpawnE _ _ ls  -> foldl go acc ls
          SyncE          -> acc
          IsBigE e       -> go acc e
          MapE{}  -> acc
          FoldE{} -> acc
          Ext ext ->
            case ext of
              LetRegionE r rhs ->
                go (M.insertWith (++) (regionToVar r) (allFreeVars rhs) acc) rhs
              LetLocE loc phs rhs  ->
                go (M.insertWith (++) loc (dep phs ++ allFreeVars rhs) acc) rhs
              RetE{}         -> acc
              FromEndE{}     -> acc
              BoundsCheck{}  -> acc
              IndirectionE{} -> acc
              AddFixed v _   -> M.insertWith (++) v [v] acc

      dep :: PreLocExp LocVar -> [Var]
      dep ex =
        case ex of
          StartOfLE r -> [regionToVar r]
          AfterConstantLE _ loc -> [loc]
          AfterVariableLE v loc -> [v,loc]
          InRegionLE r  -> [regionToVar r]
          FromEndLE loc -> [loc]
          FreeLE -> []

-- gFreeVars ++ locations ++ region variables
allFreeVars :: Exp2 -> [Var]
allFreeVars ex = S.toList $
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
        AddFixed v _    -> S.singleton v
    _ -> gFreeVars ex


changeAppToSpawn :: Var -> [Exp2] -> Exp2 -> Exp2
changeAppToSpawn v args2 ex1 =
  case ex1 of
    VarE{}    -> ex1
    LitE{}    -> ex1
    LitSymE{} -> ex1
    AppE f locs args | v == f && args == args2 -> SpawnE f locs $ map go args
    AppE f locs args -> AppE f locs $ map go args
    PrimAppE f args  -> PrimAppE f $ map go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE (v,loc,ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE xs -> MkProdE $ map go xs
    ProjE i e  -> ProjE i $ go e
    DataConE loc dcon args -> DataConE loc dcon $ map go args
    CaseE scrt mp ->
      CaseE (go scrt) $ map (\(a,b,c) -> (a,b, go c)) mp
    TimeIt e ty b  -> TimeIt (go e) ty b
    WithArenaE v e -> WithArenaE v (go e)
    SpawnE{} -> ex1
    SyncE{}  -> ex1
    IsBigE e -> IsBigE (go e)
    Ext ext ->
      case ext of
        LetRegionE r rhs  -> Ext $ LetRegionE r (go rhs)
        LetLocE l lhs rhs -> Ext $ LetLocE l lhs (go rhs)
        RetE{}            -> ex1
        FromEndE{}        -> ex1
        BoundsCheck{}     -> ex1
        IndirectionE{}    -> ex1
        AddFixed{}        -> ex1
    MapE{}  -> error "addRANExp: TODO MapE"
    FoldE{}  -> error "addRANExp: TODO FoldE"

  where go = changeAppToSpawn v args2
