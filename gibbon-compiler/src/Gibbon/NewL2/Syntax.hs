{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- | An intermediate language with an effect system that captures traversals.

module Gibbon.NewL2.Syntax
    (
    -- * Extended language L2 with location types.
      Old.E2Ext(..)
    , Prog2, DDefs2, DDef2, FunDef2, FunDefs2, Exp2, Ty2(..)
    , Old.Effect(..), Old.ArrowTy2(..) , Old.LocRet(..), LocArg(..), LocExp, RegExp, Old.PreLocExp(..), Old.PreRegExp(..)

    -- * Regions and locations
    , LocVar, Old.Region(..), Old.Modality(..),  Old.LRM(..), LREM(..)
    , Old.Multiplicity(..), Old.RegionSize(..), Old.RegionType(..), Old.regionToVar

    -- * Operations on types
    , Old.allLocVars, Old.inLocVars, Old.outLocVars, Old.outRegVars, Old.inRegVars, Old.allRegVars
    , substLoc, substLocs, Old.substEff, Old.substEffs, extendPatternMatchEnv, extendPatternMatchEnvLocVar
    , locsInTy, Old.dummyTyLocs, allFreeVars, freeLocVars
    , toLocVar, toEndRegVar, getModality,  fromLRM, fromVarToSingleRegVar, fromLocArgToFreeVarsTy, Old.fromLocVarToRegVar, toRegVar, isRegionLocArg, inLocArgs

    -- * Other helpers
    , revertToL1, Old.occurs, Old.mapPacked, Old.constPacked, depList, Old.changeAppToSpawn
    , toEndFromTaggedV, toTagV, toEndFromTaggedRegVar, genSymRegVar, isLocAlive

    , module Gibbon.Language
    )
    where

import           Control.DeepSeq
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Safe as Sf

import           GHC.Stack (HasCallStack)
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.Language
-- import           Text.PrettyPrint.HughesPJ
import           Gibbon.L1.Syntax hiding (AddFixed, StartOfPkdCursor)
import qualified Gibbon.L1.Syntax as L1

import qualified Gibbon.L2.Syntax as Old
import qualified Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

type Prog2    = Prog Var Exp2
type DDef2    = DDef Ty2
type DDefs2   = DDefs Ty2
type FunDef2  = FunDef Var Exp2
type FunDefs2 = FunDefs Var Exp2

-- | Function types know about locations and traversal effects.
instance FunctionTy Ty2 where
  type ArrowTy Ty2 = Old.ArrowTy2 Ty2
  inTys = Old.arrIns
  outTy = Old.arrOut

-- | Extended expressions, L2.
--
--   By adding a `LocVar` decoration, all data constructors,
--   applications, and bindings gain a location annotation.
type Exp2   = PreExp Old.E2Ext LocArg Ty2
type LocExp = Old.PreLocExp LocArg
type RegExp = Old.PreRegExp LocArg

-- We need a newtype here to avoid overlapping type family instance for FunctionTy
-- | L1 Types extended with abstract Locations.
newtype Ty2 = MkTy2 { unTy2 :: (UrTy LocVar) }
  deriving (Read, Show, Eq, Ord, Generic)

instance Out Ty2
instance NFData Ty2

--------------------------------------------------------------------------------

data LREM = LREM { lremLoc    :: LocVar
                 , lremReg    :: RegVar
                 , lremEndReg :: RegVar
                 , lremMode   :: Old.Modality
                 }
  deriving (Read,Show,Eq,Ord,Generic)

instance Out LREM

instance NFData LREM where
  rnf (LREM a b c d)  = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

fromLRM :: Old.LRM -> LREM
fromLRM (Old.LRM loc reg mode) =
  LREM loc (Old.regionToVar reg) (toEndVRegVar (Old.regionToVar reg)) mode

data LocArg = Loc LREM
            | EndWitness LREM LocVar
            | Reg RegVar Old.Modality
            | EndOfReg RegVar Old.Modality RegVar
            | EndOfReg_Tagged RegVar
  deriving (Read, Show, Eq, Ord, Generic)

instance Out LocArg
instance NFData LocArg

isRegionLocArg :: LocArg -> Bool 
isRegionLocArg loc = case loc of 
                          Loc{} -> False
                          EndWitness{} -> False
                          Reg{} -> True
                          EndOfReg{} -> True
                          EndOfReg_Tagged{} -> True 

inLocArgs :: L2.ArrowTy2 ty2 -> [LocArg]
inLocArgs ty = L.map (\lrm -> Loc $ fromLRM lrm) $
               L.filter (\(L2.LRM _ _ m) -> m == L2.Input || m == L2.InputMutable) (L2.locVars ty)

toRegVar :: LocArg -> RegVar
toRegVar arg =
  case arg of
    Loc lrm        -> lremReg lrm
    Reg v _        -> v
    EndOfReg _ _ v -> v
    EndOfReg_Tagged v -> v
    EndWitness {} -> error "toRegVar: EndWitness not handled"

toEndRegVar :: LocArg -> RegVar
toEndRegVar arg =
  case arg of
    Loc lrm        -> lremEndReg lrm
    Reg v _        -> toEndVRegVar v
    EndOfReg _ _ v -> v
    EndOfReg_Tagged v -> v
    EndWitness {} -> error "toRegVar: EndWitness not handled"

fromVarToSingleRegVar :: Var -> RegVar
fromVarToSingleRegVar v = SingleR v

{- VS: TODO: this should return either LocVar or RegVar -}
toLocVar :: LocArg -> LocVar
toLocVar arg =
  case arg of
    Loc lrm        -> lremLoc lrm
    EndWitness _ v -> v
    Reg v _        -> Old.fromRegVarToLocVar v
    EndOfReg _ _ v -> Old.fromRegVarToLocVar v
    EndOfReg_Tagged v -> Old.fromRegVarToLocVar v

getModality :: LocArg -> Maybe L2.Modality
getModality lc =
  case lc of
    Loc lrm        -> Just $ lremMode lrm
    EndWitness lrm _v -> Just $ lremMode lrm
    Reg _v m        -> Just m
    EndOfReg _ m _v -> Just m 
    EndOfReg_Tagged _ -> Nothing

fromLocArgToFreeVarsTy :: LocArg -> FreeVarsTy
fromLocArgToFreeVarsTy arg =
  case arg of
    Loc lrm        -> fromLocVarToFreeVarsTy $ lremLoc lrm
    EndWitness _ v -> fromLocVarToFreeVarsTy v
    Reg v _        -> fromRegVarToFreeVarsTy v
    EndOfReg _ _ v -> fromRegVarToFreeVarsTy v
    EndOfReg_Tagged v -> fromRegVarToFreeVarsTy v


-- Returns the data constructor 
-- fromLocArgToVar :: LocArg -> Var 
-- fromLocArgToVar arg =
--   case arg of
--     Loc lrm        -> unwrapLocVar $ lremLoc lrm
--     EndWitness _ v -> v
--     Reg v _        -> v
--     EndOfReg _ _ v -> v
--     EndOfReg_Tagged v -> toEndFromTaggedV v

instance Out (Old.ArrowTy2 Ty2)

toTagV :: Var -> Var
toTagV v = (toVar "tag_") `varAppend` v

toEndFromTaggedV :: Var -> Var
toEndFromTaggedV v = (toVar "end_from_tagged_") `varAppend` v

genSymRegVar :: RegVar -> PassM RegVar
genSymRegVar reg = do
  case reg of 
    SingleR v -> do 
                  v' <- gensym v
                  return $ SingleR v'
    SoARv reg fieldRegs -> do 
                  reg' <- genSymRegVar reg
                  fieldRegs' <- mapM (\(k, freg) -> do 
                                        freg' <- genSymRegVar freg
                                        return (k, freg')) fieldRegs
                  return $ SoARv reg' fieldRegs'

toEndFromTaggedRegVar :: RegVar -> RegVar
toEndFromTaggedRegVar r = case r of 
                            SingleR v -> SingleR (toEndFromTaggedV v)
                            SoARv regvar fieldRegs -> SoARv (toEndFromTaggedRegVar regvar) (L.map (\(k, freg) -> (k, toEndFromTaggedRegVar freg)) fieldRegs) 

--------------------------------------------------------------------------------

instance FreeVars LocExp where
  gFreeVars e =
    case e of
      -- Old.AfterConstantLE _ loc  -> S.singleton $ unwrapLocVar (toLocVar loc)
      -- Old.AfterVariableLE v loc _ -> S.fromList [v, unwrapLocVar (toLocVar loc)]
      Old.AfterConstantLE _ _loc  -> S.empty
      Old.AfterVariableLE v _loc _ -> S.fromList [v]
      _ -> S.empty


instance Typeable (Old.E2Ext LocArg Ty2) where
  gRecoverType ddfs env2 ex =
    case ex of
      Old.LetRegionE _r _ _ _ bod    -> gRecoverType ddfs env2 bod
      Old.LetParRegionE _r _ _ bod -> gRecoverType ddfs env2 bod
      Old.StartOfPkdCursor{}       -> MkTy2 $ CursorTy
      Old.TagCursor{}      -> MkTy2 $ CursorTy
      Old.LetLocE _l _rhs bod -> gRecoverType ddfs env2 bod
      Old.RetE _loc var       -> case M.lookup var (vEnv env2) of
                                   Just ty -> ty
                                   Nothing -> error $ "gRecoverType: unbound variable " ++ sdoc var
      Old.FromEndE _loc       -> error "Shouldn't enconter FromEndE in tail position"
      Old.BoundsCheck{}       -> error "Shouldn't enconter BoundsCheck in tail position"
      Old.IndirectionE tycon _ _ (to,_) _ -> MkTy2 $ PackedTy tycon (toLocVar to)
      Old.AddFixed{}          -> error "Shouldn't enconter AddFixed in tail position"
      Old.GetCilkWorkerNum    -> MkTy2 $ IntTy
      Old.LetAvail _ bod      -> gRecoverType ddfs env2 bod
      Old.AllocateTagHere{}   -> MkTy2 $ ProdTy []
      Old.AllocateScalarsHere{} -> MkTy2 $ ProdTy []
      Old.SSPush{}              -> MkTy2 $ ProdTy []
      Old.SSPop{}               -> MkTy2 $ ProdTy []
      Old.LetRegE{}             -> error "gRecoverType: LetRegE not handled"
      Old.BoundsCheckVector{}   -> error "gRecoverType: BoundsCheckVector not handled"

  gRecoverTypeLoc ddfs env2 ex =
    case ex of
      Old.LetRegionE _r _ _ _ bod    -> gRecoverTypeLoc ddfs env2 bod
      Old.LetParRegionE _r _ _ bod -> gRecoverTypeLoc ddfs env2 bod
      Old.StartOfPkdCursor{}       -> MkTy2 $ CursorTy
      Old.TagCursor{}      -> MkTy2 $ CursorTy
      Old.LetLocE _l _rhs bod -> gRecoverTypeLoc ddfs env2 bod
      Old.RetE _loc var       -> case M.lookup (fromVarToFreeVarsTy var) (vEnv env2) of
                                   Just ty -> ty
                                   Nothing -> error $ "gRecoverType: unbound variable " ++ sdoc var
      Old.FromEndE _loc       -> error "Shouldn't enconter FromEndE in tail position"
      Old.BoundsCheck{}       -> error "Shouldn't enconter BoundsCheck in tail position"
      Old.IndirectionE tycon _ _ (to,_) _ -> MkTy2 $ PackedTy tycon (toLocVar to)
      Old.AddFixed{}          -> error "Shouldn't enconter AddFixed in tail position"
      Old.GetCilkWorkerNum    -> MkTy2 $ IntTy
      Old.LetAvail _ bod      -> gRecoverTypeLoc ddfs env2 bod
      Old.AllocateTagHere{}   -> MkTy2 $ ProdTy []
      Old.AllocateScalarsHere{} -> MkTy2 $ ProdTy []
      Old.SSPush{}              -> MkTy2 $ ProdTy []
      Old.SSPop{}               -> MkTy2 $ ProdTy []
      Old.LetRegE{}             -> error "gRecoverTypeLoc: LetRegE not handled"
      Old.BoundsCheckVector{}   -> error "gRecoverTypeLoc: BoundsCheckVector not handled"



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
instance Out (Old.E2Ext LocArg Ty2) => Typeable (PreExp Old.E2Ext LocArg Ty2) where
  gRecoverType ddfs env2 ex =
    case ex of
      VarE v       -> M.findWithDefault (error $ "Cannot find type of variable " ++ show v ++ " in " ++ show (vEnv env2)) v (vEnv env2)
      LitE _       -> MkTy2 $ IntTy
      CharE _      -> MkTy2 $ CharTy
      FloatE{}     -> MkTy2 $ FloatTy
      LitSymE _    -> MkTy2 $ SymTy
      AppE v _ locargs _ ->
                       let fnty  = fEnv env2 # v
                           outty = Old.arrOut fnty
                           mp = M.fromList $ zip (Old.allLocVars fnty) (map toLocVar locargs)
                       in substLoc mp outty

      PrimAppE (DictInsertP ty) ((VarE v):_) -> MkTy2 $ SymDictTy (Just v) $ stripTyLocs (unTy2 ty)
      PrimAppE (DictEmptyP  ty) ((VarE v):_) -> MkTy2 $ SymDictTy (Just v) $ stripTyLocs (unTy2 ty)
      PrimAppE p _ -> MkTy2 $ primRetTy (fmap unTy2 p)

      LetE (v,_,t,_) e -> gRecoverType ddfs (extendVEnv v t env2) e
      IfE _ e _        -> gRecoverType ddfs env2 e
      MkProdE es       -> MkTy2 $ ProdTy $ L.map (unTy2 . gRecoverType ddfs env2) es
      DataConE loc c _ -> MkTy2 $ PackedTy (getTyOfDataCon ddfs c) (toLocVar loc)
      TimeIt e _ _     -> gRecoverType ddfs env2 e
      MapE _ e         -> gRecoverType ddfs env2 e
      FoldE _ _ e      -> gRecoverType ddfs env2 e
      Ext ext          -> gRecoverType ddfs env2 ext
      ProjE i e ->
        case unTy2 $ gRecoverType ddfs env2 e of
          (ProdTy tys) -> MkTy2 $ (tys !! i)
          oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
                        ++"\nExpression:\n  "++ sdoc ex
                        ++"\nEnvironment:\n  "++sdoc (vEnv env2)
      SpawnE v locargs _ ->
                         let fnty  = fEnv env2 # v
                             outty = Old.arrOut fnty
                             mp = M.fromList $ zip (Old.allLocVars fnty) (map toLocVar locargs)
                         in substLoc mp outty
      SyncE -> MkTy2 $ voidTy
      WithArenaE _v e -> gRecoverType ddfs env2 e
      CaseE _ mp ->
        let (c,vlocargs,e) = Sf.headErr mp
            (vars,locargs) = unzip vlocargs
            locs = map toLocVar locargs

            env2' = extendPatternMatchEnv c ddfs vars locs env2
        in gRecoverType ddfs env2' e


  gRecoverTypeLoc ddfs env2 ex =
    case ex of
      VarE v       -> M.findWithDefault (error $ "Cannot find type of variable " ++ show v ++ " in " ++ show (vEnv env2)) (fromVarToFreeVarsTy v) (vEnv env2)
      LitE _       -> MkTy2 $ IntTy
      CharE _      -> MkTy2 $ CharTy
      FloatE{}     -> MkTy2 $ FloatTy
      LitSymE _    -> MkTy2 $ SymTy
      AppE v _ locargs _ ->
                       let fnty  = fEnv env2 # (fromVarToFreeVarsTy v)
                           outty = Old.arrOut fnty
                           mp = M.fromList $ zip (Old.allLocVars fnty) (map toLocVar locargs)
                       in substLoc mp outty

      PrimAppE (DictInsertP ty) ((VarE v):_) -> MkTy2 $ SymDictTy (Just v) $ stripTyLocs (unTy2 ty)
      PrimAppE (DictEmptyP  ty) ((VarE v):_) -> MkTy2 $ SymDictTy (Just v) $ stripTyLocs (unTy2 ty)
      PrimAppE p _ -> MkTy2 $ primRetTy (fmap unTy2 p)

      LetE (v,_,t,_) e -> gRecoverTypeLoc ddfs (extendVEnvLocVar (fromVarToFreeVarsTy v) t env2) e
      IfE _ e _        -> gRecoverTypeLoc ddfs env2 e
      MkProdE es       -> MkTy2 $ ProdTy $ L.map (unTy2 . gRecoverTypeLoc ddfs env2) es
      DataConE loc c _ -> MkTy2 $ PackedTy (getTyOfDataCon ddfs c) (toLocVar loc)
      TimeIt e _ _     -> gRecoverTypeLoc ddfs env2 e
      MapE _ e         -> gRecoverTypeLoc ddfs env2 e
      FoldE _ _ e      -> gRecoverTypeLoc ddfs env2 e
      Ext ext          -> gRecoverTypeLoc ddfs env2 ext
      ProjE i e ->
        case unTy2 $ gRecoverTypeLoc ddfs env2 e of
          (ProdTy tys) -> MkTy2 $ (tys !! i)
          oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
                        ++"\nExpression:\n  "++ sdoc ex
                        ++"\nEnvironment:\n  "++sdoc (vEnv env2)
      SpawnE v locargs _ ->
                         let fnty  = fEnv env2 # (fromVarToFreeVarsTy v)
                             outty = Old.arrOut fnty
                             mp = M.fromList $ zip (Old.allLocVars fnty) (map toLocVar locargs)
                         in substLoc mp outty
      SyncE -> MkTy2 $ voidTy
      WithArenaE _v e -> gRecoverTypeLoc ddfs env2 e
      CaseE _ mp ->
        let (c,vlocargs,e) = Sf.headErr mp
            (vars,locargs) = unzip vlocargs
            locs = map toLocVar locargs

            env2' = extendPatternMatchEnvLocVar c ddfs vars locs env2
        in gRecoverTypeLoc ddfs env2' e

-------------------------------------------------------------------------------
-- Need to redefine the following because of the Ty2 newtype:

-- | Apply a location substitution to a type.
substLoc :: M.Map LocVar LocVar -> Ty2 -> Ty2
substLoc mp ty = MkTy2 $
  case unTy2 ty of
   SymDictTy v te -> SymDictTy v te -- (go te)
   ProdTy    ts -> ProdTy (L.map (unTy2 . go . MkTy2) ts)
   PackedTy k l ->
       case M.lookup l mp of
             Just v  -> PackedTy k v
             Nothing -> PackedTy k l
   _ -> unTy2 ty
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
                      -> Env2 Var Ty2 -> Env2 Var Ty2
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

extendPatternMatchEnvLocVar :: HasCallStack => DataCon -> DDefs Ty2 -> [Var] -> [LocVar]
                      -> Env2 FreeVarsTy Ty2 -> Env2 FreeVarsTy Ty2
extendPatternMatchEnvLocVar dcon ddefs vars locs env2 =
  let tys  = lookupDataCon ddefs dcon
      tys' = foldr
               (\(loc,ty) acc ->
                  case locsInTy ty of
                    []     -> ty:acc
                    [loc2] -> (substLoc (M.singleton loc2 loc) ty) : acc
                    _  -> error $ "extendPatternMatchEnv': Found more than 1 location in type: " ++ sdoc ty)
               []
               (fragileZip locs tys)
      vars' = L.map fromVarToFreeVarsTy vars
  in extendsVEnvLocVar (M.fromList $ fragileZip vars' tys') env2

-- | Collect all the locations mentioned in a type.
locsInTy :: Ty2 -> [LocVar]
locsInTy ty =
    case unTy2 ty of
      PackedTy _ lv -> [lv]
      ProdTy tys -> concatMap (locsInTy . MkTy2) tys
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
                Just (e,ty) -> Just (revertExp e, stripTyLocs (unTy2 ty))

revertDDef :: DDef Ty2 -> DDef Ty1
revertDDef (DDef tyargs a b l) =
  DDef tyargs a
    (L.filter (\(dcon,_) -> not $ isIndirectionTag dcon) $
         L.map (\(dcon,tys) -> (dcon, L.map (\(x,y) -> (x, stripTyLocs (unTy2 y))) tys)) b) l

revertFunDef :: FunDef2 -> FunDef1
revertFunDef FunDef{funName,funArgs,funTy,funBody,funMeta} =
  FunDef { funName = funName
         , funArgs = funArgs
         , funTy   = (L.map (stripTyLocs . unTy2) (Old.arrIns funTy), stripTyLocs (unTy2 (Old.arrOut funTy)))
         , funBody = revertExp funBody
         , funMeta = funMeta
         }

revertExp :: Exp2 -> Exp1
revertExp ex =
  case ex of
    VarE v    -> VarE v
    LitE n    -> LitE n
    CharE n  -> CharE n
    FloatE n  -> FloatE n
    LitSymE v -> LitSymE v
    AppE v cty _ args   -> AppE v cty [] (L.map revertExp args)
    PrimAppE p args -> PrimAppE (revertPrim p) $ L.map revertExp args
    LetE (v,_, ty, (Ext (Old.IndirectionE _ _ _ _ arg))) bod ->
      let PackedTy tycon _ =  unTy2 ty in
          LetE (v,[],(stripTyLocs (unTy2 ty)), AppE (mkCopyFunName tycon) NotTailRec [] [revertExp arg]) (revertExp bod)
    LetE (v,_,ty,rhs) bod ->
      LetE (v,[], stripTyLocs (unTy2 ty), revertExp rhs) (revertExp bod)
    IfE a b c  -> IfE (revertExp a) (revertExp b) (revertExp c)
    MkProdE ls -> MkProdE $ L.map revertExp ls
    ProjE i e  -> ProjE i (revertExp e)
    CaseE scrt brs     -> CaseE (revertExp scrt) (L.map docase brs)
    DataConE _ dcon ls -> DataConE () dcon $ L.map revertExp ls
    TimeIt e ty b -> TimeIt (revertExp e) (stripTyLocs (unTy2 ty)) b
    SpawnE v _ args -> SpawnE v [] (L.map revertExp args)
    SyncE -> SyncE
    WithArenaE v e -> WithArenaE v (revertExp e)
    Ext ext ->
      case ext of
        Old.LetRegionE _ _ _ _ bod -> revertExp bod
        Old.LetParRegionE _ _ _ bod -> revertExp bod
        Old.LetLocE _ _ bod  -> revertExp bod
        Old.TagCursor _a _b -> error "revertExp cannot revert TagCursor" --Ext (L1.StartOfPkdCursor a)
        Old.StartOfPkdCursor v -> Ext (L1.StartOfPkdCursor v)
        Old.RetE _ v -> VarE v
        Old.AddFixed{} -> error "revertExp: TODO AddFixed."
        Old.FromEndE{} -> error "revertExp: TODO FromEndLE"
        Old.BoundsCheck{}   -> error "revertExp: TODO BoundsCheck"
        Old.IndirectionE{}  -> error "revertExp: TODO IndirectionE"
        Old.GetCilkWorkerNum-> LitE 0
        Old.LetAvail _ bod  -> revertExp bod
        Old.AllocateTagHere{} -> error "revertExp: TODO AddFixed."
        Old.AllocateScalarsHere{} -> error "revertExp: TODO AddFixed."
        Old.SSPush{} -> error "revertExp: TODO SSPush."
        Old.SSPop{} -> error "revertExp: TODO SSPop."
        Old.LetRegE {} -> error "revertExp: LetRegE not handled"
        Old.BoundsCheckVector {} -> error "revertExp: BoundsCheckVector not handled"
    MapE{}  -> error $ "revertExp: TODO MapE"
    FoldE{} -> error $ "revertExp: TODO FoldE"
  where
    -- Ugh .. this is bad. Can we remove the identity cases here ?
    -- TODO: Get rid of this (and L3.toL3Prim) soon.
    revertPrim :: Prim Ty2 -> Prim Ty1
    revertPrim pr = fmap (stripTyLocs . unTy2) pr

    docase :: (DataCon, [(Var,LocArg)], Exp2) -> (DataCon, [(Var,())], Exp1)
    docase (dcon,vlocargs,rhs) =
      let (vars,_) = unzip vlocargs
      in (dcon, zip vars (repeat ()), revertExp rhs)


-- | Build a dependency list which can be later converted to a graph
depList :: Exp2 -> [(FreeVarsTy, FreeVarsTy, [FreeVarsTy])]
-- The helper function, go, works with a map rather than list so that all
-- dependencies are properly grouped, without any duplicate keys. But we
-- convert it back to a list so that we can hand it off to 'graphFromEdges'.
-- Reversing the list makes it easy to peek at the return value of this AST later.
depList = L.map (\(a,b) -> (a,a,b)) . M.toList . go M.empty
    where
      go :: M.Map FreeVarsTy [FreeVarsTy] -> Exp2 -> M.Map FreeVarsTy [FreeVarsTy]
      go acc ex =
        case ex of
          VarE v    -> M.insertWith (++) (fromVarToFreeVarsTy v) [(fromVarToFreeVarsTy v)] acc
          LitE{}    -> acc
          CharE{}  -> acc
          FloatE{}  -> acc
          LitSymE{} -> acc
          AppE _ _ _ args   -> foldl go acc args
          PrimAppE _ args -> foldl go acc args
          LetE (v,_,_,rhs) bod ->
            let acc_rhs = go acc rhs
            in go (M.insertWith (++) (fromVarToFreeVarsTy v) (S.toList $ allFreeVars rhs) acc_rhs) bod
          IfE _ b c  -> go (go acc b) c
          MkProdE ls -> foldl go acc ls
          ProjE _ e  -> go acc e
          CaseE (VarE v) mp ->
            L.foldr (\(_,vlocs,e) acc' ->
                       let (vars,locs) = unzip vlocs
                           acc'' = L.foldr (\w acc''' -> M.insertWith (++) (fromVarToFreeVarsTy v) [w] acc''')
                                           acc'
                                           ((map fromVarToFreeVarsTy vars) ++ (map (fromLocVarToFreeVarsTy . toLocVar) locs))
                       in go acc'' e)
                    acc
                    mp
          CaseE _scrt mp -> L.foldr (\(_,_,e) acc' -> go acc' e) acc mp
          DataConE _ _ args -> foldl go acc args
          TimeIt e _ _ -> go acc e
          WithArenaE _ e -> go acc e
          SpawnE _ _ ls  -> foldl go acc ls
          SyncE          -> acc
          MapE{}  -> acc
          FoldE{} -> acc
          Ext ext ->
            case ext of
              Old.LetRegionE r _ _ _ rhs ->
                go (M.insertWith (++) (fromRegVarToFreeVarsTy $ Old.regionToVar r) (S.toList $ allFreeVars rhs) acc) rhs
              Old.LetParRegionE r _ _ rhs ->
                go (M.insertWith (++) (fromRegVarToFreeVarsTy $ Old.regionToVar r) (S.toList $ allFreeVars rhs) acc) rhs
              Old.LetLocE loc phs rhs  ->
                go (M.insertWith (++) (fromLocVarToFreeVarsTy (toLocVar loc)) (dep phs ++ (S.toList $ allFreeVars rhs)) acc) rhs
              Old.RetE{}         -> acc
              Old.FromEndE{}     -> acc
              Old.BoundsCheck{}  -> acc
              Old.IndirectionE{} -> acc
              Old.AddFixed v _   -> M.insertWith (++) (fromVarToFreeVarsTy v) [(fromVarToFreeVarsTy v)] acc
              Old.GetCilkWorkerNum -> acc
              Old.LetAvail _ bod -> go acc bod
              Old.AllocateTagHere{} -> acc
              Old.AllocateScalarsHere{} -> acc
              Old.SSPush{} -> acc
              Old.SSPop{} -> acc
              Old.StartOfPkdCursor cur -> M.insertWith (++) (fromVarToFreeVarsTy cur) [(fromVarToFreeVarsTy cur)] acc
              Old.TagCursor _a _b -> acc --M.insertWith (++) (fromVarToFreeVarsTy b) [(fromVarToFreeVarsTy b)] (M.insertWith (++) (fromVarToFreeVarsTy a) [(fromVarToFreeVarsTy a)] acc)
              Old.LetRegE {} -> error "depList: LetRegE not handled"
              Old.BoundsCheckVector {} -> error "depList: BoundsCheckVector not handled"

      dep :: Old.PreLocExp LocArg -> [FreeVarsTy]
      dep ex =
        case ex of
          Old.StartOfRegionLE r -> [fromRegVarToFreeVarsTy $ Old.regionToVar r]
          Old.AfterConstantLE _ loc   -> [fromLocVarToFreeVarsTy $ toLocVar loc]
          Old.AfterVariableLE v loc _ -> [fromVarToFreeVarsTy v, fromLocVarToFreeVarsTy $ toLocVar loc]
          Old.InRegionLE r  -> [fromRegVarToFreeVarsTy $ Old.regionToVar r]
          Old.FromEndLE loc -> [fromLocVarToFreeVarsTy $ toLocVar loc]
          Old.FreeLE -> []
          Old.GenSoALoc {} -> error "depList: GenSoALoc not handled"
          Old.GetDataConLocSoA {} -> error "depList: GetDataConLocSoA not handled"
          Old.GetFieldLocSoA {} -> error "depList: GetFieldLocSoA not handled"
          Old.AssignLE {} -> error "depList: AssignLE not handled"

-- gFreeVars ++ locations ++ region variables
allFreeVars :: Exp2 -> S.Set FreeVarsTy
allFreeVars ex =
  case ex of
    AppE _ _ locs args -> S.fromList (map (fromLocArgToFreeVarsTy) locs) `S.union` (S.unions (map allFreeVars args))
    PrimAppE _ args -> (S.unions (map allFreeVars args))
    LetE (v,locs,_,rhs) bod -> (S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs) `S.union` (allFreeVars rhs) `S.union` (allFreeVars bod))
                               `S.difference` S.singleton (fromVarToFreeVarsTy v)
    IfE a b c -> allFreeVars a `S.union` allFreeVars b `S.union` allFreeVars c
    MkProdE args -> (S.unions (map allFreeVars args))
    ProjE _ bod -> allFreeVars bod
    CaseE scrt brs -> (allFreeVars scrt) `S.union` (S.unions (map (\(_,vlocs,c) -> allFreeVars c `S.difference`
                                                                                   S.fromList (map (fromVarToFreeVarsTy . fst) vlocs) `S.difference`
                                                                                   S.fromList (map (fromLocVarToFreeVarsTy . toLocVar . snd) vlocs))
                                                                  brs))
    DataConE loc _ args -> S.singleton ((fromLocVarToFreeVarsTy . toLocVar) loc) `S.union` (S.unions (map allFreeVars args))
    TimeIt e _ _ -> allFreeVars e
    WithArenaE _ e -> allFreeVars e
    SpawnE _ locs args -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs) `S.union` (S.unions (map allFreeVars args))
    Ext ext ->
      case ext of
        Old.LetRegionE r _ _ _ bod -> S.delete ((fromRegVarToFreeVarsTy . Old.regionToVar) r) (allFreeVars bod)
        Old.LetParRegionE r _ _ bod -> S.delete ((fromRegVarToFreeVarsTy . Old.regionToVar) r) (allFreeVars bod)
        Old.LetLocE loc locexp bod -> S.difference (allFreeVars bod `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars locexp)) ((S.singleton . fromLocVarToFreeVarsTy) (toLocVar loc))
        Old.StartOfPkdCursor v -> S.singleton (fromVarToFreeVarsTy v)
        Old.TagCursor a b-> S.fromList [((fromLocVarToFreeVarsTy . toLocVar)  a),((fromLocVarToFreeVarsTy . toLocVar) b)]
        Old.RetE locs v     -> S.insert (fromVarToFreeVarsTy v) (S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) locs))
        Old.FromEndE loc    -> S.singleton ((fromLocVarToFreeVarsTy . toLocVar) loc)
        Old.BoundsCheck _ reg cur -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) [reg, cur])
        Old.IndirectionE _ _ (a,b) (c,d) _ -> S.fromList (map (fromLocVarToFreeVarsTy . toLocVar) [a, b, c, d])
        Old.AddFixed v _    -> S.singleton (fromVarToFreeVarsTy v)
        Old.GetCilkWorkerNum-> S.empty
        Old.LetAvail vs bod -> S.fromList (L.map fromVarToFreeVarsTy vs) `S.union` (S.map fromVarToFreeVarsTy $ gFreeVars bod)
        Old.AllocateTagHere loc _ -> S.singleton $ fromLocVarToFreeVarsTy (toLocVar loc)
        Old.AllocateScalarsHere loc -> S.singleton $ fromLocVarToFreeVarsTy (toLocVar loc)
        Old.SSPush _ a b _ -> S.fromList (map fromLocVarToFreeVarsTy [a,b])
        Old.SSPop _ a b -> S.fromList (map fromLocVarToFreeVarsTy [a,b])
        Old.LetRegE {} -> error "allFreeVars: LetRegE not handled"
        Old.BoundsCheckVector {} -> error "allFreeVars: BoundsCheckVector not handled"
    _ -> (S.map fromVarToFreeVarsTy $ gFreeVars ex)

freeLocVars :: Exp2 -> [LocVar]
freeLocVars ex = L.map getLocVarFromFreeVarsTy (S.toList $ (allFreeVars ex))



-- Vidush: I need to make a function that checks wheather a variable is dead or not.
-- In case a addCursor operation is dead code, we should not do a side-effect of bumping 
-- a mutable cursor for it.
isLocAlive :: LocVar -> Exp2 -> Bool -> Bool
isLocAlive loc exp accum = case exp of 
                                VarE{} -> accum
                                LetE (_v,locs,_,rhs) bod -> let check = isLocAliveHelperList loc locs
                                                                checkRhs = isLocAlive loc rhs check
                                                                isAliveBod = isLocAlive loc bod checkRhs
                                                              in isAliveBod
                                LitE{}    -> accum
                                CharE{}  -> accum
                                FloatE{}  -> accum
                                LitSymE{} -> accum
                                AppE _ _ locs args -> let checkArgs = map (\e -> isLocAlive loc e accum) args
                                                          checkArgs' = foldr (\b a -> b || a) False checkArgs
                                                          checkLocs = isLocAliveHelperList loc locs 
                                                        in checkArgs' || checkLocs    
                                PrimAppE _ args -> let checkArgs = map (\e -> isLocAlive loc e accum) args
                                                       checkArgs' = foldr (\b a -> b || a) False checkArgs
                                                     in checkArgs'
                                IfE a b c  -> let checkA = isLocAlive loc a accum
                                                  checkB = isLocAlive loc b checkA 
                                                  checkC = isLocAlive loc c checkB
                                               in checkC
                                MkProdE ls -> let checkLs = map (\e -> isLocAlive loc e accum) ls
                                                  checkLs' = foldr (\b a -> b || a) False checkLs
                                                in checkLs' 
                                ProjE _ e  -> let checkE = isLocAlive loc e accum 
                                               in checkE
                                -- assuming scrutinee is in ANF
                                CaseE (VarE _v) mp ->
                                  L.foldr (\(_,vlocs,e) acc ->
                                            let (_vars,locs) = unzip vlocs
                                                isLocUsedInLst = isLocAliveHelperList loc locs
                                                checkE = isLocAlive loc e (acc || isLocUsedInLst)
                                             in checkE
                                          )
                                          accum
                                          mp
                                DataConE dl _ args -> let locFromLocArg = toLocVar dl
                                                          checkDconLoc = if loc == locFromLocArg 
                                                                         then True 
                                                                         else False
                                                          argsCheck = map (\a -> isLocAlive loc a accum) args
                                                          argsCheck' = foldr (\b a -> b || a) False argsCheck 
                                                        in (checkDconLoc || argsCheck')
                                TimeIt e _ _ -> let checkE = isLocAlive loc e accum 
                                                 in checkE
                                WithArenaE _ e -> let checkE = isLocAlive loc e accum 
                                                   in checkE
                                SpawnE _ lst ls  -> let 
                                                      isLocUsedInLst = isLocAliveHelperList loc lst
                                                      checkLS = map (\a -> isLocAlive loc a accum) ls 
                                                      checkLS' = foldr (\b a -> b || a) False checkLS
                                                     in (checkLS' || isLocUsedInLst)
                                SyncE          -> accum
                                MapE{}  -> accum
                                FoldE{} -> accum
                                Ext ext -> case ext of 
                                                Old.RetE locs _ -> isLocAliveHelperList loc locs
                                                Old.LetRegionE _r _ _ _ bod -> isLocAlive loc bod accum
                                                Old.LetParRegionE _r _ _ bod -> isLocAlive loc bod accum
                                                Old.LetLocE _lc _locexp bod -> let 
                                                                                checkBod = isLocAlive loc bod accum
                                                                               in checkBod
                                                Old.StartOfPkdCursor _v -> accum
                                                Old.TagCursor _a _b -> accum 
                                                Old.FromEndE lc -> let lcl = toLocVar lc
                                                                       checkLC = if lcl == loc 
                                                                                 then True 
                                                                                 else False
                                                                     in (accum || checkLC)
                                                Old.BoundsCheck _ _reg cur -> let curLoc = toLocVar cur 
                                                                                  curCheck = if curLoc == loc 
                                                                                            then True
                                                                                            else False
                                                                               in (accum || curCheck)
                                                Old.IndirectionE _ _ (a,b) (c,d) e -> let 
                                                                                        la = toLocVar a 
                                                                                        lb = toLocVar b 
                                                                                        lc = toLocVar c 
                                                                                        ld = toLocVar d 
                                                                                        checkA = if la == loc then True else False
                                                                                        checkB = if lb == loc then True else False
                                                                                        checkC = if lc == loc then True else False
                                                                                        checkD = if ld == loc then True else False
                                                                                        checkE = isLocAlive loc e accum 
                                                                                      in (checkA || checkB || checkC || checkD || checkE)
                                                Old.AddFixed _v _    -> accum
                                                Old.GetCilkWorkerNum-> accum
                                                Old.LetAvail _vs _bod -> accum
                                                Old.AllocateTagHere lct _ -> let lct'= toLocVar lct 
                                                                               in if lct' == loc 
                                                                                  then True 
                                                                                  else False 
                                                Old.AllocateScalarsHere lct -> let lct' = toLocVar lct 
                                                                                in if lct' == loc 
                                                                                   then True 
                                                                                   else False
                                                Old.SSPush _ _a _b _ -> accum 
                                                Old.SSPop _ _a _b -> accum
                                                Old.LetRegE _ _ bod -> isLocAlive loc bod accum 
                                                Old.BoundsCheckVector {} -> error "allFreeVars: BoundsCheckVector not handled"

                                _ -> accum  


isLocAliveHelperList :: LocVar -> [LocArg] -> Bool
isLocAliveHelperList lc lst = let used = foldr (\li ac -> let li' = toLocVar li 
                                                           in if li' == lc 
                                                              then True
                                                              else ac  
                                               ) False lst
                               in used