{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- | An intermediate language with an effect system that captures traversals.

module Packed.FirstOrder.L2.Syntax
    ( Prog(..), FunDef(..), Effect(..), ArrowTy(..)
    , LocRet(..), LocExp, PreLocExp(..)
    , NewFuns, getFunTy
    , progToEnv

    -- * Operations on types
    , allLocVars, inLocVars, outLocVars, outRegVars, substEffs, substTy, prependArgs
    , isPackedTy', locsInTy, initFunEnv, getTyLocs, inRegVars, stripTyLocs

    -- * Temporary backwards compatibility, plus rexports
    , UrTy(..)
    , PreExp(..)
    , pattern SymTy

    -- * Extended language L2.0 with location types.
    , Exp2, E2Ext(..), Ty2

    -- * Other helpers
    , mapPacked, depList, occurs

    -- * Conversion back to L1
    , revertToL1

    {-
    , mapMExprs



    -- The following will be removed:

    -- (Maybe) DEPRECATED:
    -- * Extended "L2.1", for inline packed:
    , pattern NamedVal

    -- DEPRECATED:
    -- * Extended "L2.2", for after cursor insertion:
    , pattern WriteInt, pattern ReadInt, pattern NewBuffer
    , pattern ScopedBuffer, pattern AddCursor
    , isExtendedPattern
    , builtinTEnv
    , includeBuiltins
    -}

    )
    where

import Control.DeepSeq
import Data.List as L
import Data.Loc
import Data.Set as S
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.Common hiding (FunDef)
import Packed.FirstOrder.GenericOps
import Packed.FirstOrder.L1.Syntax hiding
       (FunDef, Prog, mapExprs, progToEnv, fundefs, getFunTy, add1Prog)
import qualified Packed.FirstOrder.L1.Syntax as L1

--------------------------------------------------------------------------------

-- | Extended expressions, L2.  Monomorphic.
--
--   By adding a `LocVar` decoration, all data constructors,
--   applications, and bindings gain a location annotation.
type Exp2 = E2 LocVar Ty2

-- | L1 expressions extended with L2.  This is the polymorphic version.
-- Shorthand for recursions above.
type E2 l d = PreExp E2Ext l d

-- | The extension that turns L1 into L2.
data E2Ext loc dec =
    LetRegionE Region                 (L (E2 loc dec)) -- ^ Not used until later on.
  | LetLocE    loc    (PreLocExp loc) (L (E2 loc dec)) -- ^ Bind a new location.
  | RetE [loc] Var     -- ^ Return a value together with extra loc values.
  | FromEndE loc -- ^ Bind a location from an EndOf location (for RouteEnds and after)
  | BoundsCheck Int loc loc  -- ^ Bytes required, region, write cursor
  | IndirectionE TyCon DataCon (loc,Var) (loc,Var) -- ^ An inter-region indirection
 deriving (Show, Ord, Eq, Read, Generic, NFData)

-- instance Read (E2 l d) where
-- instance Read (L (E2 l d)) where

-- | Define a location in terms of a different location.
data PreLocExp loc = StartOfLE Region
                   | AfterConstantLE Int -- ^ Number of bytes after.
                                    loc  -- ^ Location which this location is offset from.
                   | AfterVariableLE Var -- ^ Name of variable v. This loc is size(v) bytes after.
                                    loc  -- ^ Location which this location is offset from.
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
  type TyOf (E2Ext l d)  = UrTy l
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
      IndirectionE tycon _ _ (to,_) -> PackedTy tycon to


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


----------------------------------------------------------------------------------------------------

-- | Our type for functions grows to include effects, and explicit universal
-- quantification over location/region variables.
data ArrowTy t = ArrowTy
    { locVars :: [LRM]       -- ^ Universally-quantified location params.
                             -- Only these should be referenced in arrIn/arrOut.
    , arrIn :: t             -- ^ Input type for the function.
    , arrEffs:: (Set Effect) -- ^ These are present-but-empty initially,
                             -- and the populated by InferEffects.
    , arrOut:: t             -- ^ Output type for the function.
    , locRets :: [LocRet]    -- ^ L2B feature: multi-valued returns.
    }
  deriving (Read,Show,Eq,Ord, Generic, NFData)

-- | The side-effect of evaluating a function.
data Effect = Traverse LocVar
              -- ^ The function, during its execution, traverses all
              -- of the value living at this location.
  deriving (Read,Show,Eq,Ord, Generic, NFData)

-- instance Out Ty
instance Out t => Out (ArrowTy t)
instance Out Effect
instance Out a => Out (Set a) where
  docPrec n x = docPrec n (S.toList x)
  doc x = doc (S.toList x)
instance Out FunDef
instance Out Prog
instance (Out l, Out d) => Out (E2Ext l d)
instance Out l => Out (PreLocExp l)
instance Out LocRet


-- | L1 Types extended with abstract Locations.
type Ty2 = L1.UrTy LocVar


type NewFuns = M.Map Var FunDef

-- | Here we only change the types of FUNCTIONS:
data Prog = Prog { ddefs    :: DDefs Ty2
                 , fundefs  :: NewFuns
                 , mainExp  :: Maybe (L Exp2, Ty2)
                 }
  deriving (Show, Ord, Eq, Generic, NFData)

----------------------------------------------------------------------------------------------------

-- | Abstract some of the differences of top level program types, by
--   having a common way to extract an initial environment.  The
--   initial environment has types only for functions.
progToEnv :: Prog -> Env2 Ty2
progToEnv Prog{fundefs} =
    Env2 M.empty
         (M.fromList [ (n,(a, b))
                     | FunDef n (ArrowTy _ a _ b _) _ _ <- M.elems fundefs ])


-- | A function definition with the function's effects.
data FunDef = FunDef { funname :: Var
                     , funty   :: (ArrowTy Ty2)
                     , funarg  :: Var
                     , funbod  :: L Exp2 }
  deriving (Show, Ord, Eq, Generic, NFData)
--------------------------------------------------------------------------------

-- | Retrieve the type of a function:
getFunTy :: NewFuns -> Var -> ArrowTy Ty2
getFunTy mp f = case M.lookup f mp of
                  Nothing -> error $ "getFunTy: function was not bound: "++show f
                  Just (FunDef{funty}) -> funty




-- TODO: beta-branch: REVAMP BELOW HERE
--------------------------------------------------------------------------------

-- | Retrieve all LocVars from a fn type (Arrow)
allLocVars :: ArrowTy t -> [LocVar]
allLocVars ty = L.map (\(LRM l _ _) -> l) (locVars ty)


inLocVars :: ArrowTy t -> [LocVar]
inLocVars ty = L.map (\(LRM l _ _) -> l) $
               L.filter (\(LRM _ _ m) -> m == Input) (locVars ty)

outLocVars :: ArrowTy t -> [LocVar]
outLocVars ty = L.map (\(LRM l _ _) -> l) $
                L.filter (\(LRM _ _ m) -> m == Output) (locVars ty)

outRegVars :: ArrowTy t -> [LocVar]
outRegVars ty = L.map (\(LRM _ r _) -> regionVar r) $
                L.filter (\(LRM _ _ m) -> m == Output) (locVars ty)

inRegVars :: ArrowTy t -> [LocVar]
inRegVars ty = nub $ L.map (\(LRM _ r _) -> regionVar r) $
               L.filter (\(LRM _ _ m) -> m == Input) (locVars ty)

-- | Apply a variable substitution to a type.
substTy :: Map LocVar LocVar -> Ty2 -> Ty2
substTy mp t = go t
  where
    go t =
     case t of
      IntTy  -> IntTy
      SymTy  -> SymTy
      BoolTy -> BoolTy
      SymDictTy te -> SymDictTy (go te)
      ProdTy    ts -> ProdTy    (L.map go ts)
      PackedTy k l ->
          case M.lookup l mp of
                Just v  -> PackedTy k v
                Nothing -> PackedTy k l
                -- errorWithStackTrace $ "substTy: failed to find "++show l++
                --   "\n  in map: "++show mp++", when processing type "++show t
      -- TODO(chai):
      PtrTy    -> PtrTy
      CursorTy -> CursorTy
      ListTy _ -> error "tyWithFreshLocs: FIXME implement lists"

-- | Apply a substitution to an effect set.
substEffs :: Map LocVar LocVar -> Set Effect -> Set Effect
substEffs mp ef =
    dbgTrace 5 ("\n  Substituting in effects "++show(mp,ef)) $
    S.map (\(Traverse v) ->
               case M.lookup v mp of
                 Just v2 -> Traverse v2
                 Nothing -> Traverse v) ef

-- Because L2 just adds a bit of metadata and enriched types, it is
-- possible to strip it back down to L1.
revertToL1 :: Prog -> L1.Prog
revertToL1 Prog{ddefs,fundefs,mainExp} =
  L1.Prog ddefs' funefs' mainExp'
  where
    ddefs'   = M.map revertDDef ddefs
    funefs'  = M.map revertFunDef fundefs
    mainExp' = fmap (revertExp . fst) mainExp

    revertDDef :: DDef Ty2 -> DDef Ty1
    revertDDef (DDef a b) =
      DDef a (L.map (\(dcon,tys) -> (dcon, L.map (\(x,y) -> (x, stripTyLocs y)) tys)) b)

    revertFunDef :: FunDef -> (L1.FunDef Ty1 (L L1.Exp1))
    revertFunDef FunDef{funname,funarg,funty,funbod} =
      L1.FunDef { funName  = funname
                , funArg   =  (funarg, stripTyLocs (arrIn funty))
                , funRetTy = stripTyLocs (arrOut funty)
                , funBody  = revertExp funbod
                }

    revertExp :: L Exp2 -> L L1.Exp1
    revertExp (L p ex) = L p $
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v _ arg    -> AppE v [] (revertExp arg)
        PrimAppE p args -> PrimAppE (revertPrim p) $ L.map revertExp args
        LetE (v,_,ty,rhs) bod ->
          LetE (v,[], stripTyLocs ty, revertExp rhs) (revertExp bod)
        IfE a b c  -> IfE (revertExp a) (revertExp b) (revertExp c)
        MkProdE ls -> MkProdE $ L.map revertExp ls
        ProjE i e  -> ProjE i (revertExp e)
        CaseE scrt brs     -> CaseE (revertExp scrt) (L.map docase brs)
        DataConE _ dcon ls -> DataConE () dcon $ L.map revertExp ls
        TimeIt e ty b -> TimeIt (revertExp e) (stripTyLocs ty) b
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
    revertPrim :: Prim Ty2 -> Prim L1.Ty1
    revertPrim pr =
      case pr of
        AddP      -> AddP
        SubP      -> SubP
        MulP      -> MulP
        DivP      -> DivP
        ModP      -> ModP
        EqSymP    -> EqSymP
        EqIntP    -> EqIntP
        LtP       -> LtP
        GtP       -> GtP
        MkTrue    -> MkTrue
        MkFalse   -> MkFalse
        SizeParam -> SizeParam
        SymAppend -> SymAppend
        DictInsertP ty -> DictInsertP (stripTyLocs ty)
        DictLookupP ty -> DictLookupP (stripTyLocs ty)
        DictEmptyP  ty -> DictEmptyP  (stripTyLocs ty)
        DictHasKeyP ty -> DictHasKeyP (stripTyLocs ty)
        ErrorP s ty    -> ErrorP s (stripTyLocs ty)
        ReadPackedFile fp tycon ty -> ReadPackedFile fp tycon (stripTyLocs ty)
        MkNullCursor -> MkNullCursor
        PEndOf -> error "Do not use PEndOf after L2."

    docase :: (DataCon, [(Var,LocVar)], L Exp2) -> (DataCon, [(Var,())], L L1.Exp1)
    docase (dcon,vlocs,rhs) =
      let (vars,_) = unzip vlocs
      in (dcon, zip vars (repeat ()), revertExp rhs)


-- | If a variable occurs in an expression
occurs :: Var -> L Exp2 -> Bool
occurs w (L _ ex) =
  case ex of
    VarE v -> v == w
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

-- Injected cursor args go first in input and output:
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
getTyLocs :: Ty2 -> [LocVar]
-- TODO: could just be a fold
getTyLocs t =
    case t of
      SymTy     -> []
      BoolTy    -> []
      IntTy     -> []
      PackedTy _ v  -> [v]
      ProdTy ls     -> L.concatMap getTyLocs ls
      SymDictTy elt -> getTyLocs elt
      PtrTy    -> []
      CursorTy -> []
      ListTy _ -> error "allLocVars: FIXME lists"

-- | Build a dependency list which can be later converted to a graph
depList :: L Exp2 -> [(Var, Var, [Var])]
-- The `acc` is a map so that all dependencies are properly grouped, without any
-- duplicate keys. But we later convert it into a form expected by `graphFromEdges`.
-- The `reverse` makes it easy to peek at the return value of this AST.
depList = reverse . L.map (\(a,b) -> (a,a,b)) . M.toList . go M.empty
    where
      go acc (L _ ex) =
        case ex of
          LetE (v,_,_,rhs) bod -> go (M.insertWith (++) v (allFreeVars rhs) acc) bod
          CaseE _ mp -> L.foldr (\(_,_,e) acc' -> go acc' e) acc mp
          Ext ext ->
            case ext of
              LetRegionE r rhs ->
                let v = regionVar r
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
          StartOfLE r -> [regionVar r]
          AfterConstantLE _ loc -> [loc]
          AfterVariableLE v loc -> [v,loc]
          InRegionLE r  -> [regionVar r]
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
              LetRegionE r _  -> S.singleton (regionVar r) `S.union` gFreeVars ex
              LetLocE loc _ _ -> S.singleton loc `S.union` gFreeVars ex
              RetE locs _     -> S.fromList locs `S.union` gFreeVars ex
              FromEndE loc    -> S.singleton loc
              BoundsCheck _ reg cur -> S.fromList [reg,cur]
              IndirectionE _ _ (a,b) (c,d) -> S.fromList $ [a,b,c,d]
          _ -> gFreeVars ex


initFunEnv :: NewFuns -> FunEnv Ty2
initFunEnv fds = M.foldr (\fn acc -> let fnty = (funty fn)
                                     in M.insert (funname fn) (arrIn fnty, arrOut fnty) acc)
                 M.empty fds

isPackedTy' :: Ty2 -> Bool
isPackedTy' (PackedTy _ _) = True
isPackedTy' _ = False

locsInTy :: Ty2 -> [LocVar]
locsInTy ty =
    case ty of
      PackedTy _ lv -> [lv]
      ProdTy tys -> concatMap locsInTy tys
      _ -> []


{-

Commenting out unused functions, to make L2 look a bit cleaner. After we finish
writing + verifying Cursorize and other related passes which depend on this,
we can just delete all of these!

-- revertToL1 Prog{ ..} =
--   L1.Prog { L1.ddefs   = fmap (fmap (fmap (const ()))) ddefs
--           , L1.fundefs = M.map go fundefs
--           , L1.mainExp = fmap (exp . fst) mainExp
--           }
--  where
--    go FunDef{..} =
--        let ArrowTy{arrIn,arrOut} = funty in
--        L1.FunDef funname (funarg, stripTyLocs arrIn) (stripTyLocs arrOut) (exp funbod)
--    exp :: E2' () Ty -> L1.Exp
--    exp ex = mapExt (\(e::E2 () Ty) ->
--                     error $ "revertToL1: cannot revert, essential L2 construct used:\n  "++show e)
--                    (fmap stripTyLocs ex)


-- | Collect all the locations mentioned in a type.
_allLocVars :: Ty2 -> [LocVar]
-- TODO: could just be a fold
_allLocVars t =
    case t of
      SymTy     -> []
      BoolTy    -> []
      IntTy     -> []
      PackedTy _ v  -> [v]
      ProdTy ls     -> L.concatMap _allLocVars ls
      SymDictTy elt -> _allLocVars elt
      PtrTy    -> []
      CursorTy -> []
      ListTy _ -> error "allLocVars: FIXME lists"


-- | Retrieve all LocVars mentioned in a type
_getTyLocs :: Ty2 -> Set LocVar
_getTyLocs t =
    case t of
      IntTy  -> S.empty
      SymTy  -> S.empty
      BoolTy -> S.empty
      ProdTy ls     -> S.unions (L.map _getTyLocs ls)
      PackedTy _ lv -> S.singleton lv -- This is a tricky case:
      SymDictTy elt -> _getTyLocs elt
      -- TODO(chai):
      PtrTy    -> S.empty
      CursorTy -> S.empty
      ListTy{} -> error "FINISHLISTS"


-- | Annotate a naked type with fresh location variables.
_tyWithFreshLocs :: Ty1 -> SyM Ty2
_tyWithFreshLocs t =
  case t of
    L1.IntTy    -> return IntTy
    L1.SymTy    -> return SymTy
    L1.BoolTy   -> return BoolTy
    L1.ProdTy l -> ProdTy <$> mapM _tyWithFreshLocs l
    L1.SymDictTy v  -> SymDictTy <$> _tyWithFreshLocs v
    L1.PackedTy _ _ -> error $ "tyWithFreshLocs: unexpected type: " ++ show t
    L1.PtrTy    -> error $ "FINISHME: _tyWithFreshLocs PtrTy"
    L1.CursorTy -> error $ "FINISHME: _tyWithFreshLocs CursorTy"
    L1.ListTy _ -> error "tyWithFreshLocs: FIXME implement lists"


Cursor types encoded into the current language



-- Cursorizing arguments and returns -- abstracting the conventions
--------------------------------------------------------------------------------

-- _addOutputParamArgs = __


-- _addEndWitnessReturns = __

-- Cursorizing types.
--------------------------------------------------------------------------------
-- This happens in two stages, corresponding to the passes RouteEnds
-- and CursorDirect.

-- | Step 1/3: add additional outputs corresponding to
-- end-of-input-value witnesses.  Return the new type and the added
-- outputs.
cursorizeUrTy :: ArrowTy Ty -> (ArrowTy Ty, [LocVar])
cursorizeUrTy (ArrowTy inT ef ouT) = (newArr, newOut)
 where
  newArr = ArrowTy inT ef newOutTy
  newOutTy = prependArgs (L.map mkCursorTy newOut)
                         ouT
  -- Every _traversed_ packed input means a POTENTIAL output (new
  -- return value for the cursor's final value).
  newOut   = [ toEndVar v  -- This determines the ORDER of added inputs.
             | Traverse v <- S.toList ef ] -- ^ Because we traverse all outputs,
                                           -- this effect set  is just what we need.

-- | Step 2/3: continue the conversion by:
--
--  (1) First, adding additional input arguments for the destination
--      cursors to which outputs are written.
--  (2) Packed types in the output then become end-cursors for those
--      same destinations.
--  (3) Packed types in the input STAY non-cursor packed types.
--
--  Results: the new type as well as the extra params added to the
--  input type.
cursorizeTy2 :: ArrowTy Ty -> (ArrowTy Ty, [LocVar])
cursorizeTy2 (ArrowTy inT ef ouT) =  (newArr, newIn)
 where
  newArr   = ArrowTy newInTy ef newOutTy
  newInTy  = prependArgs (L.map mkCursorTy newIn) -- These are cursors
                         inT -- These remain non-cursors.
                         -- (mapPacked (\_ l -> mkCursorTy l) inT)
  -- Let's turn output values into updated-output-cursors:
  -- NOTE: we could distinguish between the (size ef) output cursors
  -- that are already prepended here:
  newOutTy = mapPacked (\_ l -> mkCursorTy (ensureEndVar l)) ouT
  newIn    =
   if S.null ef
   then allLocVars ouT -- These stay in their original order (preorder)
   else -- Strip the added output cursors off before computing this
        let ProdTy ls = ouT in
        allLocVars (ProdTy (L.drop (S.size ef) ls))

-- | Take the final step (3/3)
--   Packed types in the input now become (read-only) cursors.
cursorizeArrty3 :: ArrowTy Ty -> ArrowTy Ty
cursorizeArrty3 arr@(ArrowTy inT ef ouT) =
    if hasRealPacked ouT
    then error $"Bad input to cursorizeArrty3, has non-cursor packed outputs.  Was this put through cursorizeTy2?:+ "
             ++show arr
    else ArrowTy (cursorizeTy3 inT) ef ouT

-- | The non-arrow counterpart to `cursorizeArrTy3`
cursorizeTy3 :: Ty2 -> Ty2
cursorizeTy3  = mapPacked (\ _k l -> mkCursorTy l)


ensureEndVar :: Var -> Var
ensureEndVar v | isEndVar v = v
               | otherwise  = toEndVar v

--------------------------------------------------------------------------------

-- | Map every lexical variable in scope to an abstract location.
--   This is useful for compiler passes that need to track abstract
--   locations of program terms.
type LocEnv = M.Map Var Loc

-- | Convert the type of a function argument to an abstract location
-- for that function argument.
argtyToLoc :: Var -> Ty -> Loc
argtyToLoc v ty =
 case ty of
  PackedTy{}
    | isCursorTy ty -> Fixed $ cursorTyLoc ty
    | otherwise -> Fixed v
    -- ^ Here we set the type based on the variable binding name, not the
    -- quantified loc variable in the type signature.
  (ProdTy ls)   -> TupLoc [argtyToLoc (subloc v i) t | (t,i) <- zip ls [1..]]
   -- ^ Here we generate fixed locations that are *subparts* of the function argument.
  SymTy         -> Bottom
  IntTy         -> Bottom
  BoolTy        -> Bottom
  SymDictTy _t  -> -- ^ This may contain packed objects, but it is not contiguous.
    Fixed v
    -- if hasPacked t then Top else Bottom
  ListTy _ -> error "allLocVars: FIXME lists"


-- A bit of name mangling when promoting lexical variables to location vars
---------------------------------------------------------------------------
-- | First, lift program variables so they don't interfere with ones
-- we introduce.  Also, remove internal underscores.
mangle :: Var -> Var
mangle v = v
-- mangle v = "_" ++ L.filter (/='_') v

-- | Refer to a portion of the data associated with a var.
subloc :: Var -> Int -> Var
subloc v n = varAppend v (toVar (show n))

-- Strip off any subloc modifiers
-- root :: Var -> Var
------------------------------------------------------------

-- | Take a location which is expected to be a single variable, and
-- retrieve that variable.
getLocVar :: Loc -> Maybe Var
getLocVar (Fresh v) = Just v
getLocVar (Fixed v) = Just v
getLocVar Top = Nothing
getLocVar l = error $"getLocVar: expected a single packed value location, got: "
                    ++show(doc l)



-- | We extend the environment when going under lexical binders, which
-- always have fixed abstract locations associated with them.
extendLocEnv :: [(Var,L1.Ty)] -> LocEnv -> SyM LocEnv
extendLocEnv []    e     = return e
extendLocEnv ((v,t):r) e =
    do t' <- tyWithFreshLocs t -- Temp, just to call argtyToLoc.
       extendLocEnv r (M.insert v (argtyToLoc (mangle v) t') e)


-- FIXME: Remove:
mapExprs :: (Env2 (UrTy ()) -> Exp -> Exp) -> Prog -> Prog
mapExprs fn (Prog dd fundefs mainExp) =
    Prog dd
         (fmap (\ (FunDef nm arrTy@(ArrowTy inT _ _) arg bod) ->
                 let env = Env2 (M.singleton arg (fmap (\_->()) inT))
                                funEnv
                 in FunDef nm arrTy arg (fn env bod))
            fundefs)
         -- The function is implicitly assumed not to change the type!
         -- TODO: perhaps should re-infer the type here?
         (fmap (\(e,t) -> (fn (Env2 M.empty funEnv) e, t) ) mainExp)
  where
    funEnv = fEnv $ includeBuiltins $ progToEnv (Prog dd fundefs mainExp)

-- | Map exprs with an initial type environment:
mapMExprs :: Monad m => (Env2 (UrTy LocVar) -> L Exp2 -> m (L Exp2)) -> Prog ->
             m Prog
mapMExprs = error $ "FINISHME: L2 mapMExprs"
-- mapMExprs fn (Prog dd fundefs mainExp) =
--     Prog dd <$>
--          (mapM (\ (FunDef nm arrTy@(ArrowTy inT _ _) arg bod) ->
--                  let env = Env2 (M.singleton arg (fmap (\_->()) inT))
--                                 funEnv
--                  in
--                    FunDef nm arrTy arg <$> (fn env bod))
--             fundefs)
--          <*>
--          (mapM (\ (e,t) ->
--                  (,t) <$> fn (Env2 M.empty funEnv) e) mainExp)
--   where
--     funEnv = fEnv $ includeBuiltins $ progToEnv (Prog dd fundefs mainExp)


--------------------------------------------------------------------------------


-- Conventions encoded inside the existing Core IR
-- =============================================================================

-- For use after inlinePacked / before cursorize:
-------------------------------------------------

-- | Used to inline variable bindings while retaining their (former) name and type.
pattern NamedVal :: forall t t1 (t2 :: * -> * -> *).
                    Var -> t -> L (PreExp t2 t1 t) -> PreExp t2 t1 t
pattern NamedVal vr ty e <- LetE (vr,[],ty,e)
                                  (L _ (VarE (Var "NAMED_VAL_PATTERN_SYN")))
  where NamedVal vr ty e = LetE (vr,[],ty,e)
                                    (L NoLoc (VarE "NAMED_VAL_PATTERN_SYN"))


-- For use after cursorize:
--------------------------------------------------------------------------------

pattern NewBuffer :: forall t t1 (t2 :: * -> * -> *). PreExp t2 t1 t
pattern NewBuffer <- AppE (Var "NewBuffer") [] (L _ (MkProdE []))
  where NewBuffer = AppE "NewBuffer" [] (L NoLoc (MkProdE []))

-- | output buffer space that is known not to escape the current function.
pattern ScopedBuffer :: forall t t1 (t2 :: * -> * -> *). PreExp t2 t1 t
pattern ScopedBuffer <- AppE (Var "ScopedBuffer") [] (L _ (MkProdE []))
  where ScopedBuffer = AppE "ScopedBuffer" [] (L NoLoc (MkProdE []))

-- | Tag writing is still modeled by DataConE.
pattern WriteInt :: forall t t1 (t2 :: * -> * -> *).
                    Var -> L (PreExp t2 t1 t) -> PreExp t2 t1 t
pattern WriteInt v e <- AppE (Var "WriteInt") [] (L _ (MkProdE [L _ (VarE v), e]))
  where WriteInt v e = AppE "WriteInt" [] (L NoLoc (MkProdE [L NoLoc (VarE v), e]))

-- | One cursor in, (int,cursor') output.
pattern ReadInt :: forall t t1 (t2 :: * -> * -> *). Var -> PreExp t2 t1 t
pattern ReadInt v <- AppE (Var "ReadInt") [] (L _ (VarE v))
  where ReadInt v = AppE "ReadInt" [] (L NoLoc (VarE v))

-- | Add a constant offset to a cursor variable.
pattern AddCursor :: forall t t1 (t2 :: * -> * -> *).
                     Var -> Int -> PreExp t2 t1 t
pattern AddCursor v i <- AppE (Var "AddCursor") []
                               (L _ (MkProdE [L _ (VarE v), L _ (LitE i)]))
  where AddCursor v i = AppE "AddCursor" []
                                 (L NoLoc (MkProdE [L NoLoc (VarE v),
                                                    L NoLoc (LitE i)]))


-- | A predicate to check if the form is part of the extended "L2.5" language.
isExtendedPattern :: PreExp l e d -> Bool
isExtendedPattern e =
  case e of
    NewBuffer{}    -> True
    ScopedBuffer{} -> True
    ReadInt{}      -> True
    WriteInt{}     -> True
    AddCursor{}    -> True
    _              -> False


-- Initial type environments
--------------------------------------------------------------------------------

-- | A type environment listing the types of built-in functions.
--
--   Using this table represents a policy decision.  Specifically,
--   that a type checker is relying on the fact that all the L2.5
--   patterns above are valid AppE forms.  The alternative is for that
--   typechecker to match against these patterns before the AppE
--   cases.
--
builtinTEnv :: M.Map Var (ArrowTy L1.Ty1)
builtinTEnv = undefined
  -- M.fromList
  -- [ ("NewBuffer",    ArrowTy voidTy S.empty dummyCursorTy)
  -- , ("ScopedBuffer", ArrowTy voidTy S.empty dummyCursorTy)
  -- , ("ReadInt",      ArrowTy dummyCursorTy S.empty (ProdTy [IntTy, dummyCursorTy]))
  -- , ("WriteInt",     ArrowTy (ProdTy [dummyCursorTy, IntTy]) S.empty dummyCursorTy)
  -- , ("AddCursor",    ArrowTy (ProdTy [dummyCursorTy, IntTy]) S.empty dummyCursorTy)
  -- -- Note: ReadPackedFile is a builtin/primitive.  It is polymorphic,
  -- -- which currently doesn't allow us to model it as a function like
  -- -- this [2017.01.08].
  -- ]

includeBuiltins :: Env2 (UrTy ()) -> Env2 (UrTy ())
includeBuiltins (Env2 _ _) = undefined
    -- Env2 v (f `M.union` f')
    -- where f' = M.fromList [ (n,(fmap (\_->()) a, fmap (\_->()) b))
    --                       | (n, ArrowTy a _ b) <- M.assocs builtinTEnv ]
-}
