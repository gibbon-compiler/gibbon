{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}

module Gibbon.Language.Syntax
  (
    -- * Datatype definitions
    DDefs, DataCon, TyCon, Tag, IsBoxed, DDef(..)
  , lookupDDef, getConOrdering, getTyOfDataCon, lookupDataCon, lkp
  , lookupDataCon', insertDD, emptyDD, fromListDD, isVoidDDef

    -- * Function definitions
  , FunctionTy(..), FunDefs, FunDef(..), insertFD, fromListFD, initFunEnv

    -- * Programs
  , Prog(..), progToEnv, getFunTy

    -- * Generic operations
  , FreeVars(..), Expression(..), Binds, Flattenable(..)
  , Simplifiable(..), SimplifiableExt(..), Typeable(..)
  , Substitutable(..), SubstitutableExt(..), Renamable(..)

    -- * Helpers for writing instances
  , HasSimplifiable, HasSimplifiableExt, HasSubstitutable, HasSubstitutableExt
  , HasRenamable

    -- * Environments
  , TyEnv, Env2(..), emptyEnv2
  , extendVEnv, extendsVEnv, lookupVEnv, extendFEnv, lookupFEnv

    -- * Expresssions and thier types
  , PreExp(..), Prim(..), UrTy(..)

    -- * Helpers operating on expressions
  , mapExt, mapLocs, mapExprs, mapMExprs, visitExp
  , subst, substE, hasTimeIt, hasSpawns, hasSpawnsProg, projNonFirst
  , mkProj, mkProd, mkLets, flatLets, tuplizeRefs

    -- * Helpers operating on types
  , mkProdTy, projTy , voidTy, isProdTy, isNestedProdTy, isPackedTy, isScalarTy
  , hasPacked, sizeOfTy, primArgsTy, primRetTy, dummyCursorTy, tyToDataCon

    -- * Misc
  , assertTriv, assertTrivs

  ) where

import           Control.DeepSeq
import qualified Data.Map as M
import           Data.List as L
import           Data.Loc
import qualified Data.Set as S
import           Data.Word ( Word8 )
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common

--------------------------------------------------------------------------------
-- Data type definitions
--------------------------------------------------------------------------------

type DDefs a = M.Map Var (DDef a)

type DataCon = String
type TyCon   = String
type Tag     = Word8

type IsBoxed = Bool

-- | Data type definitions.
--
-- Monomorphism: In the extreme case we can strip packed datatypes of
-- all type parameters, or we can allow them to retain type params but
-- require that they always be fully instantiated to monomorphic types
-- in the context of our monomorphic programs.
--
-- Here we allow individual to be marked with whether or not they
-- should be boxed.  We say that a regular, pointer-based datatype has
-- all-boxed fields, whereas a fully serialized datatype has no boxed
-- fields.
data DDef a = DDef { tyName   :: Var
                   , tyArgs   :: [TyVar]
                   , dataCons :: [(DataCon,[(IsBoxed,a)])] }
  deriving (Read, Show, Eq, Ord, Functor, Generic)

instance NFData a => NFData (DDef a) where

instance Out a => Out (DDef a)

-- | Lookup a ddef in its entirety
lookupDDef :: Out a => DDefs a -> TyCon -> DDef a
lookupDDef mp tycon =
    case M.lookup (toVar tycon) mp of
      Just x -> x
      Nothing -> error $ "lookupDDef failed on symbol: "++ tycon ++"\nDDefs: "++sdoc mp

-- | Get the canonical ordering for data constructors, currently based
-- on ordering in the original source code.  Takes a TyCon as argument.
getConOrdering :: Out a => DDefs a -> TyCon -> [DataCon]
getConOrdering dd tycon = L.map fst dataCons
  where DDef{dataCons} = lookupDDef dd tycon

-- | Lookup the name of the TyCon that goes with a given DataCon.
--   Must be unique!
getTyOfDataCon :: Out a => DDefs a -> DataCon -> TyCon
getTyOfDataCon dds con = (fromVar . fst) $ lkp dds con

-- | Lookup the arguments to a data contstructor.
lookupDataCon :: Out a => DDefs a -> DataCon -> [a]
lookupDataCon dds con =
    -- dbgTrace 5 ("lookupDataCon -- "++sdoc(dds,con)) $
    L.map snd $ snd $ snd $ lkp dds con

-- | Like 'lookupDataCon' but lookup arguments to a data contstructor for a
-- specific instance of a datatype.
--
--     lookupDataCon' (Maybe Int) Just = [Int]
lookupDataCon' :: Out a => DDef a -> DataCon -> [a]
lookupDataCon' ddf@DDef{dataCons} con =
   case L.filter ((== con) . fst) dataCons of
     []    -> error$ "lookupDataCon': could not find constructor " ++ show con
              ++ ", in datatype:\n  " ++ sdoc ddf
     [hit] -> L.map snd (snd hit)
     _     -> error$ "lookupDataCon': found multiple occurences of constructor "++show con
              ++ ", in datatype:\n  " ++ sdoc ddf

-- | Lookup a Datacon.  Return (TyCon, (DataCon, [flds]))
lkp :: Out a => DDefs a -> DataCon -> (Var, (DataCon, [(IsBoxed,a)]))
lkp dds con =
   -- Here we try to lookup in ALL datatypes, assuming unique datacons:
  case [ (tycon,variant)
       | (tycon, DDef{dataCons}) <- M.toList dds
       , variant <- L.filter ((==con). fst) dataCons ] of
    [] -> error$ "lookupDataCon: could not find constructor "++show con
          ++", in datatypes:\n  "++sdoc dds
    [hit] -> hit
    _ -> error$ "lookupDataCon: found multiple occurences of constructor "++show con
          ++", in datatypes:\n  "++sdoc dds


insertDD :: DDef a -> DDefs a -> DDefs a
insertDD d = M.insertWith err' (tyName d) d
  where
   err' = error $ "insertDD: data definition with duplicate name: "++show (tyName d)

emptyDD :: DDefs a
emptyDD  = M.empty

fromListDD :: [DDef a] -> DDefs a
fromListDD = L.foldr insertDD M.empty

-- | Is this an empty type (like 'data Void' in Haskell) ?
isVoidDDef :: DDef a -> Bool
isVoidDDef DDef{dataCons} = L.null dataCons

--------------------------------------------------------------------------------
-- Function definitions
--------------------------------------------------------------------------------

-- | A type family describing function types.
class (Out (ArrowTy ty), Show (ArrowTy ty)) => FunctionTy ty where
  type ArrowTy ty
  inTys :: ArrowTy ty -> [ty]
  outTy :: ArrowTy ty -> ty

-- | A set of top-level recursive function definitions.
type FunDefs ex = M.Map Var (FunDef ex)

-- | A function definiton indexed by a type and expression.
data FunDef ex = FunDef { funName  :: Var
                        , funArgs  :: [Var]
                        , funTy    :: ArrowTy (TyOf ex)
                        , funBody  :: ex }

deriving instance (Read ex, Read (ArrowTy (TyOf ex))) => Read (FunDef ex)
deriving instance (Show ex, Show (ArrowTy (TyOf ex))) => Show (FunDef ex)
deriving instance (Eq ex, Eq (ArrowTy (TyOf ex))) => Eq (FunDef ex)
deriving instance (Ord ex, Ord (ArrowTy (TyOf ex))) => Ord (FunDef ex)
deriving instance Generic (FunDef ex)
deriving instance (Generic (ArrowTy (TyOf ex)), NFData ex, NFData (ArrowTy (TyOf ex))) => NFData (FunDef ex)
deriving instance (Generic (ArrowTy (TyOf ex)), Out ex, Out (ArrowTy (TyOf ex))) =>  Out (FunDef ex)

-- | Insert a 'FunDef' into 'FunDefs'.
-- Raise an error if a function with the same name already exists.
insertFD :: FunDef ex -> FunDefs ex -> FunDefs ex
insertFD d = M.insertWith err' (funName d) d
  where
   err' = error $ "insertFD: function definition with duplicate name: "++show (funName d)

-- |
fromListFD :: [FunDef ex] -> FunDefs ex
fromListFD = L.foldr insertFD M.empty

-- |
initFunEnv :: FunDefs a -> TyEnv (ArrowTy (TyOf a))
initFunEnv fds = M.map funTy fds

--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

-- | Complete programs include datatype definitions:
--
-- For evaluating a complete program, main's type will be an Int or a
-- datatype.  For running a pass benchmark, main will be Nothing and
-- we will expect a "benchmark" function definition which consumes an
-- appropriate packed AST datatype.
data Prog ex = Prog { ddefs   :: DDefs (TyOf ex)
                    , fundefs :: FunDefs ex
                    , mainExp :: Maybe (ex, (TyOf ex))
                    }

-- Since 'FunDef' is defined using a type family, we cannot use the deriving clause.
-- Ryan Scott recommended using singletons-like alternative outlined here:
-- https://lpaste.net/365181
--
deriving instance (Read (TyOf ex), Read ex, Read (ArrowTy (TyOf ex))) => Read (Prog ex)
deriving instance (Show (TyOf ex), Show ex, Show (ArrowTy (TyOf ex))) => Show (Prog ex)
deriving instance (Eq (TyOf ex), Eq ex, Eq (ArrowTy (TyOf ex))) => Eq (Prog ex)
deriving instance (Ord (TyOf ex), Ord ex, Ord (ArrowTy (TyOf ex))) => Ord (Prog ex)
deriving instance Generic (Prog ex)
deriving instance (NFData (TyOf ex), NFData (ArrowTy (TyOf ex)), NFData ex, Generic (ArrowTy (TyOf ex))) => NFData (Prog ex)

-- | Abstract some of the differences of top level program types, by
--   having a common way to extract an initial environment.  The
--   initial environment has types only for functions.
progToEnv :: Prog a -> Env2 (TyOf a)
progToEnv Prog{fundefs} = Env2 M.empty (initFunEnv fundefs)

-- | Look up the input/output type of a top-level function binding.
getFunTy :: Var -> Prog ex -> ArrowTy (TyOf ex)
getFunTy fn Prog{fundefs} =
    case M.lookup fn fundefs of
      Just f -> funTy f
      Nothing -> error $ "getFunTy: L1 program does not contain binding for function: "++show fn

instance (Generic (ArrowTy (TyOf ex)), Out (ArrowTy (TyOf ex)),
          Out (TyOf ex), Out ex) => Out (Prog ex)

--------------------------------------------------------------------------------
-- Generic Ops
--------------------------------------------------------------------------------

-- | Expression and program types which support a notion of free variables.
class FreeVars a where
    -- | Return a set of free TERM variables.  Does not return location variables.
    gFreeVars :: a -> S.Set Var

instance FreeVars e => FreeVars (L e) where
  gFreeVars (L _ e) = gFreeVars e


-- | A generic interface to expressions found in different phases of
-- the compiler.
class (Show e, Out e, FreeVars e) => Expression e where
  -- | The type representation used in this expression.
  type TyOf e
  -- | The location (variable) representation used in this expression.
  type LocOf e
  -- | Is an expression considered trivial (duplicatable by the compiler)?
  isTrivial :: e -> Bool


-- | IRs amenable to flattening
class Expression e => Flattenable e where
  -- | Process an expression into a fully-flattened expression which typically includes a
  -- larger number of temporary, local variable bindings.
  gFlattenExp :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> PassM e

  -- | A private method.  Gather the bindings from a subexpression,
  -- but do not "discharge" them by creating a let expression.  They
  -- are in order, so later may depend on earlier.
  gFlattenGatherBinds :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> PassM ([Binds e],e)

type Binds e = (Var,[LocOf e],TyOf e, e)


-- | IRs amenable to simplification/inlineTrivs. Note that there's a
-- separate 'SimplifiableExt' for simplifying extensions. 'Simplifiable' is
-- the only class which makes such a distinction -- b/c when it's simplifying
-- an extension point, the type of the environment would still be 'M.Map Var e',
-- where e is a top-level IR. Right now we don't have a class (and probably
-- don't want to have one as well) which ties an extension point with an IR.
-- Keeping these classes separate works out nicely.
class Expression e => Simplifiable e where
  gInlineTrivExp :: M.Map Var e -> e -> e

class Expression e => SimplifiableExt e ext where
  gInlineTrivExt :: M.Map Var e -> ext -> ext

type HasSimplifiable e l d = ( Show l, Out l, Show d, Out d
                             , Expression (e l d)
                             , SimplifiableExt (L (PreExp e l d)) (e l d)
                             )

type HasSimplifiableExt e l d = ( Show l, Out l, Show d, Out d
                                , Simplifiable (L (PreExp e l d))
                                )


-- | This is NOT a replacement for any typechecker. This only recover type of
-- an expression given a type-environment. Without this, we cannot have truly
-- generic Flattenable, b/c we need to know the type of an expression before we
-- bind it with a LetE.
class Expression e => Typeable e where
  gRecoverType :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> TyOf e

-- | Generic substitution over expressions.
class Expression e => Substitutable e where
  gSubst  :: Var -> e -> e -> e
  gSubstE :: e   -> e -> e -> e

class Expression e => SubstitutableExt e ext where
  gSubstExt  :: Var -> e -> ext -> ext
  gSubstEExt :: e   -> e -> ext -> ext

type HasSubstitutable e l d = ( Expression (e l d)
                              , SubstitutableExt (L (PreExp e l d)) (e l d)
                              , Eq d, Show d, Out d, Eq l, Show l, Out l
                              , Eq (e l d) )

type HasSubstitutableExt e l d = ( Eq d, Show d, Out d, Eq l, Show l, Out l
                                 , Substitutable (L (PreExp e l d)) )

-- | Alpha renaming, without worrying about name capture -- assuming that Freshen
-- has run before!
class Renamable e where
  gRename :: M.Map Var Var -> e -> e

type HasRenamable e l d = (Renamable l, Renamable d, Renamable (e l d))

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | A simple type environment
type TyEnv a = M.Map Var a

emptyTyEnv :: TyEnv a
emptyTyEnv = M.empty

-- | A common currency for a two part environment consisting of
-- function bindings and regular value bindings.
data Env2 a = Env2 { vEnv :: TyEnv a
                   , fEnv :: TyEnv (ArrowTy a) }


deriving instance (Show (TyOf a), Show a, Show (ArrowTy a)) => Show (Env2 a)
deriving instance (Read (TyOf a), Read a, Read (ArrowTy a)) => Read (Env2 a)
deriving instance (Eq (TyOf a), Eq a, Eq (ArrowTy a)) => Eq (Env2 a)
deriving instance (Ord (TyOf a), Ord a, Ord (ArrowTy a)) => Ord (Env2 a)
deriving instance Generic (Env2 a)
instance (Out a, Out (ArrowTy a)) => Out (Env2 a)

emptyEnv2 :: Env2 a
emptyEnv2 = Env2 { vEnv = emptyTyEnv
                 , fEnv = M.empty }

-- | Extend non-function value environment.
extendVEnv :: Var -> a -> Env2 a -> Env2 a
extendVEnv v t (Env2 ve fe) = Env2 (M.insert v t ve) fe

-- | Extend multiple times in one go.
extendsVEnv :: M.Map Var a -> Env2 a -> Env2 a
extendsVEnv mp (Env2 ve fe) = Env2 (M.union mp ve) fe

lookupVEnv :: Out a => Var -> Env2 a -> a
lookupVEnv v env2 = (vEnv env2) # v

-- | Extend function type environment.
extendFEnv :: Var -> ArrowTy a -> Env2 a -> Env2 a
extendFEnv v t (Env2 ve fe) = Env2 ve (M.insert v t fe)

lookupFEnv :: Out (ArrowTy a) => Var -> Env2 a -> ArrowTy a
lookupFEnv v env2 = (fEnv env2) # v

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

-- Shorthand to make the below definition more readable.
-- I.e., this covers all the verbose recursive fields.
#define EXP (L (PreExp ext loc dec))

-- | The source language.  It has pointer-based sums and products, as
-- well as packed algebraic datatypes.
--
-- (1) It is parameterized by an a potential extension point.
--
-- (2) It is parameterized by 'loc', the type of locations.
--
-- (3) It is parameterized by a decoration, d, attached to every binder.
--
data PreExp (ext :: * -> * -> *) loc dec =
     VarE Var              -- ^ Variable reference
   | LitE Int              -- ^ Numeric literal
   | LitSymE Var           -- ^ A quoted symbol literal.
   | AppE Var [loc] [EXP]
     -- ^ Apply a top-level / first-order function.  Instantiate
     -- its type schema by providing location-variable arguments,
     -- if applicable.
   | PrimAppE (Prim dec) [EXP]
     -- ^ Primitive applications don't manipulate locations.
   | LetE (Var,[loc],dec, EXP) -- binding
          EXP                  -- body
    -- ^ One binding at a time.  Allows binding a list of
    -- implicit *location* return vales from the RHS, plus a single "real" value.
    -- This list of implicit returnsb

   | IfE EXP EXP EXP

   -- TODO: eventually tuples will just be a wired-in datatype.
   | MkProdE   [EXP] -- ^ Tuple construction
   | ProjE Int EXP   -- ^ Tuple projection.

   | CaseE EXP [(DataCon, [(Var,loc)], EXP)]
     -- ^ Case on a datatype.  Each bound, unpacked variable lives at
     -- a fixed, read-only location.

   | DataConE loc DataCon [EXP]
     -- ^ Construct data that may unpack some fields.  The location
     -- argument, if applicable, is the byte location at which to
     -- write the tag for the sum type.

   | TimeIt EXP dec Bool
    -- ^ The boolean being true indicates this TimeIt is really (iterate _)
    -- This iterate form is used for criterion-style benchmarking.

   | WithArenaE Var EXP

   | SpawnE Var [loc] [EXP]
   | SyncE

   -- Limited list handling:
   -- TODO: RENAME to "Array".
   -- TODO: Replace with Generate, add array reference.
   | MapE  (Var,dec, EXP) EXP
   | FoldE { initial  :: (Var,dec,EXP)
           , iterator :: (Var,dec,EXP)
           , body     :: EXP }

   ----------------------------------------
  | Ext (ext loc dec) -- ^ Extension point for downstream language extensions.

  deriving (Show, Read, Eq, Ord, Generic, NFData, Functor)
  -- Foldable, Traversable - need instances for L in turn

instance NFData (PreExp e l d) => NFData (L (PreExp e l d)) where
  rnf (L loc a) = seq loc (rnf a)

deriving instance Generic (L (PreExp e l d))

instance (Out l, Show l, Show d, Out d, Expression (e l d))
      => Expression (PreExp e l d) where
  type (TyOf (PreExp e l d))  = d
  type (LocOf (PreExp e l d)) = l
  isTrivial = f
    where
      f :: (PreExp e l d) -> Bool
      f e =
       case e of
        VarE _    -> True
        LitE _    -> True
        LitSymE _ -> True
        -- -- These should really turn to literalS:
        -- -- Commenting out for now because it confuses inference (!)
        -- PrimAppE MkTrue  [] -> True
        -- PrimAppE MkFalse [] -> True
        PrimAppE _ _        -> False

        ----------------- POLICY DECISION ---------------
        -- Leave these tuple ops as trivial for now:
        -- See https://github.com/iu-parfunc/gibbon/issues/86
        --
        -- ProjE _ (L _ et) | f et -> True
        --                  | otherwise -> False
        --
        -- [2018.04.13]:
        -- Turning this off to make tree_lookup go through InferLocs.
        -- The sumUpSetEven examples seems to be working. Maybe we could
        -- hack inferLocs to work around this though.
        -- Double check everything else before merging into master!!!
        ProjE{} -> False
        --
        MkProdE ls -> all (\(L _ x) -> f x) ls

        -- DataCon's are a bit tricky.  May want to inline them at
        -- some point if it avoids region conflicts.
        DataConE{} -> False

        IfE{}      -> False
        CaseE{}    -> False
        LetE {}    -> False
        MapE {}    -> False
        FoldE {}   -> False
        AppE  {}   -> False
        TimeIt {}  -> False
        WithArenaE{} -> False
        SpawnE{}   -> False
        SyncE      -> False
        Ext ext -> isTrivial ext


instance Expression (PreExp e l d) => Expression (L (PreExp e l d)) where
  type (TyOf (L (PreExp e l d)))  = d
  type (LocOf (L (PreExp e l d))) = l
  isTrivial (L _ e) = isTrivial e


-- | Free data variables.  Does not include function variables, which
-- currently occupy a different namespace.  Does not include location/region variables.
instance FreeVars (e l d) => FreeVars (PreExp e l d) where
  gFreeVars ex = case ex of
      VarE v    -> S.singleton v
      LitE _    -> S.empty
      LitSymE _ -> S.empty
      ProjE _ e -> gFreeVars e
      IfE a b c -> gFreeVars a `S.union` gFreeVars b `S.union` gFreeVars c
      AppE _v _ ls         -> S.unions (L.map gFreeVars ls)
      PrimAppE _ ls        -> S.unions (L.map gFreeVars ls)
      LetE (v,_,_,rhs) bod -> gFreeVars rhs `S.union`
                              S.delete v (gFreeVars bod)
      CaseE e ls -> S.union (gFreeVars e)
                    (S.unions $ L.map (\(_, _, ee) -> gFreeVars ee) ls)
      MkProdE ls          -> S.unions $ L.map gFreeVars ls
      DataConE _ _ ls     -> S.unions $ L.map gFreeVars ls
      TimeIt e _ _        -> gFreeVars e
      MapE (v,_t,rhs) bod -> gFreeVars rhs `S.union`
                             S.delete v (gFreeVars bod)
      FoldE (v1,_t1,r1) (v2,_t2,r2) bod ->
          gFreeVars r1 `S.union` gFreeVars r2 `S.union`
          (S.delete v1 $ S.delete v2 $ gFreeVars bod)

      WithArenaE v e -> S.delete v $ gFreeVars e

      SpawnE _ _ ls -> S.unions (L.map gFreeVars ls)
      SyncE -> S.empty

      Ext q -> gFreeVars q


-- | A Typeable instance for L1 and L3 (L2 defines it's own)
instance (Show (), Out (), Expression (e () (UrTy ())),
          TyOf (e () (UrTy ())) ~ TyOf (PreExp e () (UrTy ())),
          FunctionTy (UrTy ()), Typeable (e () (UrTy ())))
       => Typeable (PreExp e () (UrTy ())) where
  gRecoverType ddfs env2 ex =
    case ex of
      VarE v       -> M.findWithDefault (error $ "Cannot find type of variable " ++ show v ++ " in " ++ show (vEnv env2)) v (vEnv env2)
      LitE _       -> IntTy
      LitSymE _    -> SymTy
      AppE v _ _   -> outTy $ fEnv env2 # v
      PrimAppE (DictInsertP ty) ((L _ (VarE v)):_) -> SymDictTy (Just v) $ stripTyLocs ty
      PrimAppE (DictEmptyP  ty) ((L _ (VarE v)):_) -> SymDictTy (Just v) $ stripTyLocs ty
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
      WithArenaE _v e -> gRecoverType ddfs env2 e
      SpawnE v _ _    -> outTy $ fEnv env2 # v
      SyncE           -> voidTy
      CaseE _ mp ->
        let (c,args,e) = head mp
            args' = L.map fst args
        in gRecoverType ddfs (extendsVEnv (M.fromList (zip args' (lookupDataCon ddfs c))) env2) e

instance Typeable (PreExp e l (UrTy l)) => Typeable (L (PreExp e l (UrTy l))) where
  gRecoverType ddfs env2 (L _ ex) = gRecoverType ddfs env2 ex

instance HasSubstitutable e l d => Substitutable (L (PreExp e l d)) where
  gSubst  = subst
  gSubstE = substE

instance Renamable Var where
  gRename env v = M.findWithDefault v v env

instance HasRenamable e l d => Renamable (L (PreExp e l d)) where
  gRename env (L p ex) = L p $
    case ex of
      VarE v -> VarE (go v)
      LitE{}    -> ex
      LitSymE{} -> ex
      AppE f locs args -> AppE (go f) (gol locs) (gol args)
      PrimAppE pr args -> PrimAppE pr (gol args)
      LetE (v,locs,ty,rhs) bod -> LetE (go v, gol locs, go ty, go rhs) (go bod)
      IfE a b c  -> IfE (go a) (go b) (go c)
      MkProdE ls -> MkProdE (gol ls)
      ProjE i e  -> ProjE i (go e)
      CaseE scrt ls ->
        CaseE (go scrt) (map (\(a,b,c) -> (a, map (\(d,e) -> (go d, go e)) b, go c)) ls)
      DataConE loc dcon ls -> DataConE (go loc) dcon (gol ls)
      TimeIt e ty b -> TimeIt (go e) (go ty) b
      SpawnE f locs args -> SpawnE (go f) (gol locs) (gol args)
      SyncE   -> SyncE
      Ext ext -> Ext (go ext)
      MapE{}  -> ex
      FoldE{} -> ex
     where
       go :: forall a. Renamable a => a -> a
       go = gRename env

       gol :: forall a. Renamable a => [a] -> [a]
       gol ls = map go ls

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

-- | Some of these primitives are (temporarily) tagged directly with
-- their return types.
data Prim ty
          = AddP | SubP | MulP -- ^ May need more numeric primitives...
          | DivP | ModP        -- ^ Integer division and modulus
          | ExpP               -- ^ Exponentiation
          | RandP              -- ^ Generate a random number.
                               --   Translates to 'rand()' in C.
                               --   TEMP: It's a side-effect, and should be removed.
          | EqSymP             -- ^ Equality on Sym
          | EqIntP             -- ^ Equality on Int
          | LtP | GtP          -- ^ (<) and (>) for Int's
          | LtEqP | GtEqP      -- ^ <= and >=
          | OrP | AndP
          | SymAppend          -- ^ A quick hack till we have deterministic gensym
          | DictInsertP ty     -- ^ takes dict, k,v; annotated with element type
          | DictLookupP ty     -- ^ takes dict,k errors if absent; annotated with element type
          | DictEmptyP  ty     -- ^ annotated with element type to avoid ambiguity
          | DictHasKeyP ty     -- ^ takes dict,k; returns a Bool, annotated with element type
          | ErrorP String ty
              -- ^ crash and issue a static error message.
              --   To avoid needing inference, this is labeled with a return type.

          | SizeParam

          | MkTrue  -- ^ Zero argument constructor.
          | MkFalse -- ^ Zero argument constructor.

          | PrintInt -- ^ Print an integer to standard out
          | PrintSym -- ^ Print a symbol to standard out
          | ReadInt  -- ^ Read an int from standard in

          | SymSetEmpty    -- ^ Creates an empty set
          | SymSetInsert   -- ^ Inserts a symbol into a set of symbols
          | SymSetContains -- ^ Queries if a symbol is in a set

          | SymHashEmpty   -- ^ Create empty hash table of symbols
          | SymHashInsert  -- ^ Insert a symbol into a hash table
          | SymHashLookup  -- ^ Look up a symbol in a hash table (takes default symbol)

          | IntHashEmpty   -- ^ Create empty hash table of integers
          | IntHashInsert  -- ^ Insert an integer into a hash table
          | IntHashLookup  -- ^ Look up a integer in a hash table (takes default integer)

          | ReadPackedFile (Maybe FilePath) TyCon (Maybe Var) ty
            -- ^ Read (mmap) a binary file containing packed data.  This must be annotated with the
            -- type of the file being read.  The `Ty` tracks the type as the program evolvels
            -- (first PackedTy then CursorTy).  The TyCon tracks the original type name.
            -- The variable represents the region that this file will be mapped to, and is
            -- set by InferLocations.

          | RequestEndOf
          -- ^ Conveys a demand for the "end of" some packed value, which is
          -- fulfilled by Cursorize. N.B. the argument must be a VarE that
          -- refers to a packed value.

          | Gensym

  deriving (Read, Show, Eq, Ord, Generic, NFData, Functor, Foldable, Traversable)

--------------------------------------------------------------------------------
-- Do this manually to get prettier formatting: (Issue #90)

instance Out (PreExp e l d) => Out (L (PreExp e l d)) where
  doc (L _ a)       = doc a
  docPrec n (L _ a) = docPrec n a

instance (Out l, Out d, Out (e l d)) => Out (PreExp e l d)

instance Out d => Out (Prim d)

instance Out a => Out (UrTy a)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Types include boxed/pointer-based products as well as unpacked
-- algebraic datatypes.  This data is parameterized to allow
-- annotation on Packed types later on.
data UrTy a =
          IntTy
        | SymTy -- ^ Symbols used in writing compiler passes.
        | BoolTy
        | ProdTy [UrTy a]     -- ^ An N-ary tuple
        | SymDictTy (Maybe Var) (UrTy ())  -- ^ A map from SymTy to Ty
          -- ^ We allow built-in dictionaries from symbols to a value type.

        | PackedTy TyCon a -- ^ No type arguments to TyCons for now.  (No polymorphism.)

        | ListTy (UrTy a)  -- ^ These are not fully first class.  They are only
                           -- allowed as the fields of data constructors.

        | ArenaTy -- ^ Collection of allocated, non-packed values

        | SymSetTy -- ^ Set of symbols

        | SymHashTy  -- ^ Hash table of symbols

        ---------- These are not used initially ----------------
        -- (They could be added by a later IR instead:)

        | PtrTy -- ^ A machine pointer tvo a complete value in memory.
                -- This is decorated with the region it points into, which
                -- may affect the memory layout.

        | CursorTy -- ^ A cursor for reading or writing, which may point
                   -- to an unkwown type or to a fraction of a complete value.
                   -- It is a machine pointer that can point to any byte.

  deriving (Show, Read, Ord, Eq, Generic, NFData, Functor, Foldable, Traversable)

instance Renamable a => Renamable (UrTy a) where
  gRename env ty =
    case ty of
      IntTy       -> IntTy
      SymTy       -> SymTy
      BoolTy      -> BoolTy
      ProdTy ls   -> ProdTy (map (gRename env) ls)
      SymDictTy a t -> SymDictTy a t
      PackedTy tycon loc -> PackedTy tycon (gRename env loc)
      ListTy loc -> ListTy (gRename env loc)
      PtrTy      -> PtrTy
      CursorTy   -> CursorTy

--------------------------------------------------------------------------------
-- Helpers operating on expressions
--------------------------------------------------------------------------------

-- | Apply a function to the extension points only.
mapExt :: (e1 l d -> e2 l d) -> PreExp e1 l d -> PreExp e2 l d
mapExt fn = visitExp id fn id

-- | Apply a function to the locations only.
mapLocs :: (e l2 d -> e l2 d) -> PreExp e l2 d -> PreExp e l2 d
mapLocs fn = visitExp id fn id

-- | Transform the expressions within a program.
mapExprs :: (e -> e) -> Prog e -> Prog e
mapExprs fn prg@Prog{fundefs,mainExp} =
  let mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (ex,ty) -> Just (fn ex, ty)
  in
  prg{ fundefs = M.map (\g -> g {funBody = fn (funBody g)}) fundefs
     , mainExp =  mainExp' }

-- | Monadic 'mapExprs'.
mapMExprs :: Monad m => (e -> m e) -> Prog e -> m (Prog e)
mapMExprs fn prg@Prog{fundefs,mainExp} = do
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (ex,ty) -> do ex' <- fn ex
                                   pure $ Just (ex', ty)
  fundefs' <- traverse (\g -> do funBody' <- fn (funBody g)
                                 pure $ g {funBody = funBody'})
                       fundefs
  pure $ prg { fundefs = fundefs', mainExp = mainExp' }


-- | Apply a function to the locations, extensions, and
-- binder-decorations, respectively.
visitExp :: forall l1 l2 e1 e2 d1 d2 .
            (l1 -> l2) -> (e1 l1 d1 -> e2 l2 d2) -> (d1 -> d2) ->
            PreExp e1 l1 d1 -> PreExp e2 l2  d2
visitExp _fl fe _fd exp0 = fin
 where
   L _ fin = go (L NoLoc exp0)

   go :: L (PreExp e1 l1  d1) -> L (PreExp e2 l2 d2)
   go (L sloc ex) = L sloc $
     case ex of
       Ext  x        -> Ext (fe x)
       _ -> _finishme


-- | Substitute an expression in place of a variable.
subst :: HasSubstitutable e l d
      => Var -> L (PreExp e l d) -> L (PreExp e l d) -> L (PreExp e l d)
subst old new (L p0 ex) = L p0 $
  let go = subst old new in
  case ex of
    VarE v | v == old  -> unLoc new
           | otherwise -> VarE v
    LitE _             -> ex
    LitSymE _          -> ex
    AppE v loc ls      -> AppE v loc (map go ls)
    PrimAppE p ls      -> PrimAppE p $ L.map go ls
    LetE (v,loc,t,rhs) bod | v == old  -> LetE (v,loc,t,go rhs) bod
                           | otherwise -> LetE (v,loc,t,go rhs) (go bod)
    ProjE i e  -> ProjE i (go e)
    CaseE e ls ->
                  CaseE (go e) (L.map f ls)
                      where f (c,vs,er) = if L.elem old (L.map fst vs)
                                          then (c,vs,er)
                                          else (c,vs,go er)
    MkProdE ls        -> MkProdE $ L.map go ls
    DataConE loc k ls -> DataConE loc k $ L.map go ls
    TimeIt e t b      -> TimeIt (go e) t b
    IfE a b c         -> IfE (go a) (go b) (go c)

    SpawnE v loc ls   -> SpawnE v loc (map go ls)
    SyncE             -> SyncE

    MapE (v,t,rhs) bod | v == old  -> MapE (v,t, rhs)    (go bod)
                       | otherwise -> MapE (v,t, go rhs) (go bod)
    FoldE (v1,t1,r1) (v2,t2,r2) bod ->
        let r1' = if v1 == old then r1 else go r1
            r2' = if v2 == old then r2 else go r2
        in FoldE (v1,t1,r1') (v2,t2,r2') (go bod)

    Ext ext -> Ext (gSubstExt old new ext)

    WithArenaE v e | v == old  -> WithArenaE v e
                   | otherwise -> WithArenaE v (go e)


-- | Expensive 'subst' that looks for a whole matching sub-EXPRESSION.
-- If the old expression is a variable, this still avoids going under binder.
substE :: HasSubstitutable e l d
       => L (PreExp e l d) -> L (PreExp e l d) -> L (PreExp e l d) -> L (PreExp e l d)
substE old new (L p0 ex) = L p0 $
  let go = substE old new in
  case ex of
    _ | ex == unLoc old -> unLoc new

    VarE v          -> VarE v
    LitE _          -> ex
    LitSymE _       -> ex
    AppE v loc ls   -> AppE v loc (map go ls)
    PrimAppE p ls   -> PrimAppE p $ L.map go ls
    LetE (v,loc,t,rhs) bod | (VarE v) == unLoc old  -> LetE (v,loc,t,go rhs) bod
                           | otherwise -> LetE (v,loc,t,go rhs) (go bod)

    ProjE i e         -> ProjE i (go e)
    CaseE e ls        -> CaseE (go e) (L.map (\(c,vs,er) -> (c,vs,go er)) ls)
    MkProdE ls        -> MkProdE $ L.map go ls
    DataConE loc k ls -> DataConE loc k $ L.map go ls
    TimeIt e t b      -> TimeIt (go e) t b
    IfE a b c         -> IfE (go a) (go b) (go c)
    SpawnE v loc ls   -> SpawnE v loc (map go ls)
    SyncE             -> SyncE
    MapE (v,t,rhs) bod | VarE v == unLoc old  -> MapE (v,t, rhs)    (go bod)
                       | otherwise -> MapE (v,t, go rhs) (go bod)
    FoldE (v1,t1,r1) (v2,t2,r2) bod ->
        let r1' = if VarE v1 == unLoc old then r1 else go r1
            r2' = if VarE v2 == unLoc old then r2 else go r2
        in FoldE (v1,t1,r1') (v2,t2,r2') (go bod)

    Ext ext -> Ext (gSubstEExt old new ext)

    WithArenaE v e | (VarE v) == unLoc old -> WithArenaE v e
                   | otherwise -> WithArenaE v (go e)


-- | Does the expression contain a TimeIt form?
hasTimeIt :: L (PreExp e l d) -> Bool
hasTimeIt (L _ rhs) =
    case rhs of
      TimeIt _ _ _ -> True
      DataConE{}   -> False
      VarE _       -> False
      LitE _       -> False
      LitSymE _    -> False
      AppE _ _ _   -> False
      PrimAppE _ _ -> False
      ProjE _ e    -> hasTimeIt e
      MkProdE ls   -> any hasTimeIt ls
      IfE a b c    -> hasTimeIt a || hasTimeIt b || hasTimeIt c
      CaseE _ ls   -> any hasTimeIt [ e | (_,_,e) <- ls ]
      LetE (_,_,_,e1) e2 -> hasTimeIt e1 || hasTimeIt e2
      SpawnE _ _ _       -> False
      SyncE              -> False
      MapE (_,_,e1) e2   -> hasTimeIt e1 || hasTimeIt e2
      FoldE (_,_,e1) (_,_,e2) e3 -> hasTimeIt e1 || hasTimeIt e2 || hasTimeIt e3
      Ext _ -> False
      WithArenaE _ e -> hasTimeIt e

hasSpawnsProg :: Prog (L (PreExp e l d)) -> Bool
hasSpawnsProg (Prog _ fundefs mainExp) =
  any (\FunDef{funBody} -> hasSpawns funBody) (M.elems fundefs) ||
    case mainExp of
      Nothing      -> False
      Just (e,_ty) -> hasSpawns e

-- | Does the expression contain a TimeIt form?
hasSpawns :: L (PreExp e l d) -> Bool
hasSpawns (L _ rhs) =
    case rhs of
      DataConE{}   -> False
      VarE{}       -> False
      LitE{}       -> False
      LitSymE{}    -> False
      AppE{}       -> False
      PrimAppE{}   -> False
      ProjE _ e    -> hasSpawns e
      MkProdE ls   -> any hasSpawns ls
      IfE a b c    -> hasSpawns a || hasSpawns b || hasSpawns c
      CaseE _ ls   -> any hasSpawns [ e | (_,_,e) <- ls ]
      LetE (_,_,_,e1) e2 -> hasSpawns e1 || hasSpawns e2
      SpawnE{}     -> True
      SyncE        -> True
      TimeIt{}     -> False
      MapE (_,_,e1) e2   -> hasSpawns e1 || hasSpawns e2
      FoldE (_,_,e1) (_,_,e2) e3 ->
        hasSpawns e1 || hasSpawns e2 || hasSpawns e3
      Ext _ -> False
      WithArenaE _ e -> hasSpawns e

-- | Project something which had better not be the first thing in a tuple.
projNonFirst :: (Out l, Out d, Out (e l d)) => Int -> L (PreExp e l d) -> L (PreExp e l d)
projNonFirst 0 e = error $ "projNonFirst: expected nonzero index into expr: " ++ sdoc e
projNonFirst i e = L (locOf e) $ ProjE i e

-- | Smart constructor that immediately destroys products if it can:
-- Does NOT avoid single-element tuples.
mkProj :: Int -> L (PreExp e l d) -> L (PreExp e l d)
mkProj ix (L _ (MkProdE ls)) = ls !! ix
mkProj ix e = l$ (ProjE ix e)

-- | Make a product type while avoiding unary products.
mkProd :: [L (PreExp e l d)]-> L (PreExp e l d)
mkProd [e] = e
mkProd ls  = L (locOf $ head ls) $ MkProdE ls

-- | Make a nested series of lets.
mkLets :: [(Var, [loc], dec, L (PreExp ext loc dec))] -> L (PreExp ext loc dec) -> L (PreExp ext loc dec)
mkLets [] bod     = bod
mkLets (b:bs) bod = L NoLoc $ LetE b (mkLets bs bod)

-- | Helper function that lifts out Lets on the RHS of other Lets.
-- Absolutely requires unique names.
mkLetE :: (Var, [l], d, L (PreExp e l d)) -> L (PreExp e l d) -> L (PreExp e l d)
mkLetE (vr,lvs,ty,(L _ (LetE bnd e))) bod = mkLetE bnd $ mkLetE (vr,lvs,ty,e) bod
mkLetE bnd bod = L NoLoc $ LetE bnd bod

-- | Alternative version of L1.mkLets that also flattens
flatLets :: [(Var,[l],d,L (PreExp e l d))] -> L (PreExp e l d) -> L (PreExp e l d)
flatLets [] bod = bod
flatLets (b:bs) bod = mkLetE b (flatLets bs bod)

tuplizeRefs :: Var -> [Var] -> [d] -> L (PreExp e l d) -> L (PreExp e l d)
tuplizeRefs ref vars tys =
  mkLets $
    L.map (\(v,ty,ix) -> (v,[],ty,mkProj ix (l$ VarE ref))) (L.zip3 vars tys [0..])

--------------------------------------------------------------------------------
-- Helpers operating on types
--------------------------------------------------------------------------------

-- | Same as mkProd, at the type level
mkProdTy :: [UrTy a]-> UrTy a
mkProdTy [t] = t
mkProdTy ls  = ProdTy ls

projTy :: (Out a) => Int -> UrTy a -> UrTy a
projTy 0 (ProdTy (ty:_))  = ty
projTy n (ProdTy (_:tys)) = projTy (n-1) (ProdTy tys)
projTy _ ty = error $ "projTy: " ++ sdoc ty ++ " is not a projection!"

-- | A makeshift void type.
voidTy :: UrTy a
voidTy = ProdTy []

-- | Are values of this type tuples ?
isProdTy :: UrTy a -> Bool
isProdTy ProdTy{} = True
isProdTy _ = False

-- | Do values of this type contain nested tuples ?
isNestedProdTy :: UrTy a -> Bool
isNestedProdTy ty =
  case ty of
    ProdTy tys -> if any isProdTy tys
                  then True
                  else False
    _ -> False

-- | Are values of this type Packed ?
isPackedTy :: UrTy a -> Bool
isPackedTy PackedTy{} = True
isPackedTy _ = False

isScalarTy :: UrTy a -> Bool
isScalarTy IntTy  = True
isScalarTy SymTy  = True
isScalarTy BoolTy = True
isScalarTy _      = False


-- | Do values of this type contain packed data?
hasPacked :: Show a => UrTy a -> Bool
hasPacked t =
  case t of
    PackedTy{}     -> True
    ProdTy ls      -> any hasPacked ls
    SymTy          -> False
    BoolTy         -> False
    IntTy          -> False
    SymDictTy _ _  -> False -- hasPacked ty
    ListTy _       -> error "FINISHLISTS"
    PtrTy          -> False
    CursorTy       -> False
    ArenaTy        -> False

-- | Provide a size in bytes, if it is statically known.
sizeOfTy :: UrTy a -> Maybe Int
sizeOfTy t =
  case t of
    PackedTy{}    -> Nothing
    ProdTy ls     -> sum <$> mapM sizeOfTy ls
    SymDictTy _ _ -> Just 8 -- Always a pointer.
    IntTy         -> Just 8
    SymTy         -> Just 4
    BoolTy        -> Just 1
    ListTy _      -> error "FINISHLISTS"
    PtrTy{}       -> Just 8 -- Assuming 64 bit
    CursorTy{}    -> Just 8
    ArenaTy       -> Just 8

-- | Type of the arguments for a primitive operation.
primArgsTy :: Prim (UrTy a) -> [UrTy a]
primArgsTy p =
  case p of
    AddP    -> [IntTy, IntTy]
    SubP    -> [IntTy, IntTy]
    MulP    -> [IntTy, IntTy]
    DivP    -> [IntTy, IntTy]
    ModP    -> [IntTy, IntTy]
    ExpP    -> [IntTy, IntTy]
    RandP   -> []
    EqSymP  -> [SymTy, SymTy]
    EqIntP  -> [IntTy, IntTy]
    LtP  -> [IntTy, IntTy]
    GtP  -> [IntTy, IntTy]
    LtEqP-> [IntTy, IntTy]
    GtEqP-> [IntTy, IntTy]
    OrP  -> [BoolTy, BoolTy]
    AndP -> [BoolTy, BoolTy]
    Gensym  -> []
    MkTrue  -> []
    MkFalse -> []
    SymAppend        -> [SymTy, IntTy]
    SizeParam        -> []
    DictEmptyP _ty   -> []
    DictInsertP _ty  -> error "primArgsTy: dicts not handled yet"
    DictLookupP _ty  -> error "primArgsTy: dicts not handled yet"
    DictHasKeyP _ty  -> error "primArgsTy: dicts not handled yet"
    PrintInt -> [IntTy]
    PrintSym -> [SymTy]
    ReadInt  -> []
    SymSetEmpty -> []
    SymSetInsert -> [SymSetTy, SymTy]
    SymSetContains -> [SymSetTy, SymTy]
    SymHashEmpty -> []
    SymHashInsert -> [SymHashTy,SymTy,SymTy]
    SymHashLookup -> [SymHashTy,SymTy]
    ReadPackedFile{} -> []
    (ErrorP _ _) -> []
    RequestEndOf      -> error "primArgsTy: RequestEndOf not handled yet"

-- | Return type for a primitive operation.
primRetTy :: Prim (UrTy a) -> (UrTy a)
primRetTy p =
  case p of
    AddP -> IntTy
    SubP -> IntTy
    MulP -> IntTy
    DivP -> IntTy
    ModP -> IntTy
    ExpP -> IntTy
    RandP-> IntTy
    Gensym  -> SymTy
    EqSymP  -> BoolTy
    EqIntP  -> BoolTy
    LtP  -> BoolTy
    GtP  -> BoolTy
    OrP  -> BoolTy
    LtEqP-> BoolTy
    GtEqP-> BoolTy
    AndP -> BoolTy
    MkTrue  -> BoolTy
    MkFalse -> BoolTy
    SymAppend      -> SymTy
    SizeParam      -> IntTy
    DictHasKeyP _  -> BoolTy
    DictEmptyP ty  -> SymDictTy Nothing $ stripTyLocs ty
    DictInsertP ty -> SymDictTy Nothing $ stripTyLocs ty
    DictLookupP ty -> ty
    PrintInt -> IntTy
    PrintSym -> SymTy
    ReadInt  -> IntTy
    SymSetEmpty -> SymSetTy
    SymSetInsert -> SymSetTy
    SymSetContains -> BoolTy
    SymHashEmpty -> SymHashTy
    SymHashInsert -> SymHashTy
    SymHashLookup -> SymTy
    (ErrorP _ ty)  -> ty
    ReadPackedFile _ _ _ ty -> ty
    RequestEndOf      -> error "primRetTy: RequestEndOf not handled yet"


dummyCursorTy :: UrTy a
dummyCursorTy = CursorTy

stripTyLocs :: UrTy a -> UrTy ()
stripTyLocs ty =
  case ty of
    IntTy     -> IntTy
    SymTy     -> SymTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map stripTyLocs ls
    SymDictTy v ty'  -> SymDictTy v $ stripTyLocs ty'
    PackedTy tycon _ -> PackedTy tycon ()
    ListTy ty'       -> ListTy $ stripTyLocs ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    SymSetTy -> SymSetTy
    SymHashTy -> SymHashTy


-- | Get the data constructor type from a type, failing if it's not packed
tyToDataCon :: Show a => UrTy a -> DataCon
tyToDataCon (PackedTy dcon _) = dcon
tyToDataCon oth = error $ "tyToDataCon: " ++ show oth ++ " is not packed"

-- | Ensure that an expression is trivial.
assertTriv :: (Expression e) => L e -> a -> a
assertTriv (L _ e) =
  if isTrivial e
  then id
  else error$ "Expected trivial argument, got: "++sdoc e

-- | List version of 'assertTriv'.
assertTrivs :: (Expression e) => [L e] -> a -> a
assertTrivs [] = id
assertTrivs (a:b) = assertTriv a . assertTrivs b
