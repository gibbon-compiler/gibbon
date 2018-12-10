{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass       #-}

module Gibbon.Language.Syntax
  (
    -- * Datatype definitions
    DDefs, DataCon, TyCon, Tag, IsBoxed, DDef(..)
  , lookupDDef, getConOrdering, getTyOfDataCon, lookupDataCon, lkp
  , insertDD, emptyDD, fromListDD

    -- * Function definitions
  , FunctionTy(..), FunDefs, FunDef(..), insertFD, fromListFD, initFunEnv

    -- * Programs
  , Prog(..), progToEnv, getFunTy

    -- * Generic operations
  , FreeVars(..), Expression(..), Binds, Flattenable(..), Simplifiable(..)
  , Typeable(..)

    -- * Environments
  , TyEnv, Env2(..), emptyEnv2
  , extendVEnv, extendsVEnv, lookupVEnv, extendFEnv

  ) where

import Control.DeepSeq
import Data.Map as M
import Data.List as L
import Data.Loc
import Data.Set as S
import Data.Word ( Word8 )
import Text.PrettyPrint.GenericPretty

import Gibbon.Common

--------------------------------------------------------------------------------
-- Data type definitions
--------------------------------------------------------------------------------

type DDefs a = Map Var (DDef a)

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

-- | Lookup a Datacon.  Return (TyCon, (DataCon, [flds]))
lkp :: Out a => DDefs a -> DataCon -> (Var, (DataCon, [(IsBoxed,a)]))
lkp dds con =
   -- Here we try to lookup in ALL datatypes, assuming unique datacons:
  case [ (tycon,variant)
       | (tycon, DDef{dataCons}) <- M.toList dds
       , variant <- L.filter ((==con). fst) dataCons ] of
    [] -> error$ "lookupDataCon: could not find constructor "++show con
          ++", in datatypes:\n  "++show(doc dds)
    [hit] -> hit
    _ -> error$ "lookupDataCon: found multiple occurences of constructor "++show con
          ++", in datatypes:\n  "++show(doc dds)


insertDD :: DDef a -> DDefs a -> DDefs a
insertDD d = M.insertWith err' (tyName d) d
  where
   err' = error $ "insertDD: data definition with duplicate name: "++show (tyName d)

emptyDD :: DDefs a
emptyDD  = M.empty

fromListDD :: [DDef a] -> DDefs a
fromListDD = L.foldr insertDD M.empty

--------------------------------------------------------------------------------
-- Function definitions
--------------------------------------------------------------------------------

-- | A type family describing function types.
class (Out (ArrowTy ty), Show (ArrowTy ty)) => FunctionTy ty where
  type ArrowTy ty
  inTy  :: ArrowTy ty -> ty
  outTy :: ArrowTy ty -> ty

-- | A set of top-level recursive function definitions.
type FunDefs ex = Map Var (FunDef ex)

-- | A function definiton indexed by a type and expression.
data FunDef ex = FunDef { funName  :: Var
                        , funArg   :: Var
                        , funTy    :: ArrowTy (TyOf ex)
                        , funBody  :: ex
                        }

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


-- | IRs amenable to simplification/inlineTrivs
class Expression e => Simplifiable e where
  gInlineTrivExp :: DDefs (TyOf e) -> e -> e

-- | This is NOT a replacement for any typechecker. This is supposed to be used just to
-- recover the type of an expression in a type-environment
-- Without this, we cannot have truly generic implementation of the Flattenable class,
-- since we need to know the type of an expression before we discharge it with a LetE
class Expression e => Typeable e where
  gTypeExp :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> TyOf e


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
