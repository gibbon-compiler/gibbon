{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE TemplateHaskell            #-}

module Gibbon.Language.Syntax
  (
    -- * Datatype definitions
    DDefs, DataCon, TyCon, Tag, IsBoxed, DDef(..)
  , lookupDDef, getConOrdering, getTyOfDataCon, lookupDataCon, lkp
  , lookupDataCon', insertDD, emptyDD, fromListDD, isVoidDDef

    -- * Function definitions
  , FunctionTy(..), FunDefs, FunDef(..), FunRec(..), FunInline(..)
  , insertFD, fromListFD, initFunEnv

    -- * Programs
  , Prog(..), progToEnv, getFunTy

    -- * Environments
  , TyEnv, Env2(..), emptyEnv2
  , extendVEnv, extendsVEnv, lookupVEnv, extendFEnv, lookupFEnv

    -- * Expresssions and thier types
  , PreExp(..), Prim(..), UrTy(..)

    -- * Functors for recursion-schemes
  , PreExpF(..), PrimF(..), UrTyF(..)

    -- * Generic operations
  , FreeVars(..), Expression(..), Binds, Flattenable(..)
  , Simplifiable(..), SimplifiableExt(..), Typeable(..)
  , Substitutable(..), SubstitutableExt(..), Renamable(..)

    -- * Helpers for writing instances
  , HasSimplifiable, HasSimplifiableExt, HasSubstitutable, HasSubstitutableExt
  , HasRenamable, HasOut, HasShow, HasEq, HasGeneric, HasNFData

  , -- * Interpreter
    Interp(..), InterpExt(..), InterpProg(..), Value(..), ValEnv, InterpLog,
    InterpM, runInterpM, execAndPrint

  ) where

import           Control.DeepSeq
import           Control.Monad.State
import           Control.Monad.Writer
#if !MIN_VERSION_base(4,15,0)
import           Control.Monad.Fail
#endif
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set as S
import           Data.Word ( Word8 )
import           Data.Kind ( Type )
import           Text.PrettyPrint.GenericPretty
import           Data.Functor.Foldable.TH
import qualified Data.ByteString.Lazy.Char8 as B
import           Data.ByteString.Builder (Builder)
import           System.IO.Unsafe (unsafePerformIO)

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

data FunRec = Rec | NotRec | TailRec
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

data FunInline = Inline | NoInline | Inlineable
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

-- | A function definiton indexed by a type and expression.
data FunDef ex = FunDef { funName   :: Var
                        , funArgs   :: [Var]
                        , funTy     :: ArrowTy (TyOf ex)
                        , funBody   :: ex
                        , funRec    :: FunRec
                        , funInline :: FunInline
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
-- deriving instance (Ord (TyOf a), Ord a, Ord (ArrowTy a)) => Ord (Env2 a)
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
#define EXP (PreExp ext loc dec)

-- | The source language.  It has pointer-based sums and products, as
-- well as packed algebraic datatypes.
--
-- (1) It is parameterized by an a potential extension point.
--
-- (2) It is parameterized by 'loc', the type of locations.
--
-- (3) It is parameterized by a decoration, d, attached to every binder.
--
data PreExp (ext :: Type -> Type -> Type) loc dec =
     VarE Var              -- ^ Variable reference
   | LitE Int              -- ^ Numeric literal
   | CharE Char            -- ^ A character literal
   | FloatE Double         -- ^ Floating point literal
   | LitSymE Var           -- ^ A quoted symbol literal
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

  deriving (Show, Read, Eq, Ord, Generic, NFData, Functor, Foldable, Traversable, Out)


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
          | EqIntP             -- ^ Equality on Int
          | LtP | GtP          -- ^ (<) and (>) for Int's
          | LtEqP | GtEqP      -- ^ <= and >=
          | FAddP | FSubP | FMulP | FDivP | FExpP | FRandP | EqFloatP | EqCharP | FLtP | FGtP | FLtEqP | FGtEqP | FSqrtP | IntToFloatP | FloatToIntP
          | FTanP              -- ^ Translates to 'tan()' in C.
          | EqSymP             -- ^ Equality on Sym
          | EqBenchProgP String
          | OrP | AndP
          | MkTrue  -- ^ Zero argument constructor.
          | MkFalse -- ^ Zero argument constructor.

          | ErrorP String ty
              -- ^ crash and issue a static error message.
              --   To avoid needing inference, this is labeled with a return type.

          | SizeParam

          | IsBig   -- ^ Check the size of constructors with size.
          | GetNumProcessors -- ^ Return the number of processors

          | PrintInt   -- ^ Print an integer to standard out
          | PrintChar   -- ^ Print a character to standard out
          | PrintFloat -- ^ Print a floating point number to standard out
          | PrintBool  -- ^ Print a boolean to standard out
          | PrintSym   -- ^ Print a symbol to standard out
          | ReadInt  -- ^ Read an int from standard in

          -- Dictionaries.

          | DictInsertP ty     -- ^ takes dict, k,v; annotated with element type
          | DictLookupP ty     -- ^ takes dict,k errors if absent; annotated with element type
          | DictEmptyP  ty     -- ^ annotated with element type to avoid ambiguity
          | DictHasKeyP ty     -- ^ takes dict,k; returns a Bool, annotated with element type

          | SymSetEmpty    -- ^ Creates an empty set
          | SymSetInsert   -- ^ Inserts a symbol into a set of symbols
          | SymSetContains -- ^ Queries if a symbol is in a set

          | SymHashEmpty   -- ^ Create empty hash table of symbols
          | SymHashInsert  -- ^ Insert a symbol into a hash table
          | SymHashLookup  -- ^ Look up a symbol in a hash table (takes default symbol)
          | SymHashContains -- ^ Queries if a symbol is in a hash

          | IntHashEmpty   -- ^ Create empty hash table of integers
          | IntHashInsert  -- ^ Insert an integer into a hash table
          | IntHashLookup  -- ^ Look up a integer in a hash table (takes default integer)

          -- Thread safe dictionaries.
          | PDictAllocP  ty ty -- ^ annotated with element type to avoid ambiguity
          | PDictInsertP ty ty -- ^ takes dict, k, v; annotated with element type
          | PDictLookupP ty ty -- ^ takes dict, k. errors if absent; annotated with element type
          | PDictHasKeyP ty ty -- ^ takes dict,k; returns a Bool, annotated with element type
          | PDictForkP ty ty   -- ^ takes dict; returns thread safe safe dicts.
          | PDictJoinP ty ty   -- ^ takes 2 dicts; returns a merged dict.

          -- Linked Lists.
          | LLAllocP ty
          | LLIsEmptyP ty
          | LLConsP ty
          | LLHeadP ty
          | LLTailP ty
          | LLFreeP ty    -- ^ Free the list, and it's data.
          | LLFree2P ty   -- ^ Free list struct, but not it's data.
          | LLCopyP ty    -- ^ Copy the list node.

          -- Operations on vectors
          | VAllocP ty   -- ^ Allocate a vector
          | VFreeP ty    -- ^ Free a vector, and it's data.
          | VFree2P ty   -- ^ Free the vector struct, but not it's data.
          | VLengthP ty -- ^ Length of the vector
          | VNthP ty    -- ^ Fetch the nth element
          | VSliceP ty         -- ^ An efficient slice operation
          | InplaceVUpdateP ty -- ^ Update ith element of the vector
          | VConcatP ty        -- ^ Flatten a vector
          | VSortP ty          -- ^ A sort primop that accepts a function pointer
          | InplaceVSortP ty   -- ^ A sort primop that sorts the array in place
          | VMergeP ty         -- ^ ASSUMPTION: the vectors being merged have the same
                               --   underlying mutable array. This assumption is checked
                               --   at the type level with a Rank-2 type variable. But this
                               --   evidence is erased (by the desugarer) by the time we get
                               --   to L0.

          | Write3dPpmFile FilePath

          | ReadPackedFile (Maybe FilePath) TyCon (Maybe Var) ty
            -- ^ Read (mmap) a binary file containing packed data.  This must be annotated with the
            -- type of the file being read.  The `Ty` tracks the type as the program evolvels
            -- (first PackedTy then CursorTy).  The TyCon tracks the original type name.
            -- The variable represents the region that this file will be mapped to, and is
            -- set by InferLocations.

          | WritePackedFile FilePath ty
            -- ^ Write a packed value to a file.
            -- To enable re-reading this packed value with Gibbon, this primitive gets rid
            -- of any absolute pointers in the value. First, it inlines (by copying) any
            -- regions pointed to by the packed value. Next, random access nodes are eliminated.
            -- We could change them to relative pointers (numeric offsets),
            -- but for a first version we can simplify things by getting rid of them completely.

          | ReadArrayFile (Maybe (FilePath, Int)) ty
            -- ^ Parse a file into a Vector. This is decorated with the
            -- element type. If the element type is a struct,
            -- like (Int, Int) for example, each line must contain 2 numbers
            -- separated by a space. The Int is the number of lines in the
            -- file.

          | RequestEndOf
          -- ^ Conveys a demand for the "end of" some packed value, which is
          -- fulfilled by Cursorize. N.B. the argument must be a VarE that
          -- refers to a packed value.

          | RequestSizeOf
          -- ^ Like 'RequestEndOf' but gets the size of a packed value. Assume
          -- that the value is written in a contiguous region, and size = end_v - v.

          | Gensym

  deriving (Read, Show, Eq, Ord, Generic, NFData, Functor, Foldable, Traversable, Out)


--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Types include boxed/pointer-based products as well as unpacked
-- algebraic datatypes.  This data is parameterized to allow
-- annotation on Packed types later on.
data UrTy a =
          IntTy
        | CharTy
        | FloatTy
        | SymTy -- ^ Symbols used in writing compiler passes.
        | BoolTy
        | ProdTy [UrTy a]     -- ^ An N-ary tuple
        | SymDictTy (Maybe Var) (UrTy ())  -- ^ A map from SymTy to Ty
          -- ^ We allow built-in dictionaries from symbols to a value type.

        | PackedTy TyCon a -- ^ No type arguments to TyCons for now.  (No polymorphism.)

        | VectorTy (UrTy a)  -- ^ Vectors are decorated with the types of their elements;
                             -- which can only include scalars or flat products of scalars.

        | PDictTy (UrTy a) (UrTy a) -- ^ Thread safe dictionaries decorated with
                                    -- key and value type.

        | ListTy (UrTy a) -- ^ Linked lists are decorated with the types of their elements;
                          -- which can only include scalars or flat products of scalars.

        | ArenaTy -- ^ Collection of allocated, non-packed values

        | SymSetTy -- ^ Set of symbols

        | SymHashTy  -- ^ Hash table of symbols

        | IntHashTy -- ^ Hash table of integers

        ---------- These are not used initially ----------------
        -- (They could be added by a later IR instead:)

        | PtrTy -- ^ A machine pointer tvo a complete value in memory.
                -- This is decorated with the region it points into, which
                -- may affect the memory layout.

        | CursorTy -- ^ A cursor for reading or writing, which may point
                   -- to an unkwown type or to a fraction of a complete value.
                   -- It is a machine pointer that can point to any byte.

  deriving (Show, Read, Ord, Eq, Generic, NFData, Functor, Foldable, Traversable, Out)


--------------------------------------------------------------------------------
-- Generic Ops
--------------------------------------------------------------------------------

-- | Expression and program types which support a notion of free variables.
class FreeVars a where
    -- | Return a set of free TERM variables.  Does not return location variables.
    gFreeVars :: a -> S.Set Var


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
                             , SimplifiableExt (PreExp e l d) (e l d)
                             )

type HasSimplifiableExt e l d = ( Show l, Out l, Show d, Out d
                                , Simplifiable (PreExp e l d)
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
                              , SubstitutableExt (PreExp e l d) (e l d)
                              , Eq d, Show d, Out d, Eq l, Show l, Out l
                              , Eq (e l d) )

type HasSubstitutableExt e l d = ( Eq d, Show d, Out d, Eq l, Show l, Out l
                                 , Substitutable (PreExp e l d) )

-- | Alpha renaming, without worrying about name capture -- assuming that Freshen
-- has run before!
class Renamable e where
  gRename :: M.Map Var Var -> e -> e

type HasRenamable e l d = (Renamable l, Renamable d, Renamable (e l d))

-- A convenience wrapper over some of the constraints.
type HasOut ex = (Out ex, Out (TyOf ex), Out (ArrowTy (TyOf ex)))
type HasShow ex = (Show ex, Show (TyOf ex), Show (ArrowTy (TyOf ex)))
type HasEq ex = (Eq ex, Eq (TyOf ex), Eq (ArrowTy (TyOf ex)))
type HasGeneric ex = (Generic ex, Generic (TyOf ex), Generic (ArrowTy (TyOf ex)))
type HasNFData ex = (NFData ex, NFData (TyOf ex), NFData (ArrowTy (TyOf ex)))

--------------------------------------------------------------------------------
-- Things which can be interpreted to yield a final, printed value.
--------------------------------------------------------------------------------

type ValEnv e = M.Map Var (Value e)
type InterpLog = Builder

newtype InterpM s e a = InterpM { unInterpM ::  WriterT InterpLog (StateT s IO) a }
    deriving newtype (Functor, Applicative, Monad, MonadState s, MonadIO, MonadWriter InterpLog)

instance MonadFail (InterpM a b) where
    fail = error

runInterpM :: InterpM s e a -> s -> IO (a, InterpLog, s)
runInterpM m s = do
    ((v,logs), s1) <- runStateT (runWriterT (unInterpM m)) s
    pure (v, logs, s1)

-- | Pure Gibbon programs, at any stage of compilation, should always
-- be evaluatable to a unique value.  The only side effects are timing.
class Expression e => Interp s e where
  gInterpExp :: RunConfig -> ValEnv e -> DDefs (TyOf e) -> FunDefs e -> e -> InterpM s e (Value e)

class (Expression e, Expression ext) => InterpExt s e ext where
  gInterpExt :: RunConfig -> ValEnv e -> DDefs (TyOf e) -> FunDefs e -> ext -> InterpM s e (Value e)

class Interp s e => InterpProg s e where
  {-# MINIMAL gInterpProg #-}
  gInterpProg :: s -> RunConfig -> Prog e -> IO (s, Value e, B.ByteString)

  -- | Interpret while ignoring timing constructs, and dropping the
  -- corresponding output to stdout.
  gInterpNoLogs :: s -> RunConfig -> Prog e -> String
  gInterpNoLogs s rc p = unsafePerformIO $ show . snd3 <$> gInterpProg s rc p

  -- | Interpret and produce a "log" of output lines, as well as a
  -- final, printed result.  The output lines include timing information.
  gInterpWithStdout :: s -> RunConfig -> Prog e -> IO (String,[String])
  gInterpWithStdout s rc p = do
    (_s1,res,logs) <- gInterpProg s rc p
    return (show res, lines (B.unpack logs))


-- | It's a first order language with simple values.
data Value e = VInt Int
             | VChar Char
             | VFloat Double
             | VSym String
             | VBool Bool
             | VDict (M.Map (Value e) (Value e))
             | VProd [(Value e)]
             | VList [(Value e)]
             | VPacked DataCon [(Value e)]
             | VLoc { bufID :: Var, offset :: Int }
             | VCursor { bufID :: Var, offset :: Int }
             | VPtr { bufID :: Var, offset :: Int }
               -- ^ Cursor are a pointer into the Store plus an offset into the Buffer.
             | VLam [Var] e (ValEnv e)
             | VWrapId Int (Value e)
               -- ^ A wrapper for vectors that wraps the value with an "id".
               -- All Inplace* operations use this "id" to update the value
               -- in 'ValEnv'.
  deriving (Read,Eq,Ord,Generic)

instance Out e => Out (Value e)
instance NFData e => NFData (Value e)

instance Show e => Show (Value e) where
 show v =
  case v of
   VInt n   -> show n
   VChar c  -> show c
   VFloat n -> show n
   VSym s   -> "'" ++ s
   VBool b  -> if b then truePrinted else falsePrinted
-- TODO: eventually want Haskell style tuple-printing:
--    VProd ls -> "("++ concat(intersperse ", " (L.map show ls)) ++")"
-- For now match Gibbon's Racket backend
   VProd [] -> ""
   VProd ls -> "'#("++ concat(L.intersperse " " (L.map show ls)) ++")"
   VList ls -> show ls
   VDict m      -> show (M.toList m)
   -- For now, Racket style:
   VPacked k ls -> "(" ++ k ++ concat (L.map ((" "++) . show) ls) ++ ")"
   VLoc buf off -> "<location "++show buf++", "++show off++">"
   VCursor idx off -> "<cursor "++show idx++", "++show off++">"
   VPtr idx off -> "<ptr "++show idx++", "++show off++">"
   VLam args bod env -> "(Clos (lambda (" ++ concat (map ((++" ") . show) args) ++ ") " ++ show bod ++ ") #{" ++ show env ++ "})"
   VWrapId vid val -> "(id: " ++ show vid ++ " " ++ show val ++ ")"

execAndPrint :: (InterpProg s ex) => s -> RunConfig -> Prog ex -> IO ()
execAndPrint s rc prg = do
  (_s1,val,logs) <- gInterpProg s rc prg
  B.putStr logs
  case val of
    -- Special case: don't print void return:
    VProd [] -> return () -- FIXME: remove this.
    _ -> print val

--------------------------------------------------------------------------------

makeBaseFunctor ''PreExp
makeBaseFunctor ''UrTy
makeBaseFunctor ''Prim
