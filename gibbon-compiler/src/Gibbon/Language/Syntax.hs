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
    DDefs, TyCon, Tag, IsBoxed, MemoryLayout(..), DDef(..), TailRecType(..)
  , lookupDDef, getConOrdering, getTyOfDataCon, lookupDataCon, lkp
  , lookupDataCon', insertDD, emptyDD, fromListDD, isVoidDDef, 
  getCursorTypeForDataCon, getCursorTypeFromTy, soaBufferedFields

    -- * Function definitions
  , FunctionTy(..), FunDefs, FunDef(..), FunMeta(..), FunRec(..), FunInline(..), FunOpt(..)
  , AbiRole(..), abiPositions
  , insertFD, fromListFD, initFunEnv, initFunEnv'

    -- * Programs
  , Prog(..), progToEnv, getFunTy, progToEnv'

    -- * Environments
  , TyEnv, Env2(..), emptyEnv2
  , extendVEnv, extendsVEnv, lookupVEnv, mblookupVEnv, extendFEnv, lookupFEnv,
    lookupFEnvLocVar, extendVEnvLocVar, extendsVEnvLocVar, lookupVEnvLocVar

    -- * Expresssions and thier types
  , PreExp(..), Prim(..), UrTy(..), IntWidth(..), intWidthBytes, narrowToIntWidth
  , LitAnn(..), litWidth, litWidthL0, intWidthRange, intWidthFits, mkLitE64
  , wrapInt, wrapAdd, wrapSub, wrapMul, wrapNegate, wrapPow
  , ArithError(..), arithErrorMessage, checkedQuot, checkedRem
  , IntPrimAnn(..), intPrimWidth, intPrimAnnOf, setIntPrimWidth, setIntPrimAnn
  , intConvertWidths, intConvertDest
  , isIntArithPrim, isIntCmpPrim, isWidthSensitivePrim
  , addP64, subP64, mulP64, divP64, modP64, expP64
  , eqIntP64, ltP64, gtP64, ltEqP64, gtEqP64, printIntP64

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
#if !MIN_VERSION_base(4,13,0)
-- https://downloads.haskell.org/ghc/8.8.1/docs/html/users_guide/8.8.1-notes.html
import           Control.Monad.Fail(MonadFail(..))
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
--import qualified Data.Typeable as Typeable

import           Gibbon.Common
import GHC.Stack (HasCallStack)

--------------------------------------------------------------------------------
-- Data type definitions
--------------------------------------------------------------------------------

type DDefs a = M.Map Var (DDef a)

type TyCon   = String
type Tag     = Word8

type IsBoxed = Bool


-- | 'MayVectorize' is pure per-function metadata: the user's promise that a
-- function's recursive calls are independent, so it MAY be safely loopified
-- and vectorized. Writing this annotation never itself turns any
-- optimization on -- that is controlled entirely by CLI flags
-- (@--opt-loopification@, @--opt-selective-buffer-sharing@,
-- @--opt-vectorization@). The compiler never mutates this constructor.
--
-- 'Loopified' is the compiler's OWN internal signal, never parsed from
-- source (there is no @OPT:Loopified@ pragma): 'LoopifyTraversals' and
-- 'LoopifyFlatTraversals' stamp it onto a function's 'funOpt' only after
-- successfully rewriting that function into loopified form. Downstream
-- passes ('SelectiveBufferSharing', 'LoopifiedTraversalFusion',
-- 'VectorizeTraversals') key off 'Loopified', not 'MayVectorize' -- a
-- function can carry 'MayVectorize' without loopification having actually
-- succeeded (the pass's own legality checks rejected it), and those
-- downstream passes must not touch such a function.
data FunOpt = MayVectorize
            | StoreScalarCounts
            | SelectiveBufferSharing
            | Loopified
        deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

data MemoryLayout = 
    FullyFactored
  | Linear
  | Mixed -- V.S this is not implemented but it would be nice to support mixed layouts.
    deriving (Read, Show, Eq, Ord, Out, NFData, Generic)

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
                   , dataCons :: [(DataCon,[(IsBoxed,a)])]
                   , memLayout :: MemoryLayout -- | The low level memory layout of the data type
                    }
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

-- | The fields of a fully factored value that get a buffer of their own, in
-- the order the SoA cursor array holds them, with the number of buffers each
-- contributes.
--
-- Note [One enumeration of SoA buffers]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Two things need this list and must agree about it: the cursor array's LENGTH,
-- which is part of every cursorized type, and its LAYOUT -- which buffer holds
-- which constructor field -- which 'Gibbon.Passes.InferLocations.freshSoALoc2'
-- decides.  They are the same list, so they are computed here once.
--
-- A field gets a buffer unless it is a cursor, or a packed field of the type
-- being laid out (which shares its parent's buffers).  A packed field of a
-- DIFFERENT type contributes that type's whole cursor array.
--
-- Random access is where the two readings could come apart.  'AddRAN' replaces
-- a constructor @D@ with a variant @D^@ carrying extra fields, and the layout
-- is over the variant, because that is what the program's case branches are
-- rewritten to.  The two agree on the count only because the fields AddRAN adds
-- are cursors, and cursors get no buffer -- a variant carrying a scalar would
-- silently give the layout more buffers than the type says there are.  That is
-- checked here rather than assumed.
soaBufferedFields :: Out a => DDefs (UrTy a) -> TyCon -> [(DataCon, Int, UrTy a, Int)]
soaBufferedFields ddefs tycon =
  checkRanVariantsAddNoBuffers
    [ (dcon, ix, ty, n)
    | (dcon, flds) <- filterRanDcons' (dataCons ddef)
    , (ix, (_, ty)) <- zip [0 ..] flds
    , Just n <- [bufferCount ty]
    ]
  where
    ddef@DDef{tyName} = lookupDDef ddefs tycon

    bufferCount ty =
      case ty of
        PackedTy tycon' _
          | toVar tycon' == tyName -> Nothing
          | otherwise ->
              case getCursorTypeFromTy tycon' ddefs of
                CursorTy -> Just 1
                CursorArrayTy sz -> Just sz
                _ -> error "soaBufferedFields: unexpected cursor type for a packed field"
        CursorTy -> Nothing
        CursorArrayTy _ -> Nothing
        _ -> Just 1

    -- Keep the `^` variant and drop the constructor it replaced: the layout is
    -- keyed on the constructors the program actually writes.
    filterRanDcons' dcons =
      let replaced = [ init dcon | (dcon, _) <- dcons, "^" `L.isSuffixOf` dcon ]
       in [ d | d@(dcon, _) <- dcons, dcon `notElem` replaced ]

    checkRanVariantsAddNoBuffers out
      | all sameBufferCount ranPairs = out
      | otherwise =
          error $
            "soaBufferedFields: " ++ tycon ++ " has a random-access variant that "
              ++ "adds a buffered field, so its layout and its cursor array "
              ++ "length disagree."
      where
        ranPairs =
          [ (base, variant)
          | (vname, variant) <- dataCons ddef
          , "^" `L.isSuffixOf` vname
          , (bname, base) <- dataCons ddef
          , bname == init vname
          ]
        sameBufferCount (base, variant) =
          buffersOf base == buffersOf variant
        buffersOf flds = sum [ n | (_, ty) <- flds, Just n <- [bufferCount ty] ]

-- | The cursor type a value of this datatype is addressed by: one cursor for a
-- 'Linear' layout, an array of @1 + buffers@ for a 'FullyFactored' one (the
-- tag buffer plus one per buffered field).
getCursorTypeForDataCon :: Out a => DDefs (UrTy a) -> DDef (UrTy a) -> UrTy a
getCursorTypeForDataCon ddefs DDef{tyName, memLayout} =
  case memLayout of
    Linear -> CursorTy
    FullyFactored ->
      CursorArrayTy (1 + sum [ n | (_, _, _, n) <- soaBufferedFields ddefs (fromVar tyName) ])
    _ -> error "Memory Layout is not implemented!"

getCursorTypeFromTy :: Out a => TyCon -> DDefs (UrTy a) -> UrTy a
getCursorTypeFromTy tycon ddefs =
  case memLayout (lookupDDef ddefs tycon) of
    Linear -> CursorTy
    FullyFactored ->
      CursorArrayTy (1 + sum [ n | (_, _, _, n) <- soaBufferedFields ddefs tycon ])
    _ -> error "Memory Layout is not implemented!"

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
type FunDefs var ex = M.Map var (FunDef var ex)

data FunRec = Rec | NotRec | TailRec
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

data FunInline = Inline | NoInline | Inlineable
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

data TailRecType =   UnknownTailType
                   | NotTailRec 
                   | TailCall 
                   | TailModuloCons
                   deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

data FunMeta = FunMeta
  { funRec    :: FunRec
  , funInline :: FunInline
    -- Whether the transitive closure of this function can trigger GC.
  , funCanTriggerGC :: Bool
  , funOpt :: [FunOpt]
  , funCursorAbi :: Maybe [AbiRole]
    -- ^ One role per formal, set by cursorization.  See 'AbiRole'.
    -- 'Nothing' on any function cursorization did not produce.
  }
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

-- | What cursorization made a formal parameter.
--
-- Note [The cursorized calling convention]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'Gibbon.Passes.Cursorize.cursorizeFunDef' builds a cursorized function's
-- parameter list as
--
-- > input region ends ++ output region ends ++ output cursors ++ original args
--
-- and @cursorizeArrowTy@ builds the matching type list the same way, so the
-- convention is positional by construction.  Several later passes need to know
-- which formal plays which role, and each of them used to recover it by
-- re-reading argument order -- four separate derivations of one fact, none of
-- them checked against the construction that decided it.  Recording the roles
-- where they are decided is what makes the convention a single source of truth;
-- a pass that reads this cannot disagree with cursorization about which array
-- is the output.
--
-- A pass handed 'Nothing' must decline rather than guess: that is a function
-- cursorization did not produce, so it has no cursorized convention at all.
data AbiRole
  = AbiInEnd   -- ^ End cursor of an input region.
  | AbiOutEnd  -- ^ End cursor of an output region.
  | AbiOutCur  -- ^ Cursor an output value is written through.
  | AbiInCur   -- ^ An original argument cursorization turned into a read cursor.
  | AbiOther   -- ^ An original argument that stayed a value.
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

-- | Positions of the formals with this role, ascending.
abiPositions :: AbiRole -> [AbiRole] -> [Int]
abiPositions role roles = [ ix | (ix, r) <- zip [0 ..] roles, r == role ]

-- | A function definiton indexed by a type and expression.
data FunDef var ex = FunDef {   funName   :: Var
                              , funArgs   :: [var]
                              , funTy     :: ArrowTy (TyOf ex)
                              , funBody   :: ex
                              , funMeta   :: FunMeta
                            }

deriving instance (Read ex, Read (ArrowTy (TyOf ex)), Read var) => Read (FunDef var ex)
deriving instance (Show ex, Show (ArrowTy (TyOf ex)), Show var) => Show (FunDef var ex)
deriving instance (Eq ex, Eq (ArrowTy (TyOf ex)), Eq var) => Eq (FunDef var ex)
deriving instance (Ord ex, Ord (ArrowTy (TyOf ex)), Ord var) => Ord (FunDef var ex)
deriving instance Generic (FunDef var ex)
deriving instance (Generic (ArrowTy (TyOf ex)), NFData ex, NFData (ArrowTy (TyOf ex)), NFData var) => NFData (FunDef var ex)
deriving instance (Generic (ArrowTy (TyOf ex)), Out ex, Out (ArrowTy (TyOf ex)), Out var) =>  Out (FunDef var ex)

-- | Insert a 'FunDef' into 'FunDefs'.
-- Raise an error if a function with the same name already exists.
insertFD :: FunDef Var ex -> FunDefs Var ex -> FunDefs Var ex
insertFD d = M.insertWith err' (funName d) d
  where
   err' = error $ "insertFD: function definition with duplicate name: "++show (funName d)

insertFD' :: FunDef FreeVarsTy ex -> FunDefs FreeVarsTy ex -> FunDefs FreeVarsTy ex
insertFD' d = M.insertWith err' (fromVarToFreeVarsTy $ funName d) d
  where
   err' = error $ "insertFD: function definition with duplicate name: "++show (funName d)

-- |
fromListFD :: [FunDef Var ex] -> FunDefs Var ex
fromListFD = L.foldr insertFD M.empty

-- |
initFunEnv :: FunDefs Var a -> TyEnv Var (ArrowTy (TyOf a))
initFunEnv fds = M.map funTy fds

initFunEnv' :: FunDefs Var a -> TyEnv FreeVarsTy (ArrowTy (TyOf a))
initFunEnv' fds = let m = M.map funTy fds
                      m' = M.mapKeys fromVarToFreeVarsTy m 
                    in m'

--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

-- | Complete programs include datatype definitions:
--
-- For evaluating a complete program, main's type will be an Int or a
-- datatype.  For running a pass benchmark, main will be Nothing and
-- we will expect a "benchmark" function definition which consumes an
-- appropriate packed AST datatype.
data Prog var ex = Prog { ddefs   :: DDefs (TyOf ex)
                    , fundefs :: FunDefs var ex
                    , mainExp :: Maybe (ex, (TyOf ex))
                    }

-- Since 'FunDef' is defined using a type family, we cannot use the deriving clause.
-- Ryan Scott recommended using singletons-like alternative outlined here:
-- https://lpaste.net/365181
--
deriving instance (Read (TyOf ex), Read ex, Read (ArrowTy (TyOf ex)), Read var, Ord var) => Read (Prog var ex)
deriving instance (Show (TyOf ex), Show ex, Show (ArrowTy (TyOf ex)), Show var) => Show (Prog var ex)
deriving instance (Eq (TyOf ex), Eq ex, Eq (ArrowTy (TyOf ex)), Eq var) => Eq (Prog var ex)
deriving instance (Ord (TyOf ex), Ord ex, Ord (ArrowTy (TyOf ex)), Ord var) => Ord (Prog var ex)
deriving instance Generic (Prog var ex)
deriving instance (NFData (TyOf ex), NFData (ArrowTy (TyOf ex)), NFData ex, Generic (ArrowTy (TyOf ex)), NFData var) => NFData (Prog var ex)

-- | Abstract some of the differences of top level program types, by
--   having a common way to extract an initial environment.  The
--   initial environment has types only for functions.
progToEnv :: Prog Var a -> Env2 Var (TyOf a)
progToEnv Prog{fundefs} = Env2 M.empty (initFunEnv fundefs)

progToEnv' :: Prog Var a -> Env2 FreeVarsTy (TyOf a)
progToEnv' Prog{fundefs} = Env2 M.empty (initFunEnv' fundefs)

-- | Look up the input/output type of a top-level function binding.
getFunTy :: Var -> Prog Var ex -> ArrowTy (TyOf ex)
getFunTy fn Prog{fundefs} =
    case M.lookup fn fundefs of
      Just f -> funTy f
      Nothing -> error $ "getFunTy: L1 program does not contain binding for function: "++show fn

instance (Generic (ArrowTy (TyOf ex)), Out (ArrowTy (TyOf ex)),
          Out (TyOf ex), Out ex, Out var) => Out (Prog var ex)

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | A simple type environment
type TyEnv a b = M.Map a b

emptyTyEnv :: TyEnv a b
emptyTyEnv = M.empty

-- | A common currency for a two part environment consisting of
-- function bindings and regular value bindings.
data Env2 a b = Env2 { vEnv :: TyEnv a b
                     , fEnv :: TyEnv a (ArrowTy b) }

deriving instance (Show (TyOf b), Show b, Show (ArrowTy b), Show a) => Show (Env2 a b)
deriving instance (Read (TyOf b), Read b, Read (ArrowTy b), Show a, Ord a, Read a) => Read (Env2 a b)
deriving instance (Eq (TyOf b), Eq b, Eq (ArrowTy b), Show a, Eq a) => Eq (Env2 a b)
deriving instance (Ord (TyOf b), Ord b, Ord (ArrowTy b), Ord a, Show a) => Ord (Env2 a b)
deriving instance Generic (Env2 a b)
instance (Out a, Out b, Out (ArrowTy b)) => Out (Env2 a b)

emptyEnv2 :: Env2 a b
emptyEnv2 = Env2 { vEnv = emptyTyEnv
                 , fEnv = M.empty }

-- | Extend non-function value environment.
extendVEnv :: Var -> a -> Env2 Var a -> Env2 Var a
extendVEnv v t (Env2 ve fe) = Env2 (M.insert v t ve) fe

extendVEnvLocVar :: FreeVarsTy -> a -> Env2 FreeVarsTy a -> Env2 FreeVarsTy a
extendVEnvLocVar v t (Env2 ve fe) = Env2 (M.insert v t ve) fe

-- | Extend multiple times in one go.
extendsVEnv :: M.Map Var a -> Env2 Var a -> Env2 Var a
extendsVEnv mp (Env2 ve fe) = Env2 (M.union mp ve) fe

extendsVEnvLocVar :: M.Map FreeVarsTy a -> Env2 FreeVarsTy a -> Env2 FreeVarsTy a 
extendsVEnvLocVar mp (Env2 ve fe) = Env2 (M.union mp ve) fe

lookupVEnv :: (HasCallStack, Out a) => Var -> Env2 Var a -> a
lookupVEnv v env2 = (vEnv env2) # v

lookupVEnvLocVar :: (HasCallStack, Out a) => FreeVarsTy -> Env2 FreeVarsTy a -> a 
lookupVEnvLocVar v env2 = (vEnv env2) # v

mblookupVEnv :: Var -> Env2 Var a -> Maybe a
mblookupVEnv cur env2 = M.lookup cur (vEnv env2)

lookupVEnv' :: Var -> Env2 Var a -> Maybe a
lookupVEnv' v (Env2 ve _) = M.lookup v ve

-- | Extend function type environment.
extendFEnv :: Var -> ArrowTy a -> Env2 Var a -> Env2 Var a
extendFEnv v t (Env2 ve fe) = Env2 ve (M.insert v t fe)

lookupFEnv :: Out (ArrowTy a) => Var -> Env2 Var a -> ArrowTy a
lookupFEnv v env2 = (fEnv env2) # v

lookupFEnvLocVar :: Out (ArrowTy a) => FreeVarsTy -> Env2 FreeVarsTy a -> ArrowTy a 
lookupFEnvLocVar loc env2 = (fEnv env2) # loc


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
   | LitE LitAnn Integer   -- ^ Numeric literal, annotated with its width.
     -- ^ Build compiler-generated ones with 'mkLitE64'.
   | CharE Char            -- ^ A character literal
   | FloatE Double         -- ^ Floating point literal
   | LitSymE Var           -- ^ A quoted symbol literal
   | AppE Var TailRecType [loc] [EXP]
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

     -- in L0, loc carries the type of the corresponding var
     -- as there is no location information
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

-- | A compiler-generated 64-bit integer literal: sizes, byte offsets, tags,
-- loop counters, trip counts and the like.  These are fixed-width by
-- construction and are never subject to contextual literal typing.
--
-- Source literals are NOT built with this; the frontend emits
-- @LitE LitUnresolved n@ and lets L0 decide the width.
mkLitE64 :: Int -> PreExp ext loc dec
mkLitE64 n = LitE (LitWidth W64) (toInteger n)

--------------------------------------------------------------------------------
-- Width-sensitive integer primitives
--------------------------------------------------------------------------------

-- | Compiler-generated 64-bit integer primitives: cursor arithmetic, byte
-- offsets, sizes, loop and trip counters, tags.  These are nullary so that
-- migrating a construction site is a token swap, with no parenthesisation.
--
-- Source operators are NOT built with these; the frontends emit
-- @AddP IntPrimUnresolved@ and let L0 infer the width.
addP64, subP64, mulP64, divP64, modP64, expP64 :: Prim ty
addP64 = AddP (IntPrimWidth W64)
subP64 = SubP (IntPrimWidth W64)
mulP64 = MulP (IntPrimWidth W64)
divP64 = DivP (IntPrimWidth W64)
modP64 = ModP (IntPrimWidth W64)
expP64 = ExpP (IntPrimWidth W64)

eqIntP64, ltP64, gtP64, ltEqP64, gtEqP64 :: Prim ty
eqIntP64 = EqIntP (IntPrimWidth W64)
ltP64    = LtP    (IntPrimWidth W64)
gtP64    = GtP    (IntPrimWidth W64)
ltEqP64  = LtEqP  (IntPrimWidth W64)
gtEqP64  = GtEqP  (IntPrimWidth W64)

printIntP64 :: Prim ty
printIntP64 = PrintInt (IntPrimWidth W64)

-- | The width annotation of a width-sensitive integer primitive, if it has
-- one.  'Nothing' for every other primitive.
intPrimAnnOf :: Prim ty -> Maybe IntPrimAnn
intPrimAnnOf p =
  case p of
    AddP a -> Just a ; SubP a -> Just a ; MulP a -> Just a
    DivP a -> Just a ; ModP a -> Just a ; ExpP a -> Just a
    EqIntP a -> Just a ; LtP a -> Just a ; GtP a -> Just a
    LtEqP a -> Just a ; GtEqP a -> Just a
    PrintInt a -> Just a
    IntConvertP a _ -> Just a
    IntToFloatP a -> Just a
    _ -> Nothing

-- | Replace the width annotation of a width-sensitive integer primitive.
-- Any other primitive is returned unchanged.
setIntPrimWidth :: IntWidth -> Prim ty -> Prim ty
setIntPrimWidth w = setIntPrimAnn (IntPrimWidth w)

-- | Replace the annotation of a width-sensitive integer primitive.
--
-- Useful for *normalising* before an equality test or map lookup: the
-- annotation is part of the constructor, so @AddP (IntPrimWidth W8)@ and
-- @AddP IntPrimUnresolved@ are different keys.
setIntPrimAnn :: IntPrimAnn -> Prim ty -> Prim ty
setIntPrimAnn a p =
  case p of
    AddP _ -> AddP a ; SubP _ -> SubP a ; MulP _ -> MulP a
    DivP _ -> DivP a ; ModP _ -> ModP a ; ExpP _ -> ExpP a
    EqIntP _ -> EqIntP a ; LtP _ -> LtP a ; GtP _ -> GtP a
    LtEqP _ -> LtEqP a ; GtEqP _ -> GtEqP a
    PrintInt _ -> PrintInt a
    -- Only the SOURCE annotation is replaced; the destination width is fixed
    -- by the surface primitive and is never inferred.
    IntConvertP _ dst -> IntConvertP a dst
    IntToFloatP _ -> IntToFloatP a
    _ -> p

-- | Binary integer arithmetic: operands and result all share the width.
isIntArithPrim :: Prim ty -> Bool
isIntArithPrim p =
  case p of
    AddP{} -> True ; SubP{} -> True ; MulP{} -> True
    DivP{} -> True ; ModP{} -> True ; ExpP{} -> True
    _ -> False

-- | Binary integer comparison: operands share the width, result is 'BoolTy'.
isIntCmpPrim :: Prim ty -> Bool
isIntCmpPrim p =
  case p of
    EqIntP{} -> True ; LtP{} -> True ; GtP{} -> True
    LtEqP{} -> True ; GtEqP{} -> True
    _ -> False

-- | Every primitive whose typing depends on an integer width annotation.
isWidthSensitivePrim :: Prim ty -> Bool
isWidthSensitivePrim p = isIntArithPrim p || isIntCmpPrim p ||
                         case p of { PrintInt{} -> True
                                   ; IntConvertP{} -> True
                                   ; IntToFloatP{} -> True
                                   ; _ -> False }

-- | The (source, destination) widths of an explicit integer conversion.
--
-- Structural, not an equality test: the annotation is part of the
-- constructor, so comparing against a fixed @IntConvertP IntPrimUnresolved W8@
-- would silently miss every resolved node.
intConvertWidths :: Prim ty -> Maybe (IntWidth, IntWidth)
intConvertWidths p =
  case p of
    IntConvertP a dst -> Just (intPrimWidth a, dst)
    _ -> Nothing

-- | The destination width of an explicit integer conversion, ignoring the
-- (possibly still unresolved) source.  Safe to call inside L0.
intConvertDest :: Prim ty -> Maybe IntWidth
intConvertDest p =
  case p of
    IntConvertP _ dst -> Just dst
    _ -> Nothing


--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

-- | Some of these primitives are (temporarily) tagged directly with
-- their return types.
data Prim ty
          -- | Integer arithmetic.  Width-polymorphic but width-HOMOGENEOUS:
          -- both operands and the result share the annotated width.
          = AddP IntPrimAnn | SubP IntPrimAnn | MulP IntPrimAnn
          | DivP IntPrimAnn | ModP IntPrimAnn  -- ^ Integer division and modulus
          | ExpP IntPrimAnn                    -- ^ Exponentiation
          | RandP              -- ^ Generate a random number.
                               --   Translates to 'rand()' in C.  Always W64.
          -- | Integer comparisons.  Operands share the annotated width; the
          -- result is 'BoolTy', so the result context never selects the width.
          | EqIntP IntPrimAnn  -- ^ Equality on Int
          | LtP IntPrimAnn | GtP IntPrimAnn          -- ^ (<) and (>) for Int's
          | LtEqP IntPrimAnn | GtEqP IntPrimAnn      -- ^ <= and >=
          -- | Explicit, deterministic integer-width conversion.
          --
          -- @IntConvertP src dst@ converts an operand of type @IntTy src@ to
          -- the unique signed @dst@-bit two's-complement value congruent to it
          -- modulo 2^dst.  Truncating, never saturating, never an overflow
          -- report.
          --
          -- INVARIANT: BOTH widths are carried.  The destination alone would
          -- not be enough: every level below L0 must be able to check the
          -- operand's type and the result's type without reconstructing or
          -- guessing the source.  The destination is fixed by the surface name
          -- (@toInt8@ .. @toInt64@) and is concrete from birth; the source
          -- starts 'IntPrimUnresolved' in the Haskell frontend and is resolved
          -- by L0 from the operand (an unconstrained operand defaults to W64).
          -- No unresolved source may cross L0 -> L1; 'toL1Prim' raises an ICE.
          --
          -- The destination context must NEVER select the source: @toInt8 300@
          -- means "convert the Int64 literal 300", not "the Int8 literal 300"
          -- (which would be a spurious range error and would erase the
          -- conversion).  'tcExpChecked' only pushes an expected width into
          -- 'isIntArithPrim' nodes, and this is not one.
          | IntConvertP IntPrimAnn IntWidth
          | FAddP | FSubP | FMulP | FDivP | FExpP | FRandP | EqFloatP | EqCharP | FLtP | FGtP | FLtEqP | FGtEqP | FSqrtP
          -- | Integer -> float.  Carries the operand's exact source width, so
          -- the node stays self-describing and L1-L4 can validate the operand
          -- type rather than assuming W64.  Same unresolved-source rules as
          -- 'IntConvertP'.
          | IntToFloatP IntPrimAnn
          -- | Float -> integer.  Deliberately W64-result-only: there is no
          -- surface syntax for a narrow float->int, and inferring the
          -- destination from context would be exactly the implicit conversion
          -- this design forbids.  Write @toInt8 (floatToInt f)@ instead.
          | FloatToIntP
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

          | PrintInt IntPrimAnn -- ^ Print an integer of the annotated width to standard out
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
-- | Width of a machine integer, in bits.  Gibbon's surface `Int` is `W64`;
-- `Int8`/`Int16`/`Int32`/`Int64` (and the parameterized `Int 8` … `Int 64`)
-- select the others.  Widths never mix implicitly: the only operation that
-- crosses widths is the explicit conversion primitives `toInt8`, `toInt16`,
-- `toInt32` and `toInt64`, which are implemented and work for all sixteen
-- source/destination pairs.  A conversion is a distinct primitive rather than
-- a cast on an existing one, so there is no `IntCastP` constructor.
data IntWidth = W8 | W16 | W32 | W64
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out, Bounded, Enum)

-- | The width annotation carried by a width-sensitive integer primitive
-- (arithmetic, integer comparison, and 'PrintInt').
--
-- Deliberately a distinct type from 'LitAnn', even though the shape matches.
-- A literal's width can be chosen by an expected type flowing inward; an
-- operator's width is fixed by agreement among its operands, and 'PrintInt'
-- has no result context at all.  Keeping the types apart stops 'litWidth' and
-- 'intPrimWidth' being used interchangeably.
--
-- INVARIANT: 'IntPrimUnresolved' appears only in L0, on an operator that came
-- from source and whose width has not been inferred yet.  No unresolved
-- width-sensitive primitive may cross the L0 -> L1 boundary; 'toL1Prim' raises
-- an internal compiler error if one does.
data IntPrimAnn = IntPrimUnresolved
                | IntPrimWidth IntWidth
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out)

-- | The concrete width of a primitive annotation.  Errors on an unresolved
-- one: past L0 that is an internal compiler error, never an excuse to fall
-- back to 'W64'.
intPrimWidth :: IntPrimAnn -> IntWidth
intPrimWidth (IntPrimWidth w) = w
intPrimWidth IntPrimUnresolved =
  error "intPrimWidth: width-sensitive integer primitive still carries an unresolved width; it must be resolved by the end of L0 typechecking."

-- | The width annotation carried by an integer literal.
--
-- A literal that comes from source text starts out as 'LitUnresolved': its
-- width is decided by the context it appears in (see @tcExpChecked@ in
-- "Gibbon.L0.Typecheck"), and an unconstrained one is defaulted to 'W64'
-- exactly once, at the end of L0 typechecking.  Compiler-generated literals
-- (sizes, offsets, loop counters, tags, ...) are built with 'mkLitE64' and are
-- concrete from birth, so \"not inferred yet\" is never confused with
-- \"deliberately 64-bit\".
--
-- INVARIANT: no 'LitUnresolved' survives the L0 -> L1 boundary; 'toL1Exp'
-- raises an internal compiler error if one does.  'litWidth' likewise refuses
-- to guess.
data LitAnn = LitUnresolved
            | LitWidth IntWidth
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out)

-- | The concrete width of a literal annotation.  Errors on an unresolved
-- literal: past L0 that is an internal compiler error, not a defaulting
-- opportunity.
litWidth :: LitAnn -> IntWidth
litWidth (LitWidth w) = w
litWidth LitUnresolved =
  error "litWidth: integer literal still carries an unresolved width; every literal must be resolved by the end of L0 typechecking."

-- | Like 'litWidth', but tolerates an unresolved literal by reporting the
-- width it would default to.  Only L0 itself may use this, because only in L0
-- can a literal legitimately still be unresolved.
litWidthL0 :: LitAnn -> IntWidth
litWidthL0 LitUnresolved = W64
litWidthL0 (LitWidth w)  = w

-- | Signed range of a machine integer of the given width, inclusive.
intWidthRange :: IntWidth -> (Integer, Integer)
intWidthRange w = let bits = 8 * toInteger (intWidthBytes w)
                  in (negate (2 ^ (bits - 1)), 2 ^ (bits - 1) - 1)

-- | Does this value fit in a signed integer of the given width?
intWidthFits :: IntWidth -> Integer -> Bool
intWidthFits w n = let (lo,hi) = intWidthRange w in n >= lo && n <= hi

-- | Size in bytes of a machine integer of the given width.
-- | The unique signed N-bit two's-complement value congruent to @n@ modulo
-- 2^N, for @N@ = the given width's bit count.
--
-- This is THE semantics of the explicit @toInt8@ .. @toInt64@ conversions, and
-- the interpreters and the generated C must agree on it exactly.  Computed in
-- 'Integer', so there is no host-'Int' overflow anywhere along the way; the
-- caller converts to a fixed-width representation only after the result is
-- known to fit.
narrowToIntWidth :: IntWidth -> Integer -> Integer
narrowToIntWidth w n =
  let bits = 8 * toInteger (intWidthBytes w)
      modulus = 2 ^ bits
      half = 2 ^ (bits - 1)
      m = n `mod` modulus          -- Haskell's `mod` is already non-negative here
  in if m < half then m else m - modulus

--------------------------------------------------------------------------------
-- Deterministic integer arithmetic
--------------------------------------------------------------------------------

-- $arith
--
-- THE definition of what @+@, @-@, @*@, @\/@, @%@ and @^@ mean on a Gibbon
-- @Int8@\/@Int16@\/@Int32@\/@Int64@.  Everything that evaluates width-annotated
-- integer arithmetic -- the L1\/L2 interpreter, the L4 interpreter, and any
-- future constant folder -- must call these and nothing else, so that there is
-- exactly one place where the answer is decided and the generated C has
-- exactly one specification to match.
--
-- For width @N@, with @modulus = 2^N@ and @wrap@ = 'wrapInt' (the unique signed
-- @N@-bit two's-complement value congruent modulo @modulus@):
--
-- > a + b     ==  wrap (a + b)
-- > a - b     ==  wrap (a - b)
-- > a * b     ==  wrap (a * b)
-- > negate a  ==  wrap (0 - a)          -- so negate MIN == MIN
-- > a ^ b     ==  wrap (a ^ b)   (b >= 0, by modular repeated squaring)
-- > a ^ b     ==  wrap 1         (b <  0, see 'wrapPow')
-- > a / b     ==  wrap (a `quot` b)     -- truncates toward zero, like C
-- > a % b     ==  wrap (a `rem`  b)     -- sign of the dividend, like C
--
-- and division or remainder by zero is an 'ArithError', never an uncontrolled
-- exception and never C undefined behaviour.
--
-- Two rules about how these are written, both of which have already caused
-- real bugs in this compiler:
--
--   * every intermediate is an 'Integer'.  The overflowing product is NEVER
--     formed in host 'Int' or 'Int64' and normalized afterwards, because that
--     first step is exactly the thing being specified away.
--   * division and remainder use @quot@\/@rem@, NEVER @div@\/@mod@.  Haskell's
--     @div@\/@mod@ floor toward negative infinity (@(-7) \`div\` 3 == -3@)
--     while C's @\/@ and @%@ truncate toward zero (@-7 \/ 3 == -2@).
--     Substituting one for the other silently changes every negative division
--     in every compiled program.

-- | The unique signed value of the given width congruent to the argument
-- modulo 2^N.  Alias of 'narrowToIntWidth', named for its role as the
-- normalizer of arithmetic results rather than as the @toIntN@ conversion.
wrapInt :: IntWidth -> Integer -> Integer
wrapInt = narrowToIntWidth

-- | Modular addition, subtraction and multiplication at the given width.
wrapAdd, wrapSub, wrapMul :: IntWidth -> Integer -> Integer -> Integer
wrapAdd w a b = wrapInt w (a + b)
wrapSub w a b = wrapInt w (a - b)
wrapMul w a b = wrapInt w (a * b)

-- | Modular negation.  Note @wrapNegate w MIN == MIN@: the negation of the most
-- negative value is not representable, and wraps back to itself.  Source-level
-- negation is represented as @0 - a@, so this agrees with 'wrapSub' by
-- construction.
wrapNegate :: IntWidth -> Integer -> Integer
wrapNegate w a = wrapInt w (negate a)

-- | Modular exponentiation at the given width.
--
-- The reduction happens at every squaring step, so the intermediate never
-- exceeds the modulus and a huge exponent costs @O(log e)@ multiplications of
-- bounded numbers rather than @O(e)@ multiplications of growing ones.
--
-- Negative exponent: returns @wrap 1@, for every base and every width.  That
-- is not an arbitrary pick.  Before this was specified, the C helper returned
-- @1@ for a negative exponent for every base except @2@ (where it evaluated
-- @1 << pow@ with a negative shift count -- undefined behaviour), and the
-- interpreter threw @Negative exponent@ instead of producing a value at all.
-- @1@ is what compiled code already produced in the general case and it is
-- total, so it is adopted everywhere and the interpreter is moved onto it.
--
-- @0 ^ 0 == 1@, which both sides already agreed on.
wrapPow :: IntWidth -> Integer -> Integer -> Integer
wrapPow w b e
  | e < 0     = wrapInt w 1
  | otherwise = wrapInt w (go (b `mod` modulus) e 1)
  where
    modulus = 2 ^ (8 * toInteger (intWidthBytes w))
    -- Ordinary square-and-multiply, reducing after every step.  Operating on
    -- the non-negative residues is sound because congruence mod 2^N is
    -- preserved by multiplication; the single 'wrapInt' above maps the final
    -- residue into the signed range.
    go _    0 acc = acc
    go base k acc =
      let acc' = if odd k then (acc * base) `mod` modulus else acc
      in go ((base * base) `mod` modulus) (k `div` 2) acc'

-- | The two ways integer division can fail.  Kept as a datatype rather than a
-- string so that a consumer cannot invent a third case or misspell one, and so
-- that GHC reports every site that has to handle them.
data ArithError = DivideByZero | RemainderByZero
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out)

-- | The user-facing text for a failed division.  The interpreters and the
-- generated C both report exactly this, so a program that dies this way is
-- recognisable regardless of which one ran it.
arithErrorMessage :: ArithError -> String
arithErrorMessage DivideByZero    = "Gibbon: integer division by zero"
arithErrorMessage RemainderByZero = "Gibbon: integer remainder by zero"

-- | Truncating-toward-zero division at the given width, matching C's @\/@.
--
-- @quot@, not @div@.  The only case where the result is not already in range
-- is @MIN \/ -1@, whose true quotient is @2^(N-1)@; 'wrapInt' carries it to
-- @MIN@, which is what two's-complement hardware produces and what C leaves
-- undefined.  A zero divisor is reported rather than evaluated.
checkedQuot :: IntWidth -> Integer -> Integer -> Either ArithError Integer
checkedQuot _ _ 0 = Left DivideByZero
checkedQuot w a b = Right (wrapInt w (a `quot` b))

-- | Remainder with the sign of the dividend at the given width, matching C's
-- @%@.
--
-- @rem@, not @mod@.  @MIN % -1@ is exactly @0@ in 'Integer', so no wrapping is
-- needed for it, but the result is normalized anyway so that the two functions
-- have the same shape and neither can drift.
checkedRem :: IntWidth -> Integer -> Integer -> Either ArithError Integer
checkedRem _ _ 0 = Left RemainderByZero
checkedRem w a b = Right (wrapInt w (a `rem` b))

intWidthBytes :: IntWidth -> Int
intWidthBytes W8  = 1
intWidthBytes W16 = 2
intWidthBytes W32 = 4
intWidthBytes W64 = 8

data UrTy loc
  = IntTy IntWidth
  | CharTy
  | FloatTy
  | SymTy -- ^ Symbols used in writing compiler passes.
  | BoolTy
  | ProdTy [UrTy loc] -- ^ An N-ary tuple
  | SymDictTy (Maybe Var) (UrTy ()) -- ^ A map from SymTy to Ty
          -- ^ We allow built-in dictionaries from symbols to a value type.
  | PackedTy TyCon loc -- ^ No type arguments to TyCons for now.  (No polymorphism.)
  | VectorTy (UrTy loc) -- ^ Vectors are decorated with the types of their elements;
                             -- which can only include scalars or flat products of scalars.
  | SimdTy (UrTy loc) Int -- ^ A fixed-width SIMD register, with element type and lane count.
                          -- This is an internal compiler type, not a heap vector.
  | PDictTy (UrTy loc) (UrTy loc) -- ^ Thread safe dictionaries decorated with
                                    -- key and value type.
  | ListTy (UrTy loc) -- ^ Linked lists are decorated with the types of their elements;
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

        | CursorArrayTy Int -- ^ An array of cursors for reading or writing multiple cursors. 
                            -- ^ The cursor may point to an unkwown type or to a fraction of a complete value.
                            -- ^ It is a machine pointer that can point to any byte.
                            -- ^ The Int is the number of cursors in the array.
        | MutCursorTy -- ^ A reference to a CursorTy. This can be mutated in place.
                        

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
  gFlattenExp :: DDefs (TyOf e) -> Env2 Var (TyOf e) -> e -> PassM e

  -- | A private method.  Gather the bindings from a subexpression,
  -- but do not "discharge" them by creating a let expression.  They
  -- are in order, so later may depend on earlier.
  gFlattenGatherBinds :: DDefs (TyOf e) -> Env2 Var (TyOf e) -> e -> PassM ([Binds e],e)

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
  gRecoverType :: DDefs (TyOf e) -> Env2 Var (TyOf e) -> e -> TyOf e
  gRecoverTypeLoc :: DDefs (TyOf e) -> Env2 FreeVarsTy (TyOf e) -> e -> TyOf e

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

type ValEnv key e = M.Map key (Value e)
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
class Expression e => Interp s e var where
  gInterpExp :: RunConfig -> ValEnv Var e -> DDefs (TyOf e) -> FunDefs var e -> e -> InterpM s e (Value e)

class (Expression e, Expression ext) => InterpExt s e ext var where
  gInterpExt :: RunConfig -> ValEnv Var e -> DDefs (TyOf e) -> FunDefs var e -> ext -> InterpM s e (Value e)

class Interp s e var => InterpProg s e var where
  {-# MINIMAL gInterpProg #-}
  gInterpProg :: s -> RunConfig -> Prog var e -> IO (s, Value e, B.ByteString)

  -- | Interpret while ignoring timing constructs, and dropping the
  -- corresponding output to stdout.
  gInterpNoLogs :: s -> RunConfig -> Prog var e -> String
  gInterpNoLogs s rc p = unsafePerformIO $ show . snd3 <$> gInterpProg s rc p

  -- | Interpret and produce a "log" of output lines, as well as a
  -- final, printed result.  The output lines include timing information.
  gInterpWithStdout :: s -> RunConfig -> Prog var e -> IO (String,[String])
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
             | VLam [Var] e (ValEnv Var e)
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

execAndPrint :: (InterpProg s ex var) => s -> RunConfig -> Prog var ex -> IO ()
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
