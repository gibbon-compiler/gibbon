
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Defines the target language for first-order L1 language with C code
-- generator for it.

module Gibbon.L4.Syntax
    ( Var, Tag, Tail(..), Triv(..), Ty(..), Prim(..), FunDecl(..)
    , Alts(..), Prog(..), MainExp(..), Label
    -- * Utility functions
    , withTail
    , fromL3Ty
    ) where

import           Control.DeepSeq
import           Data.Int
import           Data.Maybe
import           GHC.Generics (Generic)
import           Prelude hiding (init)
import           Text.PrettyPrint.GenericPretty (Out (..))

import           Gibbon.Common
import qualified Gibbon.L1.Syntax as L1
import qualified Gibbon.L3.Syntax as L3


--------------------------------------------------------------------------------
-- * AST definition

data Prog = Prog
  { fundefs :: [FunDecl]
  , mainExp :: Maybe MainExp
  } deriving (Show, Ord, Eq, Generic, NFData, Out)

data MainExp
  = PrintExp Tail
      -- ^ Evaluate the expression and print the result. Type of the
      -- expression must will eventually be anything, but not all
      -- types support printing currently [2017.01.03].

  deriving (Show, Ord, Eq, Generic, NFData, Out)

data Triv
    = VarTriv Var
    | IntTriv Int64
    | TagTriv Tag
  deriving (Show, Ord, Eq, Generic, NFData, Out)

-- | Switch alternatives.
data Alts
  = TagAlts [(Tag, Tail)]
      -- ^ Casing on tags.
  | IntAlts [(Int64, Tail)]
      -- ^ Casing on integers.
  deriving (Show, Ord, Eq, Generic, NFData, Out)

instance Out Int64 where
  doc w = doc (fromIntegral w :: Integer)
  docPrec n w = docPrec n (fromIntegral w :: Integer)

type Label = Var

data Tail
    = RetValsT [Triv] -- ^ Only in tail position, for returning from a function.
    | AssnValsT { upd       :: [(Var,Ty,Triv)]
                , bod_maybe :: Maybe Tail
                }

    -- ^ INTERNAL ONLY: used for assigning instead of returning.

    | LetCallT { binds :: [(Var,Ty)],
                 rator :: Var,
                 rands :: [Triv],
                 bod   :: Tail }
    | LetPrimCallT { binds :: [(Var,Ty)],
                     prim  :: Prim,
                     rands :: [Triv],
                     bod   :: Tail }

    -- Ugh, we should not strictly need this if we simplify everything in the right way:
    | LetTrivT { bnd :: (Var,Ty,Triv)
               , bod :: Tail }

    -- A control-flow join point; an If on the RHS of LeT:
    | LetIfT { binds :: [(Var,Ty)]
             , ife :: (Triv,Tail,Tail)
             , bod :: Tail
             }

    | LetUnpackT { binds :: [(Var,Ty)]
                 , ptr :: Var -- ^ Var pointing to a PtrTy
                 , bod :: Tail }
    -- ^ Unpack a struct pointer (variable of PtrTy) into local fields.

    | LetAllocT { lhs  :: Var -- ^ Var to bind to PtrTy
                , vals :: [(Ty,Triv)] -- ^ Fields of allocated struct
                , bod  :: Tail }
    -- ^ Allocate storage for a struct of the given type,
    --   Initialize all fields Return PtrTy.


    | IfT { tst  :: Triv,
            con  :: Tail,
            els  :: Tail }
    | ErrT String

    | LetTimedT { isIter :: Bool   -- ^ Run the RHS multiple times, if true.
                , binds  :: [(Var,Ty)]
                , timed  :: Tail
                , bod    :: Tail } -- ^ This is like a one-armed if.  It needs a struct return.

    | Switch Label Triv Alts (Maybe Tail) -- TODO: remove maybe on default case
    -- ^ For casing on numeric tags or integers.
    | TailCall Var [Triv]
    | Goto Label
  deriving (Show, Ord, Eq, Generic, NFData, Out)

data Ty
    = IntTy
    | TagTyPacked  -- ^ A single byte / Word8.  Used in PACKED mode.
    | TagTyBoxed   -- ^ A tag used in the UNPACKED, boxed, pointer-based, graph-of-structs representation.
                   --   This can usually be the same as TagTy, but needn't necessarily be.

    | SymTy    -- ^ Symbols used in writing compiler passes.
               --   It's an alias for Int, an index into a symbol table.

    | CursorTy -- ^ A byte-indexing pointer.  This is always a pointer to a raw buffer of
               -- bytes that does not contain pointers.

    | PtrTy   -- ^ A machine word.  Same width as IntTy.  Untyped.
              -- This is a pointer to a struct value which may contain other pointers.
    | RegionTy -- ^ Region start and a refcount
    | ChunkTy  -- ^ Start and end pointers

-- TODO: Make Ptrs more type safe like this:
--    | StructPtrTy { fields :: [Ty] } -- ^ A pointer to a struct containing the given fields.

    | ProdTy [Ty]
    | SymDictTy Ty
      -- ^ We allow built-in dictionaries from symbols to a value type.
  deriving (Show, Ord, Eq, Generic, NFData, Out)

data Prim
    = AddP | SubP | MulP
    | DivP | ModP
    | EqP | LtP | GtP
    | SizeParam
    | DictInsertP Ty -- ^ takes k,v,dict
    | DictLookupP Ty -- ^ takes k,dict, errors if absent
    | DictEmptyP Ty
    | DictHasKeyP Ty

    | ReadPackedFile (Maybe FilePath) TyCon

    | NewBuffer Multiplicity
    -- ^ Allocate a new buffer, return a cursor.
    | ScopedBuffer Multiplicity
    -- ^ Returns a pointer to a buffer, with the invariant that data written
    -- to this region is no longer used after the enclosing function returns.
    -- I.e. this can be stack allocated data.

    | InitSizeOfBuffer Multiplicity
    -- ^ Returns the initial buffer size for a specific multiplicity

    | WriteTag
    -- ^ Write a static tag value, takes a cursor to target.
    | WriteInt
    -- ^ Write (leaf) data, takes cursor,int
    | ReadTag
    -- ^ Read one byte from the cursor and advance it.
    | ReadInt
    -- ^ Read an 8 byte Int from the cursor and advance.
    | ReadCursor
    -- ^ Read and return a cursor

    | WriteCursor

    | BoundsCheck

    | BumpRefCount

    | FreeBuffer

    | SizeOfPacked
    -- ^ Take start and end cursors and return size of data they represent
    -- This could be represented as (end - start) / (sizeof(Int))

    | SizeOfScalar
    -- ^ Takes in a variable, and returns an int, sizeof(var)

    | GetFirstWord -- ^ takes a PtrTy, returns IntTy containing the (first) word pointed to.

    | PrintInt    -- ^ Print an integer to stdout.
    | PrintString String -- ^ Print a constant string to stdout.
                         -- TODO: add string values to the language.

  deriving (Show, Ord, Eq, Generic, NFData, Out)

data FunDecl = FunDecl
  { funName  :: Var
  , funArgs  :: [(Var,Ty)]
  , funRetTy :: Ty
  , funBody  :: Tail
  , isPure   :: Bool
  } deriving (Show, Ord, Eq, Generic, NFData, Out)


-- | Extend the tail of a Tail.  Take the return values from a Tail
-- expression and do some more computation.
--
-- WARNING: presently this may invoke the given function more than
-- once and duplicate code.
withTail :: (Tail,Ty) -> ([Triv] -> Tail) -> SyM Tail
withTail (tl0,retty) fn =
  let go x = withTail (x,retty) fn in -- Warning: assumes same type.
  case tl0 of
    Goto{} -> return tl0
    RetValsT ls -> return $ fn ls
    (ErrT x)    -> return $ ErrT x
    (AssnValsT _ _) -> error $ "withTail: expected tail expression returning values, not: "++show tl0
    (LetCallT { binds, rator, rands, bod })    -> LetCallT binds rator rands    <$> go bod
    (LetPrimCallT { binds, prim, rands, bod }) -> LetPrimCallT binds prim rands <$> go bod
    (LetTrivT { bnd, bod })                    -> LetTrivT   bnd                <$> go bod
    (LetIfT { binds, ife, bod })               -> LetIfT     binds ife          <$> go bod
    (LetUnpackT { binds, ptr, bod })           -> LetUnpackT binds ptr          <$> go bod
    (LetAllocT { lhs, vals, bod })             -> LetAllocT  lhs   vals         <$> go bod
    (LetTimedT { isIter, binds, timed, bod })  -> LetTimedT isIter binds timed  <$> go bod

    -- We could DUPLICATE code in both branches or just let-bind the result instead:
    (IfT { tst, con, els }) -> IfT tst <$> go con <*> go els
        -- LetIfT _vr (tst,con,els)  $ fn [VarTriv _vr]

    -- Uh oh, here we don't have a LetSwitch form... duplicate code.
    (Switch lbl trv alts mlast) -> Switch lbl trv <$> mapAltsM go alts <*> sequence (fmap go mlast)
    (TailCall x1 x2)        -> do bnds <- genTmps retty
                                  return $ LetCallT bnds x1 x2 $ fn (map (VarTriv . fst) bnds)
 where
   mapAltsM f (TagAlts ls) = TagAlts <$> sequence [ (tg,) <$> f tl | (tg,tl) <- ls ]
   mapAltsM f (IntAlts ls) = IntAlts <$> sequence [ (tg,) <$> f tl | (tg,tl) <- ls ]

   genTmps (ProdTy ls) = flip zip ls <$> sequence (replicate (length ls) (gensym $ toVar "tctmp"))
   genTmps ty          = do t <- gensym (toVar "tctmp"); return [(t,ty)]


fromL3Ty :: L3.Ty3 -> Ty
fromL3Ty ty =
  case ty of
    L1.IntTy -> IntTy
    L1.SymTy -> SymTy
    L1.ProdTy tys -> ProdTy $ map fromL3Ty tys
    L1.SymDictTy t -> SymDictTy $ fromL3Ty t
    _ -> IntTy -- FIXME: review this
