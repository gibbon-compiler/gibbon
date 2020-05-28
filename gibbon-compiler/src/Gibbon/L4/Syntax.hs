{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Defines the target language for first-order L1 language with C code
-- generator for it.

module Gibbon.L4.Syntax
    ( Var, Tag, Tail(..), Triv(..), Ty(..), Prim(..), FunDecl(..)
    , Alts(..), Prog(..), MainExp(..), Label, SymTable
    , L3.Scalar(..), mkScalar, scalarToTy

    -- * Utility functions
    , withTail, fromL3Ty, voidTy, inlineTrivL4, typeOfTriv
    ) where

import           Control.DeepSeq
import           Control.Monad.State.Strict
import           Data.Int
import           Data.Maybe
import qualified Data.Map as M
import           Data.Word (Word8, Word16)
import           GHC.Generics (Generic)
import           Prelude hiding (init)
import           Text.PrettyPrint.GenericPretty (Out (..))

import           Gibbon.Language (Tag, TyCon)
import           Gibbon.Common
import qualified Gibbon.Language  as L
import qualified Gibbon.L2.Syntax as L2
import qualified Gibbon.L3.Syntax as L3


--------------------------------------------------------------------------------
-- * AST definition

data Prog = Prog
  { symbolTable :: SymTable
  , fundefs     :: [FunDecl]
  , mainExp     :: Maybe MainExp
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
    | FloatTriv Double
    | TagTriv Tag
    | SymTriv Word16    -- ^ An index into the symbol table.
    | ProdTriv [Triv]   -- ^ Tuples
    | ProjTriv Int Triv -- ^ Projections
  deriving (Show, Ord, Eq, Generic, NFData, Out)

typeOfTriv :: M.Map Var Ty -> Triv -> Ty
typeOfTriv env trv =
  case trv of
    VarTriv v   -> env M.! v
    IntTriv{}   -> IntTy
    FloatTriv{} -> FloatTy
    TagTriv{}   -> TagTyPacked
    SymTriv{}   -> SymTy
    ProdTriv ts -> ProdTy (map (typeOfTriv env) ts)
    ProjTriv i trv1 -> case typeOfTriv env trv1 of
                         ProdTy tys -> tys !! i
                         ty -> error $ "typeOfTriv: expected ProdTy, got: " ++ sdoc ty

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

instance Out Word8 where
  doc w = doc (fromIntegral w :: Integer)
  docPrec n w = docPrec n (fromIntegral w :: Integer)

instance Out Word16 where
  doc w = doc (fromIntegral w :: Integer)
  docPrec n w = docPrec n (fromIntegral w :: Integer)

type Label = Var

type SymTable = M.Map Word16 String

data Tail
    = RetValsT [Triv] -- ^ Only in tail position, for returning from a function.
    | AssnValsT { upd       :: [(Var,Ty,Triv)]
                , bod_maybe :: Maybe Tail
                }

    -- ^ INTERNAL ONLY: used for assigning instead of returning.

    | LetCallT { async :: Bool, -- ^ Whether this call should be executed asynchronously (cilk_spawn).
                 binds :: [(Var,Ty)],
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

    | LetAvailT { vars :: [Var]
                , bod :: Tail }

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

    -- Allocate an arena for non-packed data
    | LetArenaT { lhs :: Var
                , bod  :: Tail
                }
  deriving (Show, Ord, Eq, Generic, NFData, Out)

data Ty
    = IntTy        -- ^ 8 byte integers.
    | FloatTy      -- ^ 8 byte floating point numbers
    | BoolTy       -- ^ 1 byte integers.
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
    | SymDictTy Var Ty
      -- ^ We allow built-in dictionaries from symbols to a value type.
    | ArenaTy
    | VectorTy Ty
  deriving (Show, Ord, Eq, Generic, NFData, Out)

data Prim
    = AddP | SubP | MulP
    | DivP | ModP
    | EqP | LtP | GtP | LtEqP | GtEqP
    | ExpP
    | RandP
    | FRandP
    | FSqrtP
    | FloatToIntP
    | IntToFloatP
    | SizeParam
    | OrP | AndP
    | DictInsertP Ty -- ^ takes k,v,dict
    | DictLookupP Ty -- ^ takes k,dict, errors if absent
    | DictEmptyP Ty
    | DictHasKeyP Ty
    | VEmptyP Ty
    | VNthP Ty
    | VLengthP Ty
    | VUpdateP Ty
    | VSnocP Ty
    | VSortP Ty
    | InPlaceVSnocP Ty
    | InPlaceVSortP Ty
    | VSliceP Ty

    | ReadPackedFile (Maybe FilePath) TyCon
    | ReadArrayFile (Maybe FilePath) Ty

    | NewBuffer L2.Multiplicity
    -- ^ Allocate a new buffer, return a cursor.
    | ScopedBuffer L2.Multiplicity
    -- ^ Returns a pointer to a buffer, with the invariant that data written
    -- to this region is no longer used after the enclosing function returns.
    -- I.e. this can be stack allocated data.

    | InitSizeOfBuffer L2.Multiplicity
    -- ^ Returns the initial buffer size for a specific multiplicity

    | MMapFileSize Var

    | ReadTag
    -- ^ Read one byte from the cursor and advance it.

    | WriteTag
    -- ^ Write a static tag value, takes a cursor to target.

    | ReadCursor
    -- ^ Read and return a cursor
    | WriteCursor

    | ReadScalar L3.Scalar
    | WriteScalar L3.Scalar

    | ReadList
    | WriteList

    | BoundsCheck

    | BumpRefCount

    | BumpArenaRefCount

    | FreeBuffer

    | SizeOfPacked
    -- ^ Take start and end cursors and return size of data they represent
    -- This could be represented as (end - start) / (sizeof(Int))

    | SizeOfScalar
    -- ^ Takes in a variable, and returns an int, sizeof(var)

    | GetFirstWord -- ^ takes a PtrTy, returns IntTy containing the (first) word pointed to.

    | PrintInt    -- ^ Print an integer to stdout.
    | PrintFloat  -- ^ Print a floating point number
    | PrintSym    -- ^ Fetch a symbol from the symbol table, and print it.
    | PrintString String -- ^ Print a constant string to stdout.
                         -- TODO: add string values to the language.

    | ReadInt

    | ParSync          -- ^ cilk_sync
    | GetCilkWorkerNum -- ^ Runs  __cilkrts_get_worker_number()
    | IsBig

    | Gensym

    | FreeSymTable

  deriving (Show, Ord, Eq, Generic, NFData, Out)

data FunDecl = FunDecl
  { funName  :: Var
  , funArgs  :: [(Var,Ty)]
  , funRetTy :: Ty
  , funBody  :: Tail
  , isPure   :: Bool
  } deriving (Show, Ord, Eq, Generic, NFData, Out)

voidTy :: Ty
voidTy = ProdTy []

mkScalar :: Ty -> L3.Scalar
mkScalar IntTy  = L3.IntS
mkScalar SymTy  = L3.SymS
mkScalar BoolTy = L3.BoolS
mkScalar ty = error $ "mkScalar: Not a scalar type: " ++ sdoc ty

scalarToTy :: L3.Scalar -> Ty
scalarToTy L3.IntS  = IntTy
scalarToTy L3.SymS  = SymTy
scalarToTy L3.BoolS = BoolTy
scalarToTy L3.FloatS = FloatTy

-- | Extend the tail of a Tail.  Take the return values from a Tail
-- expression and do some more computation.
--
-- WARNING: presently this may invoke the given function more than
-- once and duplicate code.
withTail :: MonadState Int m => (Tail,Ty) -> ([Triv] -> Tail) -> m Tail
withTail (tl0,retty) fn =
  let go x = withTail (x,retty) fn in -- Warning: assumes same type.
  case tl0 of
    Goto{} -> return tl0
    RetValsT ls -> return $ fn ls
    (ErrT x)    -> return $ ErrT x
    (AssnValsT _ _) -> error $ "withTail: expected tail expression returning values, not: "++show tl0
    (LetCallT { async, binds, rator, rands, bod }) -> LetCallT async binds rator rands <$> go bod
    (LetPrimCallT { binds, prim, rands, bod }) -> LetPrimCallT binds prim rands <$> go bod
    (LetTrivT { bnd, bod })                    -> LetTrivT   bnd                <$> go bod
    (LetIfT { binds, ife, bod })               -> LetIfT     binds ife          <$> go bod
    (LetUnpackT { binds, ptr, bod })           -> LetUnpackT binds ptr          <$> go bod
    (LetAllocT { lhs, vals, bod })             -> LetAllocT  lhs   vals         <$> go bod
    (LetTimedT { isIter, binds, timed, bod })  -> LetTimedT isIter binds timed  <$> go bod
    (LetArenaT { lhs, bod })                   -> LetArenaT lhs                 <$> go bod
    (LetAvailT { vars, bod })                  -> LetAvailT vars                <$> go bod

    -- We could DUPLICATE code in both branches or just let-bind the result instead:
    (IfT { tst, con, els }) -> IfT tst <$> go con <*> go els
        -- LetIfT _vr (tst,con,els)  $ fn [VarTriv _vr]

    -- Uh oh, here we don't have a LetSwitch form... duplicate code.
    (Switch lbl trv alts mlast) -> Switch lbl trv <$> mapAltsM go alts <*> sequence (fmap go mlast)
    (TailCall x1 x2)        -> do bnds <- genTmps retty
                                  return $ LetCallT False bnds x1 x2 $ fn (map (VarTriv . fst) bnds)
 where
   mapAltsM f (TagAlts ls) = TagAlts <$> sequence [ (tg,) <$> f tl | (tg,tl) <- ls ]
   mapAltsM f (IntAlts ls) = IntAlts <$> sequence [ (tg,) <$> f tl | (tg,tl) <- ls ]

   genTmps (ProdTy ls) = flip zip ls <$> sequence (replicate (length ls) (gensym $ toVar "tctmp"))
   genTmps ty          = do t <- gensym (toVar "tctmp"); return [(t,ty)]

fromL3Ty :: L3.Ty3 -> Ty
fromL3Ty ty =
  case ty of
    L.IntTy   -> IntTy
    L.FloatTy -> FloatTy
    L.SymTy   -> SymTy
    L.BoolTy  -> BoolTy
    L.ProdTy tys -> ProdTy $ map fromL3Ty tys
    L.SymDictTy (Just var) t -> SymDictTy var $ fromL3Ty t
    L.ArenaTy    -> ArenaTy
    L.PtrTy      -> PtrTy
    L.CursorTy   -> CursorTy
    -- L.PackedTy{} -> error "fromL3Ty: Cannot convert PackedTy"
    L.VectorTy el_ty  -> VectorTy (fromL3Ty el_ty)
    _ -> IntTy -- [2019.06.10]: CSK, Why do we need this?


inlineTrivL4 :: Prog -> Prog
inlineTrivL4 (Prog sym_tbl fundefs mb_main) =
  Prog sym_tbl (map inline_fun fundefs) (inline_main <$> mb_main)

  where
    inline_fun fn@FunDecl{funBody} = fn { funBody = inline_tail M.empty funBody }

    inline_main (PrintExp bod) = PrintExp (inline_tail M.empty bod)

    inline_tail :: M.Map Var Triv -> Tail -> Tail
    inline_tail env tl =
      case tl of
        RetValsT trvs            -> RetValsT (map (inline env) trvs)
        AssnValsT assns mb_bod   -> AssnValsT
                                      (map (\(v,ty,trv) -> (v,ty,inline env trv)) assns)
                                      (go <$> mb_bod)
        LetCallT{rands,bod}      -> tl { rands = map (inline env) rands
                                       , bod   = go bod }
        LetPrimCallT{rands,bod}  -> tl { rands = map (inline env) rands
                                       , bod   = go bod }
        LetTrivT (v,_ty,trv) bod ->
          case trv of
            VarTriv w -> case M.lookup w env of
                           Nothing -> inline_tail (M.insert v trv env) bod
                           Just pr -> inline_tail (M.insert v pr env) bod
            _         -> inline_tail (M.insert v trv env) bod
        LetIfT{ife,bod} -> tl { ife = (\(a,b,c) -> (inline env a,
                                                    go b,
                                                    go c))
                                      ife
                              , bod = go bod }
        LetUnpackT{bod} -> tl { bod = go bod }
        LetAllocT{vals,bod} -> tl { vals = map (\(a,b) -> (a, inline env b)) vals
                                  , bod  = go bod }
        LetAvailT{bod}   -> tl { bod = go bod }
        IfT{tst,con,els} -> IfT (inline env tst) (go con) (go els)
        ErrT{} -> tl
        LetTimedT{timed,bod} -> tl { timed = go timed
                                   , bod = go bod }
        Switch lbl trv alts mb_tail ->
          let alts' = case alts of
                        TagAlts as -> TagAlts $ map (\(a,b) -> (a, go b)) as
                        IntAlts as -> IntAlts $ map (\(a,b) -> (a, go b)) as
          in Switch lbl (inline env trv) alts' (go <$> mb_tail)
        TailCall v trvs -> TailCall v (map (inline env) trvs)
        LetArenaT{bod}  -> tl { bod = go bod }
        Goto{}          -> tl
      where
        go = inline_tail env

    inline env trv =
      case trv of
        VarTriv v -> case M.lookup v env of
                       Just trv' -> trv'
                       _ -> trv
        _         -> trv
