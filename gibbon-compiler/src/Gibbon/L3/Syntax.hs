{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | An intermediate language which makes cursors explicit

module Gibbon.L3.Syntax
  (
    -- * Extended language
    E3Ext(..), Prog3, DDef3, DDefs3, FunDef3, FunDefs3 , Exp3, Ty3
  , Scalar(..), mkScalar, scalarToTy

    -- * Functions
  , eraseLocMarkers, mapMExprs, cursorizeTy, toL3Prim, updateAvailVars
  , getCursorizeTyFromLocVar
  , getCursorizeTyFromLocVar'
  , getCursorizeTyFromLocVar''
  , getCursorizeTyFromLocVar'''
  , getCursorizeTyFromRegVar
  , getCursorizeTyFromRegVar'
  , getCursorizeTyFromRegVar''
  , getCursorizeTyFromRegVar'''
  , getIndexPositionOfSoALocVar
  , getIndexPositionOfSoARegVar
  , linearizeLocVar
  , linearizeRegVar
  , isMutModality
  , isMutModality'
  , isInputModality
  , checkIfLocIsPointedToByOutputMutLoc
  , checkIfVarIsMutable
  , findMutableLocationInSameRegion
  , findMutableLocationPointingToVar
  , findMutableLocationPointingToEndVar
  , findAValidRegion
  , fst4
  , snd4
  , thd4
  , fth4
  , MutableLocPtsToEnv
  , MutableLocOldValueEnv
  , updateMutableLocPtsToEnv
  , updateMutableLocOldValueEnv
  , module Gibbon.Language
  )
where

import Control.DeepSeq
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as Mb
import Text.PrettyPrint.GenericPretty

import           Gibbon.Common
-- import qualified Gibbon.L2.Syntax               as L2
import           Gibbon.Language                hiding (mapMExprs)
import qualified Gibbon.NewL2.Syntax as L2
import Gibbon.L2.Syntax (EndRegionModality)

-------------------------------------------------------------------------------- 

type Prog3 = Prog Var Exp3

type DDef3  = DDef Ty3
type DDefs3 = DDefs Ty3

type FunDefs3 = FunDefs Var Exp3

type FunDef3 = FunDef Var Exp3

-- GHC uses the instance defined for L1.Ty1
-- instance FunctionTy Ty3 where

type Exp3 = PreExp E3Ext () Ty3

type Ty3 = UrTy ()

-- Take the current snapshot of a Mutable location
-- For a Mutable Location, we store its current value in the env. (variable name, location value name)
-- We also store the mutable end region in scope if it exists for a mutable location
-- We also store any aliases that may exist for the loc we are keeping track of
type MutableLocPtsToEnv = M.Map LocVar [(Var, Maybe LocVar, Maybe RegVar, S.Set Var)]

-- Store the old value of the mutable location.
-- Also store the mutable loc of the end of region
-- We also store any aliases that may exist for the loc we are keeping track of
type MutableLocOldValueEnv = M.Map LocVar (Var, Maybe LocVar, Maybe RegVar, S.Set Var)

--------------------------------------------------------------------------------

-- | The extension that turns L1 into L3.
data E3Ext loc dec =
    ReadScalar  Scalar Var                        -- ^ One cursor in, (int, cursor') out
  | WriteScalar Scalar Var (PreExp E3Ext loc dec) -- ^ Write int at cursor, and return a cursor
  | ReadTag Var                            -- ^ One cursor in, (tag,cursor) out
  | WriteTag DataCon Var                   -- ^ Write Tag at Cursor, and return a cursor
  | WriteTagPacked Var (PreExp E3Ext loc dec)
    -- ^ Write a runtime tag byte at Cursor, and return a cursor.
  | TagCursor Var Var                      -- ^ Create a tagged cursor
  | WriteCursorIndirection Var Var Var     -- ^ Write an indirection node at the
                                           -- first cursor pointing to the second,
                                           -- using the third as the pointed-to
                                           -- chunk footer/end cursor.
  | WriteTaggedCursor Var (PreExp E3Ext loc dec) -- ^ Write a tagged cursor
  | MemCpy Var Var dec                           -- ^ Do a mem copy from right address into left address of type dec
  | ReadTaggedCursor Var                   -- ^ Reads and returns a tagged cursor at Var
  | ReadCursor Var                         -- ^ Reads and returns the cursor at Var
  | GrowRegion Var Var                     -- ^ Grow an output region given mutable cursor and mutable end refs
  | WriteCursorMutable Var (PreExp E3Ext loc dec) -- ^ Write some value to a Mutable cursor
  | ReadList Var dec                       -- ^ Read a pointer to a linked list
  | WriteList Var (PreExp E3Ext loc dec) dec       -- ^ Write a pointer to a linked list
  | ReadVector Var dec                             -- ^ Read a pointer to a vector
  | WriteVector Var (PreExp E3Ext loc dec) dec     -- ^ Write a pointer to a vector
  | MakeCursorArray Int [Var] -- ^ Make a Cursor Array from a list of Cursors. Returns a new variable for Cursor Array.
  | IndexCursorArray Var Int                       -- ^ Index into a Cursor Array 
  | AddCursor Var (PreExp E3Ext loc dec)           -- ^ Add a constant offset to a cursor variable
  | BumpCursorMutable Var (PreExp E3Ext loc dec)   -- ^ Bump a mutable cursor, that is, a reference to a cursor by a constant amount.
  | AddrOfCursor (PreExp E3Ext loc dec)            -- ^ Take the address of a Cursor.
  | DerefMutCursor Var                             -- ^ Explicitly de-reference a mutable cursor
  | CastPtr Var dec                                -- ^ Cast a pointer to the specified type
  | SubPtr Var Var                                 -- ^ Pointer subtraction
  | NewBuffer L2.Multiplicity EndRegionModality    -- ^ Create a new buffer, and return a cursor
  | ScopedBuffer L2.Multiplicity      -- ^ Create a temporary scoped buffer, and return a cursor
  | NewParBuffer L2.Multiplicity         -- ^ Create a new buffer for parallel allocations, and return a cursor
  | ScopedParBuffer L2.Multiplicity      -- ^ Create a temporary scoped buffer for parallel allocations, and return a cursor
  | EndOfBuffer L2.Multiplicity EndRegionModality
  | MMapFileSize Var
  | SizeOfPacked Var Var           -- ^ Takes in start and end cursors, and returns an Int
                                   --   we'll probably represent (sizeof x) as (end_x - start_x) / INT
  | SizeOfScalar Var               -- ^ sizeof(var)
  | BoundsCheck Int Var Var (Maybe (Var, Var)) L2.Modality  -- ^ Bytes required, region, write cursor
                                                            -- if mutable vars exist we keep them stored
  -- | BoundsCheckMut Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec) -- Bounds check for OutputMutable locations and their end regions.
  | BoundsCheckVector [(Int, Var, Var, (Var, Var))] -- ^ Bytes required, region, write cursor but for a vector of cursors and regions
  | IndirectionBarrier TyCon (Var,Var,Var,Var)
    -- ^ Do one of the following:
    -- (1) If it's a old-to-young indirection, record it in the remembered set.
    -- (2) Otherwise, bump the refcount and update the outset.
  | BumpArenaRefCount Var Var -- ^ Given an arena and end-of-region ptr, add a
                                    --   reference from the arena to the region
  | NullCursor                      -- ^ Constant null cursor value (hack?).
                                    --   Used for dict lookup, which returns a packed value but
                                    --   no end witness.
  | InitCursor dec                  -- ^ Initialize a cursor without a rhs value.
  | RetE [(PreExp E3Ext loc dec)]   -- ^ Analogous to L2's RetE.
  | GetCilkWorkerNum                -- ^ Translates to  __cilkrts_get_worker_number().
  | LetAvail [Var] (PreExp E3Ext loc dec) -- ^ These variables are available to use before the join point
  | AllocateTagHere Var TyCon  -- ^ Analogous to L2's extension.
  | AllocateScalarsHere Var    -- ^ Analogous to L2's extension.
  | StartTagAllocation Var     -- ^ Marks the beginning of tag allocation.
  | EndTagAllocation Var       -- ^ Marks the end of tag allocation.
  | StartScalarsAllocation Var -- ^ Marks the beginning of scalar allocation.
  | EndScalarsAllocation Var   -- ^ Marks the end of scalar allocation.
  | ScalarCountBump DataCon [Var]
    -- ^ Constructor-level scalar-buffer count instrumentation.  The DataCon is
    -- the semantic event; the Vars are the affected SoA scalar-buffer cursors.
  | ReadScalarCount Var
    -- ^ Read the scalar-count value stored in a footer/end cursor.
  | ReadScalarCountFirstFooter Var
    -- ^ Recover the footer holding the first chunk's count.
  | ReadScalarCountNextFooter Var
    -- ^ Recover the footer holding the next chunk's count.
  | ForE Var (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ A statement-like counted loop. The body should evaluate to unit.
  | WhileCursor Var (PreExp E3Ext loc dec)
    -- ^ A statement-like loop that repeats while the mutable cursor ref is
    -- non-null. The body should evaluate to unit.
  | SSPush SSModality Var Var TyCon
  | SSPop SSModality Var Var
  | Assert (PreExp E3Ext loc dec) -- ^ Translates to assert statements in C.
    -- ^ Analogous to L2's extensions.
  deriving (Show, Ord, Eq, Read, Generic, NFData)

isMutModality :: L2.Modality -> Bool 
isMutModality modal = case modal of 
                          L2.InputMutable -> True
                          L2.OutputMutable -> True 
                          _ -> False


isInputModality :: Maybe L2.Modality -> Bool
isInputModality modal = case modal of 
                              Just L2.Input -> True
                              _ -> False 

isMutModality' :: Maybe L2.Modality -> Bool 
isMutModality' modal = case modal of 
                          Just L2.InputMutable -> True
                          Just L2.OutputMutable -> True 
                          _ -> False

fst4 :: (a, b, c, d) -> a
fst4 (a, _, _, _) = a

snd4 :: (a, b, c, d) -> b
snd4 (_, b, _, _) = b

thd4 :: (a, b, c, d) -> c
thd4 (_, _, c, _) = c

fth4 :: (a, b, c, d) -> d
fth4 (_, _, _, d) = d


instance FreeVars (E3Ext l d) where
  gFreeVars  e =
    case e of
      ReadScalar _  v     -> S.singleton v
      WriteScalar _ v ex  -> S.insert v (gFreeVars ex)
      ReadTag v      -> S.singleton v
      WriteTag _ v   -> S.singleton v
      WriteTagPacked v ex -> S.insert v (gFreeVars ex)
      TagCursor a b      -> S.fromList [a,b]
      WriteCursorIndirection a b c -> S.fromList [a,b,c]
      ReadTaggedCursor v -> S.singleton v
      WriteTaggedCursor v ex -> S.insert v (gFreeVars ex)
      MemCpy a b _ -> S.fromList [a, b]
      ReadCursor v       -> S.singleton v
      GrowRegion v w     -> S.fromList [v, w]
      WriteCursorMutable c ex   -> S.insert c (gFreeVars ex)
      ReadList v _       -> S.singleton v
      WriteList c ex  _  -> S.insert c (gFreeVars ex)
      AddCursor v ex -> S.insert v (gFreeVars ex)
      BumpCursorMutable v ex -> S.insert v (gFreeVars ex)
      SubPtr v w     -> S.fromList [v, w]
      NewBuffer{}    -> S.empty
      NewParBuffer{}     -> S.empty
      ScopedBuffer{}     -> S.empty
      ScopedParBuffer{}  -> S.empty
      EndOfBuffer{}      -> S.empty
      MMapFileSize v     -> S.singleton v
      SizeOfPacked c1 c2 -> S.fromList [c1, c2]
      SizeOfScalar v     -> S.singleton v
      BoundsCheck{}      -> S.empty
      IndirectionBarrier _tycon (l1,r1,l2,r2) -> S.fromList [l1,r1,l2,r2]
      NullCursor         -> S.empty
      InitCursor{} -> S.empty
      BumpArenaRefCount v w -> S.fromList [v, w]
      RetE ls -> S.unions (L.map gFreeVars ls)
      GetCilkWorkerNum   -> S.empty
      LetAvail ls b      -> (S.fromList ls) `S.union` gFreeVars b
      ReadVector{}  -> error "gFreeVars: ReadVector"
      WriteVector{} -> error "gFreeVars: WriteVector"
      AllocateTagHere v _ -> S.singleton v
      AllocateScalarsHere v -> S.singleton v
      StartTagAllocation v -> S.singleton v
      EndTagAllocation v -> S.singleton v
      StartScalarsAllocation v -> S.singleton v
      EndScalarsAllocation v -> S.singleton v
      ScalarCountBump _ footers -> S.fromList footers
      ReadScalarCount v -> S.singleton v
      ReadScalarCountFirstFooter v -> S.singleton v
      ReadScalarCountNextFooter v -> S.singleton v
      ForE idx bound bod ->
        gFreeVars bound `S.union` S.delete idx (gFreeVars bod)
      WhileCursor ref bod ->
        S.insert ref (gFreeVars bod)
      SSPush _ a b _ -> S.fromList [a,b]
      SSPop _ a b -> S.fromList [a,b]
      Assert a -> gFreeVars a
      MakeCursorArray {} -> error "gFreeVars: MakeCursorArray not handled"
      IndexCursorArray {} -> error "gFreeVars: IndexCursorArray not handled"
      CastPtr {} -> error "gFreeVars: CastPtr not handled"
      BoundsCheckVector {} -> error "gFreeVars: BoundsCheckVector not handled"
      AddrOfCursor{} -> error "gFreeVars: AddrOfCursor not handled"
      DerefMutCursor{} -> error "gFreeVars: DerefMutCursor not handled"


instance (Out l, Out d, Show l, Show d) => Expression (E3Ext l d) where
  type LocOf (E3Ext l d) = l
  type TyOf  (E3Ext l d) = UrTy l
  isTrivial _ = False

instance (Out l, Show l, Typeable (PreExp E3Ext l (UrTy l))) => Typeable (E3Ext l (UrTy l)) where
    gRecoverType _ddfs _env2 NullCursor = CursorTy
    gRecoverType ddfs env2 (RetE ls)    = ProdTy $ L.map (gRecoverType ddfs env2) ls
    gRecoverType _ _ (MakeCursorArray {}) = error "gRecoverType: MakeCursorArray not handled"
    gRecoverType _ _ (IndexCursorArray {}) = error "gRecoverType: IndexCursorArray not handled"
    gRecoverType _ _ (CastPtr {}) = error "gRecoverType: CastPtr not handled"
    gRecoverType _ _ (BoundsCheckVector {}) = error "gRecoverType: BoundsCheckVector not handled"
    gRecoverType _ _ (ReadScalarCount {}) = IntTy
    gRecoverType _ _ (ReadScalarCountFirstFooter {}) = CursorTy
    gRecoverType _ _ (ReadScalarCountNextFooter {}) = CursorTy
    gRecoverType _ _ (ForE {}) = ProdTy []
    gRecoverType _ _ (WhileCursor {}) = ProdTy []
    gRecoverType _ _ (WriteTagPacked {}) = CursorTy
    gRecoverType _ _ (GrowRegion {}) = ProdTy []
    gRecoverType _ _ _ = error "L3.gRecoverType"


    gRecoverTypeLoc _ddfs _env2 NullCursor = CursorTy
    gRecoverTypeLoc ddfs env2 (RetE ls)    = ProdTy $ L.map (gRecoverTypeLoc ddfs env2) ls
    gRecoverTypeLoc _ _ (MakeCursorArray {}) = error "gRecoverType: MakeCursorArray not handled"
    gRecoverTypeLoc _ _ (IndexCursorArray {}) = error "gRecoverType: IndexCursorArray not handled"
    gRecoverTypeLoc _ _ (CastPtr {}) = error "gRecoverType: CastPtr not handled"
    gRecoverTypeLoc _ _ (BoundsCheckVector {}) = error "gRecoverType: BoundsCheckVector not handled"
    gRecoverTypeLoc _ _ (ReadScalarCount {}) = IntTy
    gRecoverTypeLoc _ _ (ReadScalarCountFirstFooter {}) = CursorTy
    gRecoverTypeLoc _ _ (ReadScalarCountNextFooter {}) = CursorTy
    gRecoverTypeLoc _ _ (ForE {}) = ProdTy []
    gRecoverTypeLoc _ _ (WhileCursor {}) = ProdTy []
    gRecoverTypeLoc _ _ (WriteTagPacked {}) = CursorTy
    gRecoverTypeLoc _ _ (GrowRegion {}) = ProdTy []
    gRecoverTypeLoc _ _ _ = error "L3.gRecoverTypeLoc"

instance (Show l, Out l) => Flattenable (E3Ext l (UrTy l)) where
    gFlattenGatherBinds _ddfs _env ex = return ([], ex)
    gFlattenExp _ddfs _env ex = return ex

instance HasSimplifiableExt E3Ext l d => SimplifiableExt (PreExp E3Ext l d) (E3Ext l d) where
  gInlineTrivExt _ _ = error $ "InlineTriv is not a safe operation to perform on L3." ++
                               " A lot of L3 extensions can only use values" ++
                               " via variable references. So those variables" ++
                               " should *not* be inlined." ++
                               " Running copy-propogation should be OK."


instance HasSubstitutableExt E3Ext l d => SubstitutableExt (PreExp E3Ext l d) (E3Ext l d) where
  gSubstExt old new ext =
    case ext of
      WriteScalar s v bod  -> WriteScalar s v (gSubst old new bod)
      WriteTagPacked v bod -> WriteTagPacked v (gSubst old new bod)
      GrowRegion v w       -> GrowRegion v w
      WriteCursorMutable v bod    -> WriteCursorMutable v (gSubst old new bod)
      AddCursor v bod      -> AddCursor v (gSubst old new bod)
      SubPtr v w           -> SubPtr v w
      LetAvail ls bod      -> LetAvail ls (gSubst old new bod)
      ForE idx bound bod
        | idx == old -> ForE idx (gSubst old new bound) bod
        | otherwise  -> ForE idx (gSubst old new bound) (gSubst old new bod)
      WhileCursor ref bod  -> WhileCursor ref (gSubst old new bod)
      MakeCursorArray{}    -> ext
      IndexCursorArray{}   -> ext
      CastPtr{}            -> ext
      BoundsCheckVector{}  -> ext
      _ -> ext

  gSubstEExt old new ext =
    case ext of
      WriteScalar s v bod    -> WriteScalar s v (gSubstE old new bod)
      WriteTagPacked v bod   -> WriteTagPacked v (gSubstE old new bod)
      GrowRegion v w         -> GrowRegion v w
      WriteCursorMutable v bod -> WriteCursorMutable v (gSubstE old new bod)
      AddCursor v bod   -> AddCursor v (gSubstE old new bod)
      SubPtr v w        -> SubPtr v w
      LetAvail ls b     -> LetAvail ls (gSubstE old new b)
      ForE idx bound bod -> ForE idx (gSubstE old new bound) (gSubstE old new bod)
      WhileCursor ref bod -> WhileCursor ref (gSubstE old new bod)
      MakeCursorArray{}    -> ext
      IndexCursorArray{}   -> ext
      CastPtr{}            -> ext
      BoundsCheckVector{}  -> ext
      _ -> ext

instance HasRenamable E3Ext l d => Renamable (E3Ext l d) where
  gRename env ext =
    case ext of
      ReadScalar s v     -> ReadScalar s (go v)
      WriteScalar s v bod-> WriteScalar s (go v) (go bod)
      TagCursor a b      -> TagCursor (go a) (go b)
      WriteCursorIndirection a b c -> WriteCursorIndirection (go a) (go b) (go c)
      ReadTaggedCursor v -> ReadTaggedCursor (go v)
      WriteTaggedCursor v bod -> WriteTaggedCursor (go v) (go bod)
      MemCpy a b ty -> MemCpy (go a) (go b) ty 
      ReadCursor v       -> ReadCursor (go v)
      GrowRegion v w     -> GrowRegion (go v) (go w)
      WriteCursorMutable v bod  -> WriteCursorMutable (go v) (go bod)
      ReadList v el_ty      -> ReadList (go v) el_ty
      WriteList v bod el_ty -> WriteList (go v) (go bod) el_ty
      ReadVector v el_ty      -> ReadVector (go v) el_ty
      WriteVector v bod el_ty -> WriteVector (go v) (go bod) el_ty
      ReadTag v          -> ReadTag (go v)
      WriteTag dcon v    -> WriteTag dcon (go v)
      WriteTagPacked v bod -> WriteTagPacked (go v) (go bod)
      AddCursor v bod    -> AddCursor (go v) (go bod)
      BumpCursorMutable v bod -> BumpCursorMutable (go v) (go bod)
      SubPtr v w         -> SubPtr (go v) (go w)
      NewBuffer{}        -> ext
      ScopedBuffer{}     -> ext
      NewParBuffer{}     -> ext
      ScopedParBuffer{}  -> ext
      EndOfBuffer{}      -> ext
      MMapFileSize v     -> MMapFileSize (go v)
      SizeOfPacked a b   -> SizeOfPacked (go a) (go b)
      SizeOfScalar v     -> SizeOfScalar (go v)
      BoundsCheck i a b mb bmod  -> BoundsCheck i (go a) (go b) mb bmod
      IndirectionBarrier tycon (a,b,c,d) ->
        IndirectionBarrier tycon (go a, go b, go c, go d)
      BumpArenaRefCount v w -> BumpArenaRefCount (go v) (go w)
      NullCursor         -> ext
      InitCursor{} -> ext
      RetE ls            -> RetE (L.map go ls)
      GetCilkWorkerNum   -> GetCilkWorkerNum
      LetAvail ls b      -> LetAvail (L.map go ls) (go b)
      AllocateTagHere v tycon -> AllocateTagHere (go v) tycon
      AllocateScalarsHere v  -> AllocateScalarsHere (go v)
      StartTagAllocation v -> StartTagAllocation (go v)
      EndTagAllocation v -> EndTagAllocation (go v)
      StartScalarsAllocation v -> StartScalarsAllocation (go v)
      EndScalarsAllocation v -> EndScalarsAllocation (go v)
      ScalarCountBump dcon footers -> ScalarCountBump dcon (L.map go footers)
      ReadScalarCount v -> ReadScalarCount (go v)
      ReadScalarCountFirstFooter v -> ReadScalarCountFirstFooter (go v)
      ReadScalarCountNextFooter v -> ReadScalarCountNextFooter (go v)
      ForE idx bound bod ->
        let env' = M.delete idx env
        in ForE idx (go bound) (gRename env' bod)
      WhileCursor ref bod -> WhileCursor (go ref) (go bod)
      SSPush a b c d -> SSPush a (go b) (go c) d
      SSPop a b c -> SSPop a (go b) (go c)
      Assert e -> Assert (go e)
      MakeCursorArray{} -> error "gRename: MakeCursorArray not handled"
      IndexCursorArray{} -> error "gRename: IndexCursorArray not handled"
      CastPtr{} -> error "gRename: CastPtr not handled"
      BoundsCheckVector{} -> error "gRename: BoundsCheckVector not handled"
      AddrOfCursor{} -> error "gRename: AddrOfCursor not handled"
      DerefMutCursor{} -> error "gRename: DerefMutCursor not handled"
    where
      go :: forall a. Renamable a => a -> a
      go = gRename env

data Scalar = IntS | CharS | FloatS | SymS | BoolS
  deriving (Show, Ord, Eq, Read, Generic, NFData, Out)

mkScalar :: Out a => UrTy a -> Scalar
mkScalar IntTy  = IntS
mkScalar CharTy = CharS
mkScalar FloatTy= FloatS
mkScalar SymTy  = SymS
mkScalar BoolTy = BoolS
mkScalar ty = error $ "mkScalar: Not a scalar type: " ++ sdoc ty

scalarToTy :: Scalar -> UrTy a
scalarToTy IntS  = IntTy
scalarToTy CharS = CharTy
scalarToTy FloatS= FloatTy
scalarToTy SymS  = SymTy
scalarToTy BoolS = BoolTy


-- Takes in a Loc and checks if a mutable locations points to that loc
checkIfLocIsPointedToByOutputMutLoc :: LocVar -> MutableLocPtsToEnv -> Maybe LocVar
checkIfLocIsPointedToByOutputMutLoc loc mlocenv = L.foldr (\(k, lst) mbl ->
                                                            foldr (\(_v, mlv, _r, _aliases) mbl' -> case mlv of 
                                                                                                      Nothing -> mbl'
                                                                                                      Just lv -> if lv == loc
                                                                                                               then Just k
                                                                                                               else mbl'
                                                                  ) mbl lst
                                                          ) Nothing (M.toList mlocenv)

-- Check if a Variable if a mutable variable or not
checkIfVarIsMutable :: Var -> MutableLocPtsToEnv -> Bool 
checkIfVarIsMutable var mlocenv = L.foldr (\(_k, lst) b -> 
                                                  foldr (\(v, _mlv, _r, aliases) b'  -> 
                                                                              if S.null aliases 
                                                                              then (v == var) || b'
                                                                              else let 
                                                                                    isAlias = S.member var aliases 
                                                                                    direct = v == var
                                                                                   in isAlias || direct || b'
                                                        ) b lst
                                          ) False (M.toList mlocenv)

findMutableLocationPointingToVar :: Var -> MutableLocPtsToEnv -> Maybe LocVar
findMutableLocationPointingToVar v mlocenv = L.foldr (\(k, lst) acc -> 
                                                            foldr (\(vv, _mlv, _rr, aliases) acc' ->
                                                                                             if v == vv || S.member v aliases 
                                                                                             then Just k
                                                                                             else acc'
                                                                  ) acc lst 
                                                    ) Nothing (M.toList mlocenv)

-- Vidush: Assumption, only the head of the list points to the current value of the mutable location!
-- findMutableLocationPointingToVar :: Var -> MutableLocPtsToEnv -> Maybe LocVar
-- findMutableLocationPointingToVar v mlocenv = L.foldr (\(k, lst) acc -> 
--                                                                 case lst of 
--                                                                      (vv, _mlv, _rr, aliases):_xs -> if v == vv || S.member v aliases 
--                                                                                                     then Just k
--                                                                                                     else acc
--                                                                      [] -> acc
--                                                     ) Nothing (M.toList mlocenv)

findMutableLocationPointingToEndVar :: Var -> MutableLocPtsToEnv -> Maybe LocVar
findMutableLocationPointingToEndVar v mlocenv = L.foldr (\(k, lst) acc ->
                                                              foldr (\(vv, _mlv, _rr, aliases) acc' -> 
                                                                                               if (v == (toEndV vv)) || S.member v aliases 
                                                                                               then Just k
                                                                                               else acc'
                                                                    ) acc lst
                                                    ) Nothing (M.toList mlocenv)

-- findMutableLocationPointingToEndVar :: Var -> MutableLocPtsToEnv -> Maybe LocVar
-- findMutableLocationPointingToEndVar v mlocenv = L.foldr (\(k, lst) acc -> case lst of 
--                                                                                 (vv, _mlv, _rr, aliases):_xs -> if (v == (toEndV vv)) || S.member v aliases 
--                                                                                                                 then Just k
--                                                                                                                 else acc
--                                                                                 [] -> acc
--                                                     ) Nothing (M.toList mlocenv)


findMutableLocationInSameRegion :: RegVar -> MutableLocPtsToEnv -> Maybe (Var, LocVar)
findMutableLocationInSameRegion r mlocenv = L.foldr (\(k, lst) acc ->
                                                            foldr (\(v, _mlv, rr, _aliases) acc' -> case rr of 
                                                                                                        Nothing -> acc' 
                                                                                                        Just rr' -> if r == rr' 
                                                                                                                    then Just (v, k)
                                                                                                                    else acc'
                                                                  ) acc lst
                                                    ) Nothing (M.toList mlocenv)

-- Vidush: Implement two functions that insert and update the key in the environment for both the pts to env and for the old env.
-- TODO: Implement some simple logic to tell if the old variable can be an alias. Tough problem. 
-- For starters, if its a concrete update like AddCursor then let us say no, they cannot alias 
-- For Make SoA locations, these might alias so we can store them as aliases in the updated entry.
-- (Var, Maybe LocVar, Maybe RegVar, S.Set Var)


findAValidRegion :: [(Var, Maybe LocVar, Maybe RegVar, S.Set Var)] -> Maybe RegVar
findAValidRegion lst = case lst of 
                            [] -> Nothing
                            -- Vidush: Maybe its good to assert that all the regions are the same.
                            (_v, _lc, reg, _aliases):xs -> case reg of
                                                              Nothing -> findAValidRegion xs
                                                              Just{} -> reg


findAValidRegion' :: [(Var, Maybe LocVar, Maybe RegVar, S.Set Var)] -> Maybe RegVar -> Maybe RegVar
findAValidRegion' lst r = case lst of 
                            [] -> r
                            -- Vidush: Maybe its good to assert that all the regions are the same.
                            (_v, _lc, reg, _aliases):xs -> case reg of
                                                              Nothing -> let found = findAValidRegion xs
                                                                          in case found of 
                                                                                    Nothing -> r 
                                                                                    Just{} -> found  
                                                              Just{} -> reg 

updateMutableLocPtsToEnv :: LocVar -> MutableLocPtsToEnv -> (Var, Maybe LocVar, Maybe RegVar, S.Set Var) -> Bool -> MutableLocPtsToEnv
updateMutableLocPtsToEnv key env (v, lc, reg, aliases) isFuture = case M.lookup key env of 
                                                                    -- If the key does not exists we just make an entry for it
                                                                    -- in the env.
                                                                    Nothing -> M.insert key [(v, lc, reg, aliases)] env
                                                                    Just lst@(_x:_xs) ->  let reg' = findAValidRegion' lst reg
                                                                                           in if isFuture
                                                                                              then M.insert key ([(v, lc, reg', aliases)] ++ lst) env
                                                                                              -- ++ xs
                                                                                              -- Vidush: This might need to be more principled
                                                                                              -- We might need to have a flag in the type
                                                                                              -- saying that the value can be a future value
                                                                                              -- If it is a future value, then we may need to
                                                                                              -- set that bit and store it as a future value 
                                                                                              else M.insert key ([(v, lc, reg', aliases)]) env
                                                                    Just [] -> M.insert key ([(v, lc, reg, aliases)]) env
                                                                      
                                                                      
                                                                      
                                                                      -- let reg' = (findAValidRegion lst) 
                                                                      --             in case reg' of 
                                                                      --                         Nothing -> -- M.insert key (lst ++ [(v, lc, reg, aliases)]) env
                                                                      --                                     if mayalias
                                                                      --                                     then M.insert key (lst ++ [(v, lc, reg, aliases)]) env
                                                                      --                                     else M.insert key ([(v, lc, reg, aliases)]) env
                                                                      --                         Just rr -> case reg of 
                                                                      --                                          Nothing -> -- M.insert key (lst ++ [(v, lc, reg, aliases)]) env
                                                                      --                                                      if mayalias
                                                                      --                                                      then M.insert key (lst ++ [(v, lc, reg', aliases)]) env
                                                                      --                                                      else M.insert key ([(v, lc, reg', aliases)]) env
                                                                      --                                          Just rr' -> if rr /= rr'
                                                                      --                                                      then error "Expected the regions to be the same!\n"
                                                                      --                                                      else if mayalias
                                                                      --                                                      then M.insert key (lst ++ [(v, lc, reg', aliases)]) env
                                                                      --                                                      else M.insert key ([(v, lc, reg', aliases)]) env
                                                                                                            
                                                                                                                     

updateMutableLocOldValueEnv :: LocVar -> MutableLocOldValueEnv -> (Var, Maybe LocVar, Maybe RegVar, S.Set Var) -> Bool -> PassM (MutableLocOldValueEnv, [Binds Exp3])
updateMutableLocOldValueEnv key env (v, lc, reg, aliases) mayalias = case M.lookup key env of 
                                                                              Nothing -> do
                                                                                         case key of 
                                                                                              Single{} -> do 
                                                                                                          deref_var <- gensym "deref"
                                                                                                          let bnd = [(deref_var, [], CursorTy, Ext $ DerefMutCursor v)]                                                                                
                                                                                                          pure (M.insert key (deref_var, lc, reg, aliases) env, bnd) 
                                                                                              SoA{} -> do 
                                                                                                       cpy <- gensym "cpy"
                                                                                                       let cpy_ty = getCursorizeTyFromLocVar'' Nothing True key
                                                                                                       let memcpy_intr = [(cpy, [], cpy_ty, Ext $ InitCursor cpy_ty), ("_", [], ProdTy [], Ext $ MemCpy cpy v cpy_ty)]
                                                                                                       pure (M.insert key (cpy, lc, reg, aliases) env, memcpy_intr) 



                                                                              Just (v', lc', reg', aliases') -> case reg' of 
                                                                                                                      Nothing -> if mayalias 
                                                                                                                                 then return (M.insert key (v, lc, reg, S.union (S.insert v' aliases') aliases) env, [])
                                                                                                                                 else return (M.insert key (v', lc', reg, aliases') env, [])
                                                                                                                      Just rr -> case reg of 
                                                                                                                                      Nothing -> if mayalias 
                                                                                                                                                 then return (M.insert key (v, lc, reg', S.union (S.insert v' aliases') aliases) env, [])
                                                                                                                                                 else return (M.insert key (v', lc', reg', aliases') env, [])
                                                                                                                                      Just rr' -> if rr /= rr'
                                                                                                                                                  then error "Expected region for location to not change!!\n"
                                                                                                                                                  else if mayalias 
                                                                                                                                                  then return (M.insert key (v, lc, reg, S.union (S.insert v' aliases') aliases) env, [])
                                                                                                                                                  else return (M.insert key (v', lc', reg', aliases') env, [])





-- For a single location variable, its modality will determine which type of 
-- Cursor will be assigned to it. 
singleLocToCursorBasedOnModality :: LocVar -> Maybe L2.Modality -> Bool -> Ty3 
singleLocToCursorBasedOnModality lc modality _isTailAndOverrideModality = if False 
                                                                          then MutCursorTy
                                                                          else case modality of 
                                                                                  Nothing -> if _isTailAndOverrideModality
                                                                                             then MutCursorTy
                                                                                             else CursorTy 
                                                                                  Just m -> case (lc, m) of
                                                                                              (Single{}, L2.Input) -> CursorTy
                                                                                              (Single{}, L2.InputMutable) -> MutCursorTy
                                                                                              (Single{}, L2.Output) -> CursorTy
                                                                                              (Single{}, L2.OutputMutable) -> MutCursorTy
                                                                                              _ -> error "Did not expect LocVar!!"

-- For a single location variable, its modality will determine which type of 
-- Cursor will be assigned to it. Returns L2.Ty2
singleLocToCursorBasedOnModalityL2 :: LocVar -> Maybe L2.Modality -> Bool -> L2.Ty2
singleLocToCursorBasedOnModalityL2 lc modality _isTailAndOverrideModality = if False
                                                                            then L2.MkTy2 MutCursorTy
                                                                            else case modality of 
                                                                             Nothing -> if _isTailAndOverrideModality
                                                                                        then L2.MkTy2 MutCursorTy
                                                                                        else L2.MkTy2 CursorTy
                                                                             Just m -> case (lc, m) of
                                                                                           (Single{}, L2.Input) -> L2.MkTy2 CursorTy
                                                                                           (Single{}, L2.InputMutable) -> L2.MkTy2 MutCursorTy
                                                                                           (Single{}, L2.Output) -> L2.MkTy2 CursorTy
                                                                                           (Single{}, L2.OutputMutable) -> L2.MkTy2 MutCursorTy
                                                                                           _ -> error "Did not expect LocVar!!"

-- For a single location variable, its modality will determine which type of 
-- Cursor will be assigned to it. Returns UrTy loc
singleLocToCursorBasedOnModalityUrTy :: LocVar -> Maybe L2.Modality -> Bool -> UrTy loc
singleLocToCursorBasedOnModalityUrTy lc modality _isTailAndOverrideModality = if False
                                                                              then MutCursorTy 
                                                                              else case modality of 
                                                                                        Nothing -> if _isTailAndOverrideModality 
                                                                                                   then MutCursorTy
                                                                                                   else CursorTy
                                                                                        Just m -> case (lc, m) of
                                                                                                       (Single{}, L2.Input) -> CursorTy
                                                                                                       (Single{}, L2.InputMutable) -> MutCursorTy
                                                                                                       (Single{}, L2.Output) -> CursorTy
                                                                                                       (Single{}, L2.OutputMutable) -> MutCursorTy
                                                                                                       _ -> error "Did not expect LocVar!!"



-- For a single region variable, its modality will determine which type of 
-- Cursor will be assigned to it.
singleRegToCursorBasedOnModality :: RegVar -> Maybe L2.Modality -> Bool -> Ty3 
singleRegToCursorBasedOnModality lc modality _isTailAndOverrideModality = if False
                                                                                   then MutCursorTy
                                                                                   else case modality of 
                                                                                              Nothing -> if _isTailAndOverrideModality
                                                                                                         then MutCursorTy
                                                                                                         else CursorTy
                                                                                              Just m -> case (lc, m) of
                                                                                                             (SingleR{}, L2.Input) -> CursorTy
                                                                                                             (SingleR{}, L2.InputMutable) -> MutCursorTy
                                                                                                             (SingleR{}, L2.Output) -> CursorTy
                                                                                                             (SingleR{}, L2.OutputMutable) -> MutCursorTy
                                                                                                             _ -> error "Did not expect LocVar!!"

-- For a single region variable, its modality will determine which type of 
-- Cursor will be assigned to it.
singleRegToCursorBasedOnModalityL2 :: RegVar -> Maybe L2.Modality -> Bool -> L2.Ty2 
singleRegToCursorBasedOnModalityL2 lc modality _isTailAndOverrideModality = if False
                                                                            then L2.MkTy2 MutCursorTy
                                                                            else
                                                                             case modality of 
                                                                              Nothing -> if _isTailAndOverrideModality 
                                                                                         then L2.MkTy2 CursorTy
                                                                                         else L2.MkTy2 MutCursorTy
                                                                              Just m -> case (lc, m) of
                                                                                                   (SingleR{}, L2.Input) -> L2.MkTy2 CursorTy
                                                                                                   (SingleR{}, L2.InputMutable) -> L2.MkTy2 MutCursorTy
                                                                                                   (SingleR{}, L2.Output) -> L2.MkTy2 CursorTy
                                                                                                   (SingleR{}, L2.OutputMutable) -> L2.MkTy2 MutCursorTy
                                                                                                   _ -> error "Did not expect LocVar!!"


-- For a single region variable, its modality will determine which type of 
-- Cursor will be assigned to it.
singleRegToCursorBasedOnModalityUrTy :: RegVar -> Maybe L2.Modality -> Bool-> UrTy loc 
singleRegToCursorBasedOnModalityUrTy lc modality _isTailAndOverrideModality = if False
                                                                              then MutCursorTy 
                                                                              else 
                                                                               case modality of 
                                                                                    Nothing -> if _isTailAndOverrideModality
                                                                                               then MutCursorTy
                                                                                               else CursorTy
                                                                                    Just m -> case (lc, m) of
                                                                                                   (SingleR{}, L2.Input) -> CursorTy
                                                                                                   (SingleR{}, L2.InputMutable) -> MutCursorTy
                                                                                                   (SingleR{}, L2.Output) -> CursorTy
                                                                                                   (SingleR{}, L2.OutputMutable) -> MutCursorTy
                                                                                                   _ -> error "Did not expect LocVar!!"


getIndexPositionOfSoALocVar :: Bool -> Maybe L2.Modality -> [((DataCon, Int), LocVar)] -> LocVar -> (Int, Int, Bool)
getIndexPositionOfSoALocVar _isTailAndOverrideModality modality flds loc = foldl (\(s, e, b) (_, fl) -> if b 
                                                                    then
                                                                      (s, e, True)
                                                                    else
                                                                      let seen = if fl == loc then True else False
                                                                       in case fl of 
                                                                          Single{} -> (e, e + 1, seen) 
                                                                          SoA{} -> let (CursorArrayTy sz) = getCursorizeTyFromLocVar modality False fl 
                                                                                    in (e, e + sz, seen)
                                             ) (1, 1, False) flds 

getIndexPositionOfSoARegVar :: Bool -> Maybe L2.Modality -> [((DataCon, Int), RegVar)] -> RegVar -> (Int, Int, Bool)
getIndexPositionOfSoARegVar _isTailAndOverrideModality modality flds loc = foldl (\(s, e, b) (_, fl) -> if b 
                                                                    then
                                                                      (s, e, True)
                                                                    else
                                                                      let seen = if fl == loc then True else False
                                                                       in case fl of 
                                                                          SingleR{} -> (e, e + 1, seen) 
                                                                          SoARv{} -> let (CursorArrayTy sz) = getCursorizeTyFromRegVar modality False fl 
                                                                                    in (e, e + sz, seen)
                                             ) (1, 1, False) flds 

linearizeLocVar :: LocVar -> [LocVar]
linearizeLocVar loc = case loc of 
                            Single{} -> [loc]
                            SoA dcloc flocs -> let flinear = concatMap (\(_, fl) -> linearizeLocVar fl) flocs
                                                 in [singleLocVar dcloc] ++ flinear


linearizeRegVar :: RegVar -> [RegVar]
linearizeRegVar loc = case loc of 
                            SingleR{} -> [loc]
                            SoARv dcloc flocs -> let flinear = concatMap (\(_, fl) -> linearizeRegVar fl) flocs
                                                 in [dcloc] ++ flinear

getCursorizeTyFromLocVar :: Maybe L2.Modality -> Bool -> LocVar -> Ty3
getCursorizeTyFromLocVar modality _isTailAndOverrideModality lc = case lc of 
                                  Single{} -> singleLocToCursorBasedOnModality lc modality False
                                  SoA _ flds -> let size_flds = foldr (\(_, flc) len -> case flc of 
                                                                                                    Single{} -> len + 1
                                                                                                    -- For an SoA location 
                                                                                                    -- For now, outer modality also determines 
                                                                                                    -- the inner modality.
                                                                                                    SoA{} -> let ty3 = getCursorizeTyFromLocVar modality False flc 
                                                                                                              in case ty3 of 
                                                                                                                       CursorArrayTy sz -> len + sz
                                                                                                                       _ -> error "Did not expect type!"
                                                                                 ) 0 flds
                                                  in CursorArrayTy (1 + size_flds)

getCursorizeTyFromRegVar :: Maybe L2.Modality -> Bool -> RegVar -> Ty3
getCursorizeTyFromRegVar modality _isTailAndOverrideModality rv = case rv of 
                                  SingleR{} -> singleRegToCursorBasedOnModality rv modality False
                                  SoARv _ flds -> let size_flds = foldr (\(_, flr) len -> case flr of
                                                                                                SingleR{} -> len + 1
                                                                                                SoARv{} -> let ty3 = getCursorizeTyFromRegVar modality False flr
                                                                                                           in case ty3 of 
                                                                                                                  CursorArrayTy sz -> len + sz 
                                                                                                                  _ -> error "Did not expect type!"
                                                                        ) 0 flds
                                                   in CursorArrayTy (1 + size_flds)


getCursorizeTyFromLocVar' :: Maybe L2.Modality -> Bool -> LocVar -> L2.Ty2
getCursorizeTyFromLocVar' modality _isTailAndOverrideModality lc = case lc of 
                                  Single{} -> singleLocToCursorBasedOnModalityL2 lc modality False 
                                  SoA _ flds -> let size_flds = foldr (\(_, flc) len -> case flc of 
                                                                                                    Single{} -> len + 1
                                                                                                    SoA{} -> let ty3 = getCursorizeTyFromLocVar modality False flc 
                                                                                                              in case ty3 of 
                                                                                                                       CursorArrayTy sz -> len + sz
                                                                                                                       _ -> error "Did not expect type!"
                                                                                 ) 0 flds
                                                  in L2.MkTy2 $ CursorArrayTy (1 + size_flds)

getCursorizeTyFromRegVar' :: Maybe L2.Modality -> Bool -> RegVar -> L2.Ty2
getCursorizeTyFromRegVar' modality _isTailAndOverrideModality rv = case rv of 
                                  SingleR{} -> singleRegToCursorBasedOnModalityL2 rv modality False
                                  SoARv _ flds -> let size_flds = foldr (\(_, flr) len -> case flr of
                                                                                                SingleR{} -> len + 1
                                                                                                SoARv{} -> let ty3 = getCursorizeTyFromRegVar modality False flr
                                                                                                           in case ty3 of 
                                                                                                                  CursorArrayTy sz -> len + sz 
                                                                                                                  _ -> error "Did not expect type!"
                                                                        ) 0 flds
                                                   in L2.MkTy2 $ CursorArrayTy (1 + size_flds)


getCursorizeTyFromLocVar'' :: Maybe L2.Modality -> Bool -> LocVar -> UrTy loc
getCursorizeTyFromLocVar'' modality _isTailAndOverrideModality lc = case lc of 
                                  Single{} -> singleLocToCursorBasedOnModalityUrTy lc modality False 
                                  SoA _ flds -> let size_flds = foldr (\(_, flc) len -> case flc of 
                                                                                                    Single{} -> len + 1
                                                                                                    SoA{} -> let ty3 = getCursorizeTyFromLocVar modality False flc 
                                                                                                              in case ty3 of 
                                                                                                                       CursorArrayTy sz -> len + sz
                                                                                                                       _ -> error "Did not expect type!"
                                                                                 ) 0 flds
                                                  in CursorArrayTy (1 + size_flds)

getCursorizeTyFromRegVar'' :: Maybe L2.Modality -> Bool -> RegVar -> UrTy loc
getCursorizeTyFromRegVar'' modality _isTailAndOverrideModality rv = case rv of 
                                  SingleR{} -> singleRegToCursorBasedOnModalityUrTy rv modality False
                                  SoARv _ flds -> let size_flds = foldr (\(_, flr) len -> case flr of
                                                                                                SingleR{} -> len + 1
                                                                                                SoARv{} -> let ty3 = getCursorizeTyFromRegVar modality False flr
                                                                                                           in case ty3 of 
                                                                                                                  CursorArrayTy sz -> len + sz 
                                                                                                                  _ -> error "Did not expect type!"
                                                                        ) 0 flds
                                                   in CursorArrayTy (1 + size_flds)


getCursorizeTyFromLocVar''' :: Maybe L2.Modality -> Bool -> LocVar -> UrTy ()
getCursorizeTyFromLocVar''' modality _isTailAndOverrideModality lc = case lc of 
                                  Single{} -> singleLocToCursorBasedOnModalityUrTy lc modality False
                                  SoA _ flds -> let size_flds = foldr (\(_, flc) len -> case flc of 
                                                                                                    Single{} -> len + 1
                                                                                                    SoA{} -> let ty3 = getCursorizeTyFromLocVar modality False flc 
                                                                                                              in case ty3 of 
                                                                                                                       CursorArrayTy sz -> len + sz
                                                                                                                       _ -> error "Did not expect type!"
                                                                                 ) 0 flds
                                                  in CursorArrayTy (1 + size_flds)

getCursorizeTyFromRegVar''' :: Maybe L2.Modality -> Bool -> RegVar -> UrTy ()
getCursorizeTyFromRegVar''' modality _isTailAndOverrideModality rv = case rv of 
                                  SingleR{} -> singleRegToCursorBasedOnModalityUrTy rv modality False
                                  -- For SoA regions, arrays, are addresses so we don't need to change their type
                                  -- in case we want to mutate them in place.
                                  SoARv _ flds -> let size_flds = foldr (\(_, flr) len -> case flr of
                                                                                                SingleR{} -> len + 1
                                                                                                SoARv{} -> let ty3 = getCursorizeTyFromRegVar modality False flr
                                                                                                           in case ty3 of 
                                                                                                                  CursorArrayTy sz -> len + sz 
                                                                                                                  _ -> error "Did not expect type!"
                                                                        ) 0 flds
                                                   in CursorArrayTy (1 + size_flds)


-----------------------------------------------------------------------------------------
-- Do this manually to get prettier formatting: (Issue #90)

instance (Out l, Out d) => Out (E3Ext l d)

-----------------------------------------------------------------------------------------

-- | Erase LocVar markers from the data definition
eraseLocMarkers :: DDef L2.Ty2 -> DDef Ty3
eraseLocMarkers (DDef tyargs tyname ls layout) = DDef tyargs tyname (L.map go ls) layout
  where go :: (DataCon,[(IsBoxed,L2.Ty2)]) -> (DataCon,[(IsBoxed,Ty3)])
        go (dcon,ls') = (dcon, L.map (\(b,ty) -> (b,L2.stripTyLocs (L2.unTy2 ty))) ls')

cursorizeTy :: M.Map FreeVarsTy Var -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Maybe L2.Modality -> UrTy LocVar -> UrTy b
cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality ty =
  case ty of
    IntTy     -> IntTy
    CharTy    -> CharTy
    FloatTy   -> FloatTy
    SymTy     -> SymTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map (cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality) ls
    SymDictTy v _ -> SymDictTy v CursorTy
    PDictTy k v   -> PDictTy (cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality k) (cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality v)
    -- Check if location in the packed type is a locations pointer to by 
    -- any mutable location, (We should not return start and end locations for such types) 
    PackedTy _ l    -> let lname = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l) 
                           mut_l = findMutableLocationPointingToVar lname mutLocsEnv
                        in 
                          if Mb.isJust mut_l
                          then dbgTrace (minChatLvl) "Print env in cursorizeTy: " dbgTrace (minChatLvl) (sdoc (M.toList mutLocsEnv)) dbgTrace (minChatLvl) "End in cursorizeTy.\n" ProdTy []
                          -- If the location in questionk itself is a mutable location.
                          else if M.member l oldLocsToMutEnv
                          then ProdTy []
                          else dbgTrace (minChatLvl) "Print env in cursorizeTy: " dbgTrace (minChatLvl) (sdoc (M.toList mutLocsEnv)) dbgTrace (minChatLvl) "End in cursorizeTy.\n" ProdTy [getCursorizeTyFromLocVar'' modality isTailAndOverrideModality l, getCursorizeTyFromLocVar'' modality isTailAndOverrideModality l]
    VectorTy el_ty' -> VectorTy $ cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality el_ty'
    ListTy el_ty'   -> ListTy $ cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality el_ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    CursorArrayTy sz -> CursorArrayTy sz 
    MutCursorTy -> MutCursorTy
    ArenaTy  -> ArenaTy
    SymSetTy -> SymSetTy
    SymHashTy-> SymHashTy
    IntHashTy-> IntHashTy

-- | Map exprs with an initial type environment:
-- Exactly the same function that was in L2 before
mapMExprs :: Monad m => (Env2 Var Ty3 -> Exp3 -> m Exp3) -> Prog3 -> m Prog3
mapMExprs fn (Prog ddfs fundefs mainExp) =
  Prog ddfs <$>
    (mapM (\f@FunDef{funArgs,funTy,funBody} ->
              let env = Env2 (M.fromList $ zip funArgs (fst funTy)) funEnv
              in do
                bod' <- fn env funBody
                return $ f { funBody =  bod' })
     fundefs)
    <*>
    (mapM (\ (e,t) -> (,t) <$> fn (Env2 M.empty funEnv) e) mainExp)
  where funEnv = M.map funTy fundefs

toL3Prim :: Prim L2.Ty2 -> Prim Ty3
toL3Prim (DictEmptyP  _ty) = DictEmptyP  CursorTy
toL3Prim (DictInsertP _ty) = DictInsertP CursorTy
toL3Prim (DictLookupP _ty) = DictLookupP CursorTy
toL3Prim (DictHasKeyP _ty) = DictHasKeyP CursorTy
toL3Prim pr = fmap (L2.stripTyLocs . L2.unTy2) pr

-- |
updateAvailVars :: [Var] -> [Var] -> Exp3 -> Exp3
updateAvailVars froms tos ex =
  case ex of
    VarE v          -> VarE v
    LitE _          -> ex
    CharE _         -> ex
    FloatE{}        -> ex
    LitSymE _       -> ex
    AppE v cty loc ls   -> AppE v cty loc (map go ls)
    PrimAppE p ls   -> PrimAppE p $ L.map go ls
    LetE (v,loc,t,rhs) bod -> LetE (v,loc,t,go rhs) (go bod)
    ProjE i e         -> ProjE i (go e)
    CaseE e ls        -> CaseE (go e) (L.map (\(c,vs,er) -> (c,vs,go er)) ls)
    MkProdE ls        -> MkProdE $ L.map go ls
    DataConE loc k ls -> DataConE loc k $ L.map go ls
    TimeIt e t b      -> TimeIt (go e) t b
    IfE a b c         -> IfE (go a) (go b) (go c)
    SpawnE v loc ls   -> SpawnE v loc (map go ls)
    SyncE             -> SyncE
    WithArenaE v e    -> WithArenaE v (go e)
    MapE (v,t,rhs) bod -> MapE (v,t, go rhs) (go bod)
    FoldE (v1,t1,r1) (v2,t2,r2) bod ->
      FoldE (v1,t1,go r1) (v2,t2,go r2) (go bod)
    Ext ext ->
      case ext of
        LetAvail vs bod ->
          let n o = if o `elem` froms then tos else [o]
              vs' = foldr (\v acc -> n v ++ acc) [] vs
          in Ext $ LetAvail vs' (go bod)
        ForE idx bound bod ->
          let pairs = [ (from, to) | (from, to) <- zip froms tos, from /= idx ]
              froms' = map fst pairs
              tos' = map snd pairs
          in Ext $ ForE idx (go bound) (updateAvailVars froms' tos' bod)
        _ -> ex
  where
    go = updateAvailVars froms tos
