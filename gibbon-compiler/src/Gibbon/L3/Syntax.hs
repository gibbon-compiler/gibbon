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
  , isIntScalar, intScalarWidth, intScalarWidthMaybe, intS64
  , VecOp(..), vecOpName, simdScalarBytes, simdLanes
  , simdRegisterBytes, simdRegisterBytesAvx2
  , simdScalarEnabled, simdCapable, simdCapableWith, simdLanesValid, simdLanesValidAny
  , simdLogicalStride, simdGroups, simdStrideValid, orderedCmps
  , VecCmpOp(..), vecCmpOp, vecCmpName

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
  | WriteCursorSelectiveIndirection Var Var Var (PreExp E3Ext loc dec)
    -- ^ Write a selective sharing wrapper.  The fourth argument is a mask
    -- describing which SoA buffers are selectively wrapped in this value.
  | UnwrapSelectiveIndirections Int Var Var
    -- ^ Given a SoA cursor-array length, end cursor array, and data cursor
    -- array, unwrap any buffers listed in a dcon selective-indirection mask.
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
  | ScalarCountBump DataCon [(Var, Int)]
    -- ^ Constructor-level homogeneous-buffer count instrumentation. The
    -- DataCon is the semantic event; the Vars are the affected SoA output
    -- buffers for this constructor, including the dcon buffer and any scalar
    -- field buffers.
    --
    -- The Int is the buffer's deferred-count slot: 'Cursorize' emits the
    -- buffer's position in the SoA cursor array, and 'AssignScalarCountSlots'
    -- rebases it to a program-global slot.  See Note [Deferred scalar counts].
  | ScalarCountBind Int Int Var
    -- ^ Bind deferred-count slots [base, base+len) to the regions owning the
    -- buffers of an SoA end-cursor array, immediately BEFORE a producer call.
    -- The region is allocated by the caller, so its footer is already live.
  | ScalarCountFinalize Int Int Var
    -- ^ Flush deferred-count slots [base, base+len) into their footers,
    -- immediately AFTER a producer call.  Growth accounts for every chunk but
    -- the last; this accounts for the last one.
  | ScalarCountSet Var Var
    -- ^ Set homogeneous-buffer count metadata for a chunk.  The first Var is
    -- the output region footer/end cursor, and the second Var is the count to
    -- store.  Shape-preserving loopified traversals use this once per chunk
    -- instead of bumping once per element.
  | ScalarCountCopyAll Int Var Var
    -- ^ Copy scalar-count footer metadata for a fully factored SoA value.
    -- The Int is the cursor-array length. The first Var is the output end
    -- cursor array, and the second Var is the input end cursor array. This
    -- copies footer chains buffer-by-buffer, so propagation is O(buffers *
    -- chunks) rather than O(elements).
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
  | WhileCursorEnd Var Var (PreExp E3Ext loc dec)
    -- ^ A statement-like loop that repeats while the first mutable cursor ref
    -- has not reached the second mutable cursor ref.  This is used by flat
    -- AoS loopified traversals, where the input value end is the loop bound.
  | VecBroadcast Scalar Int (PreExp E3Ext loc dec)
    -- ^ Broadcast a scalar expression into a fixed-width SIMD register.
  | VecLoad Scalar Int Var
    -- ^ Load a SIMD register from the cursor stored in a mutable cursor ref.
  | VecAdd Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise SIMD addition.
  | VecSub Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise SIMD subtraction.
  | VecMul Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise SIMD multiplication, for scalar kinds with backend support.
  | VecDiv Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise SIMD division, for scalar kinds with backend support.
  | VecMod Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise SIMD modulus, for scalar kinds with backend support.
  | VecCmp Scalar Int VecCmpOp (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise equality producing an all-bits mask in the same register type.
  | VecSelect Scalar Int (PreExp E3Ext loc dec) (PreExp E3Ext loc dec) (PreExp E3Ext loc dec)
    -- ^ Lane-wise select: mask, then-value, else-value.
  | VecStore Scalar Int Var (PreExp E3Ext loc dec)
    -- ^ Store a SIMD register to the cursor stored in a mutable cursor ref.
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
      WriteCursorSelectiveIndirection a b c mask -> S.fromList [a,b,c] `S.union` gFreeVars mask
      UnwrapSelectiveIndirections _ ends curs -> S.fromList [ends, curs]
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
      ScalarCountBump _ footers -> S.fromList (L.map fst footers)
      ScalarCountBind _ _ ends -> S.singleton ends
      ScalarCountFinalize _ _ ends -> S.singleton ends
      ScalarCountSet footer count -> S.fromList [footer, count]
      ScalarCountCopyAll _ dstEnds srcEnds -> S.fromList [dstEnds, srcEnds]
      ReadScalarCount v -> S.singleton v
      ReadScalarCountFirstFooter v -> S.singleton v
      ReadScalarCountNextFooter v -> S.singleton v
      ForE idx bound bod ->
        gFreeVars bound `S.union` S.delete idx (gFreeVars bod)
      WhileCursor ref bod ->
        S.insert ref (gFreeVars bod)
      WhileCursorEnd cur end bod ->
        S.insert cur (S.insert end (gFreeVars bod))
      VecBroadcast _ _ val -> gFreeVars val
      VecLoad _ _ ref -> S.singleton ref
      VecAdd _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecSub _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecMul _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecDiv _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecMod _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecCmp _ _ _ a b -> gFreeVars a `S.union` gFreeVars b
      VecSelect _ _ m a b -> S.unions [gFreeVars m, gFreeVars a, gFreeVars b]
      VecStore _ _ ref val -> S.insert ref (gFreeVars val)
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
    gRecoverType _ _ (ScalarCountSet {}) = ProdTy []
    gRecoverType _ _ (ScalarCountBind {}) = ProdTy []
    gRecoverType _ _ (ScalarCountFinalize {}) = ProdTy []
    gRecoverType _ _ (ScalarCountCopyAll {}) = ProdTy []
    gRecoverType _ _ (ReadScalarCount {}) = (IntTy W64)
    gRecoverType _ _ (ReadScalarCountFirstFooter {}) = CursorTy
    gRecoverType _ _ (ReadScalarCountNextFooter {}) = CursorTy
    gRecoverType _ _ (ForE {}) = ProdTy []
    gRecoverType _ _ (WhileCursor {}) = ProdTy []
    gRecoverType _ _ (WhileCursorEnd {}) = ProdTy []
    gRecoverType _ _ (VecBroadcast s lanes _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecLoad s lanes _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecAdd s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecSub s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecMul s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecDiv s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecMod s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecCmp s lanes _ _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecSelect s lanes _ _ _) = SimdTy (scalarToTy s) lanes
    gRecoverType _ _ (VecStore {}) = ProdTy []
    gRecoverType _ _ (WriteTagPacked {}) = CursorTy
    gRecoverType _ _ (WriteCursorSelectiveIndirection {}) = CursorTy
    gRecoverType _ _ (UnwrapSelectiveIndirections {}) = ProdTy []
    gRecoverType _ _ (GrowRegion {}) = ProdTy []
    gRecoverType _ _ _ = error "L3.gRecoverType"


    gRecoverTypeLoc _ddfs _env2 NullCursor = CursorTy
    gRecoverTypeLoc ddfs env2 (RetE ls)    = ProdTy $ L.map (gRecoverTypeLoc ddfs env2) ls
    gRecoverTypeLoc _ _ (MakeCursorArray {}) = error "gRecoverType: MakeCursorArray not handled"
    gRecoverTypeLoc _ _ (IndexCursorArray {}) = error "gRecoverType: IndexCursorArray not handled"
    gRecoverTypeLoc _ _ (CastPtr {}) = error "gRecoverType: CastPtr not handled"
    gRecoverTypeLoc _ _ (BoundsCheckVector {}) = error "gRecoverType: BoundsCheckVector not handled"
    gRecoverTypeLoc _ _ (ScalarCountSet {}) = ProdTy []
    gRecoverTypeLoc _ _ (ScalarCountBind {}) = ProdTy []
    gRecoverTypeLoc _ _ (ScalarCountFinalize {}) = ProdTy []
    gRecoverTypeLoc _ _ (ScalarCountCopyAll {}) = ProdTy []
    gRecoverTypeLoc _ _ (ReadScalarCount {}) = (IntTy W64)
    gRecoverTypeLoc _ _ (ReadScalarCountFirstFooter {}) = CursorTy
    gRecoverTypeLoc _ _ (ReadScalarCountNextFooter {}) = CursorTy
    gRecoverTypeLoc _ _ (ForE {}) = ProdTy []
    gRecoverTypeLoc _ _ (WhileCursor {}) = ProdTy []
    gRecoverTypeLoc _ _ (WhileCursorEnd {}) = ProdTy []
    gRecoverTypeLoc _ _ (VecBroadcast s lanes _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecLoad s lanes _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecAdd s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecSub s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecMul s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecDiv s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecMod s lanes _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecCmp s lanes _ _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecSelect s lanes _ _ _) = SimdTy (scalarToTy s) lanes
    gRecoverTypeLoc _ _ (VecStore {}) = ProdTy []
    gRecoverTypeLoc _ _ (WriteTagPacked {}) = CursorTy
    gRecoverTypeLoc _ _ (WriteCursorSelectiveIndirection {}) = CursorTy
    gRecoverTypeLoc _ _ (UnwrapSelectiveIndirections {}) = ProdTy []
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
      WriteCursorSelectiveIndirection a b c mask ->
        WriteCursorSelectiveIndirection a b c (gSubst old new mask)
      GrowRegion v w       -> GrowRegion v w
      WriteCursorMutable v bod    -> WriteCursorMutable v (gSubst old new bod)
      AddCursor v bod      -> AddCursor v (gSubst old new bod)
      SubPtr v w           -> SubPtr v w
      LetAvail ls bod      -> LetAvail ls (gSubst old new bod)
      ForE idx bound bod
        | idx == old -> ForE idx (gSubst old new bound) bod
        | otherwise  -> ForE idx (gSubst old new bound) (gSubst old new bod)
      WhileCursor ref bod  -> WhileCursor ref (gSubst old new bod)
      WhileCursorEnd cur end bod -> WhileCursorEnd cur end (gSubst old new bod)
      VecBroadcast s lanes val -> VecBroadcast s lanes (gSubst old new val)
      VecAdd s lanes a b -> VecAdd s lanes (gSubst old new a) (gSubst old new b)
      VecSub s lanes a b -> VecSub s lanes (gSubst old new a) (gSubst old new b)
      VecMul s lanes a b -> VecMul s lanes (gSubst old new a) (gSubst old new b)
      VecDiv s lanes a b -> VecDiv s lanes (gSubst old new a) (gSubst old new b)
      VecMod s lanes a b -> VecMod s lanes (gSubst old new a) (gSubst old new b)
      VecCmp s lanes c a b -> VecCmp s lanes c (gSubst old new a) (gSubst old new b)
      VecSelect s lanes m a b -> VecSelect s lanes (gSubst old new m) (gSubst old new a) (gSubst old new b)
      VecStore s lanes ref val -> VecStore s lanes ref (gSubst old new val)
      MakeCursorArray{}    -> ext
      IndexCursorArray{}   -> ext
      CastPtr{}            -> ext
      BoundsCheckVector{}  -> ext
      _ -> ext

  gSubstEExt old new ext =
    case ext of
      WriteScalar s v bod    -> WriteScalar s v (gSubstE old new bod)
      WriteTagPacked v bod   -> WriteTagPacked v (gSubstE old new bod)
      WriteCursorSelectiveIndirection a b c mask ->
        WriteCursorSelectiveIndirection a b c (gSubstE old new mask)
      GrowRegion v w         -> GrowRegion v w
      WriteCursorMutable v bod -> WriteCursorMutable v (gSubstE old new bod)
      AddCursor v bod   -> AddCursor v (gSubstE old new bod)
      SubPtr v w        -> SubPtr v w
      LetAvail ls b     -> LetAvail ls (gSubstE old new b)
      ForE idx bound bod -> ForE idx (gSubstE old new bound) (gSubstE old new bod)
      WhileCursor ref bod -> WhileCursor ref (gSubstE old new bod)
      WhileCursorEnd cur end bod -> WhileCursorEnd cur end (gSubstE old new bod)
      VecBroadcast s lanes val -> VecBroadcast s lanes (gSubstE old new val)
      VecAdd s lanes a b -> VecAdd s lanes (gSubstE old new a) (gSubstE old new b)
      VecSub s lanes a b -> VecSub s lanes (gSubstE old new a) (gSubstE old new b)
      VecMul s lanes a b -> VecMul s lanes (gSubstE old new a) (gSubstE old new b)
      VecDiv s lanes a b -> VecDiv s lanes (gSubstE old new a) (gSubstE old new b)
      VecMod s lanes a b -> VecMod s lanes (gSubstE old new a) (gSubstE old new b)
      VecCmp s lanes c a b -> VecCmp s lanes c (gSubstE old new a) (gSubstE old new b)
      VecSelect s lanes m a b -> VecSelect s lanes (gSubstE old new m) (gSubstE old new a) (gSubstE old new b)
      VecStore s lanes ref val -> VecStore s lanes ref (gSubstE old new val)
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
      WriteCursorSelectiveIndirection a b c mask -> WriteCursorSelectiveIndirection (go a) (go b) (go c) (go mask)
      UnwrapSelectiveIndirections n ends curs -> UnwrapSelectiveIndirections n (go ends) (go curs)
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
      ScalarCountBump dcon footers ->
        ScalarCountBump dcon (L.map (\(v, slot) -> (go v, slot)) footers)
      ScalarCountBind base len ends -> ScalarCountBind base len (go ends)
      ScalarCountFinalize base len ends -> ScalarCountFinalize base len (go ends)
      ScalarCountSet footer count -> ScalarCountSet (go footer) (go count)
      ScalarCountCopyAll len dstEnds srcEnds -> ScalarCountCopyAll len (go dstEnds) (go srcEnds)
      ReadScalarCount v -> ReadScalarCount (go v)
      ReadScalarCountFirstFooter v -> ReadScalarCountFirstFooter (go v)
      ReadScalarCountNextFooter v -> ReadScalarCountNextFooter (go v)
      ForE idx bound bod ->
        let env' = M.delete idx env
        in ForE idx (go bound) (gRename env' bod)
      WhileCursor ref bod -> WhileCursor (go ref) (go bod)
      WhileCursorEnd cur end bod -> WhileCursorEnd (go cur) (go end) (go bod)
      VecBroadcast s lanes val -> VecBroadcast s lanes (go val)
      VecLoad s lanes ref -> VecLoad s lanes (go ref)
      VecAdd s lanes a b -> VecAdd s lanes (go a) (go b)
      VecSub s lanes a b -> VecSub s lanes (go a) (go b)
      VecMul s lanes a b -> VecMul s lanes (go a) (go b)
      VecDiv s lanes a b -> VecDiv s lanes (go a) (go b)
      VecMod s lanes a b -> VecMod s lanes (go a) (go b)
      VecCmp s lanes c a b -> VecCmp s lanes c (go a) (go b)
      VecSelect s lanes m a b -> VecSelect s lanes (go m) (go a) (go b)
      VecStore s lanes ref val -> VecStore s lanes (go ref) (go val)
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

-- | The kind of a scalar value stored in a packed buffer.
--
-- The integer scalar carries its exact width: L3 is fully typed, so there is
-- no such thing as an unresolved scalar width here.  'mkScalar' and
-- 'scalarToTy' are exact inverses on integers -- nothing maps @IntS w@ back to
-- @IntTy W64@.
--
-- CAUTION: because the width is part of the constructor, @IntS W8 /= IntS W64@.
-- Never write @s == IntS ...@ or @s \`elem\` [IntS, ...]@ when the intent is
-- "any integer scalar"; use 'isIntScalar', or match @IntS{}@.
data Scalar = IntS IntWidth | CharS | FloatS | SymS | BoolS
  deriving (Show, Ord, Eq, Read, Generic, NFData, Out)

mkScalar :: Out a => UrTy a -> Scalar
mkScalar (IntTy w) = IntS w
mkScalar CharTy = CharS
mkScalar FloatTy= FloatS
mkScalar SymTy  = SymS
mkScalar BoolTy = BoolS
mkScalar ty = error $ "mkScalar: Not a scalar type: " ++ sdoc ty

scalarToTy :: Scalar -> UrTy a
scalarToTy (IntS w) = IntTy w
scalarToTy CharS = CharTy
scalarToTy FloatS= FloatTy
scalarToTy SymS  = SymTy
scalarToTy BoolS = BoolTy

-- | Is this scalar an integer, of any width?  Use this instead of comparing
-- against a particular 'IntS'.
--------------------------------------------------------------------------------
-- The SIMD capability matrix
--
-- ONE source of truth, shared by 'Gibbon.Passes.VectorizeTraversals' (which
-- decides whether to emit vector IR) and 'Gibbon.Passes.Codegen' (which decides
-- whether it can lower that IR).  A vectorizer "yes" paired with a backend "no"
-- is a compiler crash; a backend "yes" paired with a vectorizer "no" is dead
-- code that will rot.  Both sides call 'simdCapable', and a unit test asserts
-- they agree over the whole (op x scalar) space.
--------------------------------------------------------------------------------

-- | A vector operation the backend can be asked to emit.  Typed rather than
-- stringly: the old code passed operation names around as 'String', so a typo
-- degraded silently into "unsupported" instead of failing to compile.  Codegen
-- still needs a name for the emitted helper, but it derives it from this with
-- 'vecOpName' rather than accepting one from a caller.
data VecOp = VecOpBroadcast | VecOpLoad | VecOpStore
           | VecOpAdd | VecOpSub | VecOpMul | VecOpDiv | VecOpMod
           | VecOpEq | VecOpLt | VecOpGt | VecOpLtEq | VecOpGtEq
           | VecOpSelect
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out, Bounded, Enum)

vecOpName :: VecOp -> String
vecOpName op =
  case op of
    VecOpBroadcast -> "broadcast"
    VecOpLoad -> "load"
    VecOpStore -> "store"
    VecOpAdd -> "add"
    VecOpSub -> "sub"
    VecOpMul -> "mul"
    VecOpDiv -> "div"
    VecOpMod -> "mod"
    VecOpEq -> "eq"
    VecOpLt -> "lt"
    VecOpGt -> "gt"
    VecOpLtEq -> "le"
    VecOpGtEq -> "ge"
    VecOpSelect -> "select"

-- | Which comparison a 'VecCmp' node performs.
--
-- Typed rather than a string, and separate from 'VecOp' so a comparison node
-- cannot be built holding, say, 'VecOpAdd'.  'vecCmpOp' maps it into the
-- capability vocabulary, so the vectorizer and the backend still consult ONE
-- matrix.
data VecCmpOp = VecCmpEq | VecCmpLt | VecCmpGt | VecCmpLtEq | VecCmpGtEq
  deriving (Show, Read, Ord, Eq, Generic, NFData, Out, Bounded, Enum)

vecCmpOp :: VecCmpOp -> VecOp
vecCmpOp c =
  case c of
    VecCmpEq -> VecOpEq
    VecCmpLt -> VecOpLt
    VecCmpGt -> VecOpGt
    VecCmpLtEq -> VecOpLtEq
    VecCmpGtEq -> VecOpGtEq

vecCmpName :: VecCmpOp -> String
vecCmpName = vecOpName . vecCmpOp

-- | Bytes occupied by one lane holding @scalar@.
--
-- Total, and a property of the ACTUAL scalar -- never of a compiler flag.  An
-- integer's width comes from 'intWidthBytes', so adding W16/W8 SIMD needs no
-- change here.
simdScalarBytes :: Scalar -> Int
simdScalarBytes (IntS w) = intWidthBytes w
simdScalarBytes SymS = 8
simdScalarBytes FloatS = 4
simdScalarBytes CharS = 1
simdScalarBytes BoolS = 1

-- | Width in bytes of the baseline SSE2 vector register.
simdRegisterBytes :: Int
simdRegisterBytes = 16

-- | Width in bytes of the AVX2 vector register.
--
-- Every lane count is derived from whichever of these two the compilation
-- selected, so the vectorizer and the backend cannot disagree about how many
-- elements a register holds or how far a cursor advances.
simdRegisterBytesAvx2 :: Int
simdRegisterBytesAvx2 = 32

-- | The lane count that exactly tiles the 128-bit register for @scalar@.
--
-- W64 -> 2, W32 -> 4, W16 -> 8, W8 -> 16.  This is the single definition of
-- "how many elements fit"; the vectorizer and the backend both use it, so they
-- cannot disagree about cursor arithmetic.
simdLanes :: Int -> Scalar -> Int
simdLanes regBytes s = regBytes `div` simdScalarBytes s

-- | Does this (scalar, lanes) pair exactly fill the register?  Anything else is
-- malformed IR and must fail loudly rather than emit a short or overlong access.
-- | The matrix as the compiler applies it by default: W64 multiply refused.
simdCapable :: VecOp -> Scalar -> Bool
simdCapable = simdCapableWith False

simdLanesValid :: Int -> Scalar -> Int -> Bool
simdLanesValid regBytes scalar lanes =
  lanes == simdLanes regBytes scalar
    && lanes * simdScalarBytes scalar == regBytes

-- | Does this (scalar, lanes) pair exactly fill a SIMD register of SOME width
-- this backend emits helpers for -- 128-bit SSE2 or 256-bit AVX2?
--
-- The backend's pure naming path only sees the lane count the IR carries, not
-- the width the compilation selected, so it asks this rather than pinning one
-- width.  A malformed pair such as @(IntS W32, 2)@ still fails loudly; only a
-- whole register of a supported width passes.
simdLanesValidAny :: Scalar -> Int -> Bool
simdLanesValidAny scalar lanes =
  any (\rb -> simdLanesValid rb scalar lanes)
      [simdRegisterBytes, simdRegisterBytesAvx2]

-- | The number of LOGICAL RECORDS one vector iteration of a fused loop
-- processes, given every scalar written by that loop.
--
-- A fused loopified traversal can write several independent scalar buffers of
-- DIFFERENT widths in one @ForE@.  They must all advance in lockstep over the
-- same records, but their registers hold different numbers of elements
-- (W64->2, W32->4, W16->8, W8->16).  The stride is therefore the widest lane
-- count present, so that every participating scalar covers the stride with an
-- INTEGRAL number of full registers:
--
-- >  simdGroups stride s  =  stride \/ simdLanes s
--
-- Lane counts are all powers of two and the stride is the maximum of them, so
-- that division is always exact.  The floor of 4 keeps a W64-only loop at its
-- historical stride of 4 (2 groups of 2 lanes), so a W64-only loop's output
-- is unaffected.
--
-- Worked example, a loop writing all four integer widths: stride 16, and one
-- iteration covers the same sixteen records for each field --
--
-- >  W8 : 1 group  x 16 lanes x 1 byte  = 16 bytes
-- >  W16: 2 groups x  8 lanes x 2 bytes = 32 bytes
-- >  W32: 4 groups x  4 lanes x 4 bytes = 64 bytes
-- >  W64: 8 groups x  2 lanes x 8 bytes = 128 bytes
--
-- In every row @groups * lanes == stride@, so each cursor advances exactly
-- @stride * simdScalarBytes@ and no buffer runs ahead of another.
simdLogicalStride :: Int -> [Scalar] -> Int
simdLogicalStride _ [] = 4
simdLogicalStride regBytes scalars = max 4 (maximum (map (simdLanes regBytes) scalars))

-- | Registers of @scalar@ needed to cover one logical stride.  Exact by
-- construction: see 'simdLogicalStride'.
simdGroups :: Int -> Int -> Scalar -> Int
simdGroups regBytes stride scalar = stride `div` simdLanes regBytes scalar

-- | Does @stride@ tile every one of these scalars with whole registers?  A
-- shape that fails this is rejected rather than vectorized with a cursor that
-- would drift past live data.
simdStrideValid :: Int -> Int -> [Scalar] -> Bool
simdStrideValid regBytes stride scalars =
  all (\s -> stride `mod` simdLanes regBytes s == 0
             && simdGroups regBytes stride s >= 1) scalars

-- | Is @scalar@ eligible for the SIMD path at all?
--
-- Every scalar is, W8 and W16 included: all of them have emitted helpers.  The
-- predicate is kept as the one place a whole scalar type could be withdrawn
-- from the SIMD path, but it currently withdraws none, so what actually decides
-- whether a loop vectorizes is 'simdCapable' -- per operation, not per scalar.
simdScalarEnabled :: Scalar -> Bool
simdScalarEnabled s =
  case s of
    IntS W64 -> True
    IntS W32 -> True
    IntS W16 -> True
    IntS W8  -> True
    SymS     -> True
    FloatS   -> True
    CharS    -> True
    BoolS    -> True

-- | Is @op@ on @scalar@ a GENUINELY PACKED operation on this backend?
--
-- "Genuinely packed" means the emitted helper computes all lanes in vector
-- registers.  An operation whose only implementation would spill the register
-- to a scalar array and loop over lanes is NOT capable here: it is slower than
-- the scalar loop it replaced, and calling it SIMD would be a lie.  Such an
-- operation makes the whole candidate loop stay scalar.
--
-- Specifically for W32 at baseline SSE2:
--
--   * add\/sub\/eq are single instructions (@_mm_add_epi32@, @_mm_sub_epi32@,
--     @_mm_cmpeq_epi32@); select is three bitwise ops; broadcast\/load\/store
--     are @_mm_set1_epi32@ \/ @_mm_loadu_si128@ \/ @_mm_storeu_si128@.
--   * mul IS supported, by one of two sequences Gibbon selects from the ISA it
--     was asked for: @_mm_mullo_epi32@ at @--simd-isa=sse4.1@ or above, and at
--     baseline SSE2 two @_mm_mul_epu32@ plus shuffle\/interleave, which computes
--     the low 32 bits of each product.  The choice is made in the compiler, not
--     left to the generated translation unit's @__SSE4_1__@.
--   * div and mod are NOT: SSE2 has no packed signed integer divide, and no
--     emulation is planned.
--
-- W64 keeps its original lane-spilling mul\/div\/mod helpers.  Those are honestly documented at their
-- definitions as NOT being an acceleration; they are retained only because
-- removing them would change accepted W64 output.
-- | The capability matrix with the W64 multiply decision left open.
--
-- The W64 packed multiply is emulated rather than absent: three packed
-- 32x32->64 multiplies plus two shifts and two adds, all in registers.  It is
-- correct and it is real SIMD; it is refused by default only because seven
-- instructions for two lanes lose to one @imul@ per lane.  Passing 'True'
-- permits it, which is what measuring that loss requires.
simdCapableWith :: Bool -> VecOp -> Scalar -> Bool
simdCapableWith w64Mul op scalar
  | not (simdScalarEnabled scalar) = False
  | otherwise =
      case scalar of
        -- W64 gets data movement, add/sub and the equality-mask + select pair,
        -- and nothing else.
        --
        -- SSE2 has no packed signed 64-bit compare at all (even
        -- _mm_cmpgt_epi64 is SSE4.2), so the four ordered comparisons stay
        -- scalar; a blanket `True` would have silently claimed them.
        --
        -- MULTIPLY is excluded: at two lanes it is a LOSS, not an
        -- acceleration, and a vectorizer that emits slower code than it
        -- replaced is worse than one that declines.  The helper no longer
        -- spills -- it is three packed 32x32->64 multiplies plus two shifts
        -- and two adds -- but that is seven instructions for two lanes
        -- against one `imul` per lane scalar.  Measured on a 431-operation
        -- kernel: 1.370 instructions per source operation vectorized against
        -- 0.750 scalar, i.e. 0.55x; the vectorized loop took 2.86s where the
        -- scalar loop took 0.55s.  Widening to AVX2 does not rescue it --
        -- four lanes still cost more than four `imul`s.
        --
        -- DIVIDE and MODULUS stay, even though their helpers do spill to a
        -- scalar array and loop over lanes.  The trade is not the same one:
        -- a 64-bit integer division is tens of cycles, so the spill is noise
        -- beside it, whereas a 3-cycle multiply is entirely swamped by it.
        -- W64 is also the only integer width at which division vectorizes at
        -- all, so dropping it would leave the guarded-division machinery
        -- ('dagSpeculatesPartialOp' and the tests that pin it) exercising
        -- nothing.
        IntS W64 -> (w64Mul || op /= VecOpMul) && op `notElem` orderedCmps
        -- W32 has a packed multiply at every ISA: _mm_mullo_epi32 from SSE4.1
        -- up, and at baseline SSE2 two _mm_mul_epu32 plus shuffles, which
        -- compute the low 32 bits of all four products in registers and
        -- measured faster than the scalar loop.  Divide/modulus have no packed
        -- form at all.
        IntS W32 -> op `elem` (VecOpMul : movementAndAddSub)
        -- W16 additionally gets a GENUINE packed multiply: `_mm_mullo_epi16`
        -- is baseline SSE2 (unlike `_mm_mullo_epi32`, which is SSE4.1).
        IntS W16 -> op `elem` (VecOpMul : movementAndAddSub)
        -- W8 likewise: unpack to 16-bit lanes, _mm_mullo_epi16, mask, repack.
        IntS W8  -> op `elem` (VecOpMul : movementAndAddSub)
        SymS     -> op `elem` [VecOpBroadcast, VecOpLoad, VecOpStore, VecOpAdd, VecOpSub]
        CharS    -> op `elem` [VecOpBroadcast, VecOpLoad, VecOpStore, VecOpAdd, VecOpSub]
        BoolS    -> op `elem` [VecOpBroadcast, VecOpLoad, VecOpStore, VecOpAdd, VecOpSub]
        -- Float has _mm_cmplt_ps and friends, but this backend emits no
        -- helpers for them, so ordered float comparisons stay scalar too.
        FloatS   -> op /= VecOpMod && op `notElem` orderedCmps
  where
    -- The narrow-integer baseline: data movement, add/sub, and the
    -- equality-mask + bitwise-select pair.  Every one of these is a single
    -- packed SSE2 instruction (or three bitwise ones for select) at W32, W16
    -- and W8.  Deliberately omits VecOpDiv and VecOpMod at every narrow width
    -- -- SSE2 has no packed signed integer divide or modulus -- and omits
    -- VecOpMul except where a genuine packed multiply exists.
    movementAndAddSub = [ VecOpBroadcast, VecOpLoad, VecOpStore
                        , VecOpAdd, VecOpSub, VecOpEq, VecOpSelect ]
                        ++ orderedCmps

-- | The four ordered signed comparisons.  Available packed at W8/W16/W32 via
-- @_mm_cmpgt_epi{8,16,32}@ (plus a mask complement for <= and >=); NOT
-- available at W64 or for floats on this backend.
orderedCmps :: [VecOp]
orderedCmps = [VecOpLt, VecOpGt, VecOpLtEq, VecOpGtEq]

isIntScalar :: Scalar -> Bool
isIntScalar IntS{} = True
isIntScalar _      = False

-- | The exact width of an integer scalar.  Errors on any other scalar rather
-- than inventing a width.
intScalarWidth :: Scalar -> IntWidth
intScalarWidth (IntS w) = w
intScalarWidth s = error $ "intScalarWidth: not an integer scalar: " ++ show s

-- | 'intScalarWidth' as a total function.
intScalarWidthMaybe :: Scalar -> Maybe IntWidth
intScalarWidthMaybe (IntS w) = Just w
intScalarWidthMaybe _        = Nothing

-- | The compiler-internal 64-bit integer scalar: tags, counts, offsets and the
-- legacy paths that predate variable widths.
intS64 :: Scalar
intS64 = IntS W64


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
    -- A program integer keeps its exact width through cursorization.  This
    -- previously collapsed every width to W64, silently erasing Int8/16/32
    -- from every let binder, function type and constructor field it touched.
    IntTy w     -> IntTy w
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
    SimdTy el_ty' lanes -> SimdTy (cursorizeTy fenv mutLocsEnv oldLocsToMutEnv isTailAndOverrideModality modality el_ty') lanes
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
    LitE{}          -> ex
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
        WhileCursorEnd cur end bod ->
          Ext $ WhileCursorEnd cur end (updateAvailVars froms tos bod)
        VecBroadcast scalar lanes val ->
          Ext $ VecBroadcast scalar lanes (go val)
        VecAdd scalar lanes a b ->
          Ext $ VecAdd scalar lanes (go a) (go b)
        VecSub scalar lanes a b ->
          Ext $ VecSub scalar lanes (go a) (go b)
        VecMul scalar lanes a b ->
          Ext $ VecMul scalar lanes (go a) (go b)
        VecDiv scalar lanes a b ->
          Ext $ VecDiv scalar lanes (go a) (go b)
        VecMod scalar lanes a b ->
          Ext $ VecMod scalar lanes (go a) (go b)
        VecCmp scalar lanes c a b ->
          Ext $ VecCmp scalar lanes c (go a) (go b)
        VecSelect scalar lanes m a b ->
          Ext $ VecSelect scalar lanes (go m) (go a) (go b)
        VecStore scalar lanes ref val ->
          Ext $ VecStore scalar lanes ref (go val)
        _ -> ex
  where
    go = updateAvailVars froms tos
