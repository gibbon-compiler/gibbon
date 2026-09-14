-- | Total traversals over the expression children of an L3 extension node.
--
-- Separate from any one pass because the totality is the point: a pass that
-- needs to see every subexpression cannot afford a traversal with a wildcard.
module Gibbon.L3.Traverse
  ( extExps
  , mapExtExps
  , traverseExtExps
  ) where

import Data.Functor.Identity (Identity(..))

import Gibbon.L3.Syntax

-- | The expression children of an extension node.
--
-- Deliberately a TOTAL case with no wildcard: a traversal that silently skips a
-- form loses whatever a caller needed to see inside it -- a call left
-- un-rewritten, a variable reported dead while it is live -- and fails with no
-- diagnostic.  A new constructor must break this build.
extExps :: E3Ext () Ty3 -> [Exp3]
extExps ext =
  case ext of
    WriteScalar _ _ e -> [e]
    WriteTagPacked _ e -> [e]
    WriteCursorSelectiveIndirection _ _ _ e -> [e]
    WriteTaggedCursor _ e -> [e]
    WriteCursorMutable _ e -> [e]
    WriteList _ e _ -> [e]
    WriteVector _ e _ -> [e]
    AddCursor _ e -> [e]
    BumpCursorMutable _ e -> [e]
    AddrOfCursor e -> [e]
    RetE es -> es
    LetAvail _ e -> [e]
    ForE _ e1 e2 -> [e1, e2]
    WhileCursor _ e -> [e]
    WhileCursorEnd _ _ e -> [e]
    VecBroadcast _ _ e -> [e]
    VecAdd _ _ a b -> [a, b]
    VecSub _ _ a b -> [a, b]
    VecMul _ _ a b -> [a, b]
    VecDiv _ _ a b -> [a, b]
    VecMod _ _ a b -> [a, b]
    VecCmp _ _ _ a b -> [a, b]
    VecSelect _ _ a b c -> [a, b, c]
    VecStore _ _ _ e -> [e]
    Assert e -> [e]
    ReadScalar{} -> []
    ReadTag{} -> []
    WriteTag{} -> []
    TagCursor{} -> []
    WriteCursorIndirection{} -> []
    UnwrapSelectiveIndirections{} -> []
    MemCpy{} -> []
    ReadTaggedCursor{} -> []
    ReadCursor{} -> []
    GrowRegion{} -> []
    ReadList{} -> []
    ReadVector{} -> []
    MakeCursorArray{} -> []
    IndexCursorArray{} -> []
    DerefMutCursor{} -> []
    CastPtr{} -> []
    SubPtr{} -> []
    NewBuffer{} -> []
    ScopedBuffer{} -> []
    NewParBuffer{} -> []
    ScopedParBuffer{} -> []
    EndOfBuffer{} -> []
    MMapFileSize{} -> []
    SizeOfPacked{} -> []
    SizeOfScalar{} -> []
    BoundsCheck{} -> []
    BoundsCheckVector{} -> []
    IndirectionBarrier{} -> []
    BumpArenaRefCount{} -> []
    NullCursor -> []
    InitCursor{} -> []
    GetCilkWorkerNum -> []
    AllocateTagHere{} -> []
    AllocateScalarsHere{} -> []
    StartTagAllocation{} -> []
    EndTagAllocation{} -> []
    StartScalarsAllocation{} -> []
    EndScalarsAllocation{} -> []
    ScalarCountBump{} -> []
    ScalarCountBind{} -> []
    ScalarCountFinalize{} -> []
    ScalarCountSet{} -> []
    ScalarCountCopyAll{} -> []
    ReadScalarCount{} -> []
    ReadScalarCountFirstFooter{} -> []
    ReadScalarCountNextFooter{} -> []
    VecLoad{} -> []
    SSPush{} -> []
    SSPop{} -> []

-- | Rebuild an extension node with its expression children mapped.  Kept
-- beside 'extExps' so the two cannot drift.
mapExtExps :: (Exp3 -> Exp3) -> E3Ext () Ty3 -> E3Ext () Ty3
mapExtExps f ext = runIdentity (traverseExtExps (Identity . f) ext)

traverseExtExps
  :: Applicative m => (Exp3 -> m Exp3) -> E3Ext () Ty3 -> m (E3Ext () Ty3)
traverseExtExps f ext =
  case ext of
    WriteScalar s v e -> WriteScalar s v <$> f e
    WriteTagPacked v e -> WriteTagPacked v <$> f e
    WriteCursorSelectiveIndirection a b c e -> WriteCursorSelectiveIndirection a b c <$> f e
    WriteTaggedCursor v e -> WriteTaggedCursor v <$> f e
    WriteCursorMutable v e -> WriteCursorMutable v <$> f e
    WriteList v e t -> (\e' -> WriteList v e' t) <$> f e
    WriteVector v e t -> (\e' -> WriteVector v e' t) <$> f e
    AddCursor v e -> AddCursor v <$> f e
    BumpCursorMutable v e -> BumpCursorMutable v <$> f e
    AddrOfCursor e -> AddrOfCursor <$> f e
    RetE es -> RetE <$> traverse f es
    LetAvail vs e -> LetAvail vs <$> f e
    ForE v e1 e2 -> ForE v <$> f e1 <*> f e2
    WhileCursor v e -> WhileCursor v <$> f e
    WhileCursorEnd v w e -> WhileCursorEnd v w <$> f e
    VecBroadcast s n e -> VecBroadcast s n <$> f e
    VecAdd s n a b -> VecAdd s n <$> f a <*> f b
    VecSub s n a b -> VecSub s n <$> f a <*> f b
    VecMul s n a b -> VecMul s n <$> f a <*> f b
    VecDiv s n a b -> VecDiv s n <$> f a <*> f b
    VecMod s n a b -> VecMod s n <$> f a <*> f b
    VecCmp s n o a b -> VecCmp s n o <$> f a <*> f b
    VecSelect s n a b c -> VecSelect s n <$> f a <*> f b <*> f c
    VecStore s n v e -> VecStore s n v <$> f e
    Assert e -> Assert <$> f e
    ReadScalar{} -> pure ext
    ReadTag{} -> pure ext
    WriteTag{} -> pure ext
    TagCursor{} -> pure ext
    WriteCursorIndirection{} -> pure ext
    UnwrapSelectiveIndirections{} -> pure ext
    MemCpy{} -> pure ext
    ReadTaggedCursor{} -> pure ext
    ReadCursor{} -> pure ext
    GrowRegion{} -> pure ext
    ReadList{} -> pure ext
    ReadVector{} -> pure ext
    MakeCursorArray{} -> pure ext
    IndexCursorArray{} -> pure ext
    DerefMutCursor{} -> pure ext
    CastPtr{} -> pure ext
    SubPtr{} -> pure ext
    NewBuffer{} -> pure ext
    ScopedBuffer{} -> pure ext
    NewParBuffer{} -> pure ext
    ScopedParBuffer{} -> pure ext
    EndOfBuffer{} -> pure ext
    MMapFileSize{} -> pure ext
    SizeOfPacked{} -> pure ext
    SizeOfScalar{} -> pure ext
    BoundsCheck{} -> pure ext
    BoundsCheckVector{} -> pure ext
    IndirectionBarrier{} -> pure ext
    BumpArenaRefCount{} -> pure ext
    NullCursor -> pure ext
    InitCursor{} -> pure ext
    GetCilkWorkerNum -> pure ext
    AllocateTagHere{} -> pure ext
    AllocateScalarsHere{} -> pure ext
    StartTagAllocation{} -> pure ext
    EndTagAllocation{} -> pure ext
    StartScalarsAllocation{} -> pure ext
    EndScalarsAllocation{} -> pure ext
    ScalarCountBump{} -> pure ext
    ScalarCountBind{} -> pure ext
    ScalarCountFinalize{} -> pure ext
    ScalarCountSet{} -> pure ext
    ScalarCountCopyAll{} -> pure ext
    ReadScalarCount{} -> pure ext
    ReadScalarCountFirstFooter{} -> pure ext
    ReadScalarCountNextFooter{} -> pure ext
    VecLoad{} -> pure ext
    SSPush{} -> pure ext
    SSPop{} -> pure ext
