{-# LANGUAGE TemplateHaskell #-}

-- | Tests for 'Gibbon.L3.Traverse'.
--
-- 'extExps' and 'traverseExtExps' enumerate the same children by hand in two
-- separate cases, so the only thing holding them together is a test.
module L3Traverse (l3TraverseTests) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Functor.Const (Const(..))
import Data.Monoid (Sum(..))
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common (SSModality(..), toVar)
import Gibbon.Language.Syntax (mkLitE64)
import qualified Gibbon.L2.Syntax as L2
import Gibbon.L3.Syntax
import Gibbon.L3.Traverse

child1, child2, child3 :: Exp3
child1 = mkLitE64 1
child2 = mkLitE64 2
child3 = mkLitE64 3

-- | Extension nodes spanning every child arity 'extExps' distinguishes.
samples :: [(String, E3Ext () Ty3)]
samples =
  [ ("ReadScalar", ReadScalar (IntS W64) (toVar "c"))
  , ("NullCursor", NullCursor)
  , ("MakeCursorArray", MakeCursorArray 3 [toVar "a", toVar "b", toVar "c"])
  , ("BoundsCheck", BoundsCheck 18 (toVar "r") (toVar "c") Nothing L2.Output)
  , ("WriteScalar", WriteScalar (IntS W64) (toVar "c") child1)
  , ("AddrOfCursor", AddrOfCursor child1)
  , ("Assert", Assert child1)
  , ("WriteList", WriteList (toVar "v") child1 (IntTy W64))
  , ("ForE", ForE (toVar "i") child1 child2)
  , ("VecAdd", VecAdd (IntS W64) 4 child1 child2)
  , ("VecSelect", VecSelect (IntS W64) 4 child1 child2 child3)
  , ("RetE", RetE [child1, child2, child3])
  ]

-- | How many children 'traverseExtExps' visits.
visited :: E3Ext () Ty3 -> Int
visited ext = getSum (getConst (traverseExtExps (\_ -> Const (Sum 1)) ext))

case_extExps_and_traverseExtExps_agree :: Assertion
case_extExps_and_traverseExtExps_agree =
  mapM_ check samples
  where
    check (name, ext) =
      assertEqual (name ++ ": extExps and traverseExtExps disagree on child count")
                  (length (extExps ext)) (visited ext)

case_mapExtExps_id_is_id :: Assertion
case_mapExtExps_id_is_id =
  mapM_ (\(name, ext) -> assertEqual name ext (mapExtExps id ext)) samples

case_mapExtExps_rewrites_every_child :: Assertion
case_mapExtExps_rewrites_every_child =
  mapM_ check samples
  where
    marker = mkLitE64 99
    check (name, ext) =
      assertEqual (name ++ ": a child survived mapExtExps")
                  (replicate (length (extExps ext)) marker)
                  (extExps (mapExtExps (const marker) ext))

-- 'extExps' reports expression children, not variables.  A node whose operands
-- are all 'Var' fields has no children, which is why liveness cannot be built
-- on a child traversal alone.
case_var_only_nodes_have_no_children :: Assertion
case_var_only_nodes_have_no_children = do
  [] @=? extExps (BoundsCheck 18 (toVar "r") (toVar "c") Nothing L2.Output)
  [] @=? extExps (MakeCursorArray 3 [toVar "a", toVar "b", toVar "c"])
  [] @=? extExps (ReadScalar (IntS W64) (toVar "c"))

l3TraverseTests :: TestTree
l3TraverseTests = $(testGroupGenerator)
-- mtl is already a build-depend of test-gibbon.

-- | Replace the i-th child `traverseExtExps` visits with the literal i.
--
-- 'State' sequences '<*>' left to right, so the result pins the ORDER
-- 'traverseExtExps' visits children in, not just how many there are.  Comparing
-- against 'extExps' of the rewritten node therefore catches a positional or
-- ordering disagreement between the two hand-written enumerations, which the
-- count-only test cannot.
numberChildren :: E3Ext () Ty3 -> E3Ext () Ty3
numberChildren ext = evalState (traverseExtExps step ext) 0
  where
    step :: Exp3 -> State Int Exp3
    step _ = do { n <- get; put (n + 1); pure (mkLitE64 (fromIntegral n)) }

-- | Every E3Ext constructor, in the order 'extExps' lists them.  Children are
-- distinct so a swap is visible.
allNodes :: [(String, E3Ext () Ty3)]
allNodes =
  [ ("WriteScalar", WriteScalar (IntS W64) c1 (VarE x1))
  , ("WriteTagPacked", WriteTagPacked c1 (VarE x1))
  , ("WriteCursorSelectiveIndirection", WriteCursorSelectiveIndirection c1 c2 c3 (VarE x1))
  , ("WriteTaggedCursor", WriteTaggedCursor c1 (VarE x1))
  , ("WriteCursorMutable", WriteCursorMutable c1 (VarE x1))
  , ("WriteList", WriteList c1 (VarE x1) (IntTy W64))
  , ("WriteVector", WriteVector c1 (VarE x1) (IntTy W64))
  , ("AddCursor", AddCursor c1 (VarE x1))
  , ("BumpCursorMutable", BumpCursorMutable c1 (VarE x1))
  , ("AddrOfCursor", AddrOfCursor (VarE x1))
  , ("RetE", RetE [VarE x1, VarE x2, VarE x3])
  , ("LetAvail", LetAvail [c1] (VarE x1))
  , ("ForE", ForE c1 (VarE x1) (VarE x2))
  , ("WhileCursor", WhileCursor c1 (VarE x1))
  , ("WhileCursorEnd", WhileCursorEnd c1 c2 (VarE x1))
  , ("VecBroadcast", VecBroadcast (IntS W64) 4 (VarE x1))
  , ("VecAdd", VecAdd (IntS W64) 4 (VarE x1) (VarE x2))
  , ("VecSub", VecSub (IntS W64) 4 (VarE x1) (VarE x2))
  , ("VecMul", VecMul (IntS W64) 4 (VarE x1) (VarE x2))
  , ("VecDiv", VecDiv (IntS W64) 4 (VarE x1) (VarE x2))
  , ("VecMod", VecMod (IntS W64) 4 (VarE x1) (VarE x2))
  , ("VecCmp", VecCmp (IntS W64) 4 VecCmpEq (VarE x1) (VarE x2))
  , ("VecSelect", VecSelect (IntS W64) 4 (VarE x1) (VarE x2) (VarE x3))
  , ("VecStore", VecStore (IntS W64) 4 c1 (VarE x1))
  , ("Assert", Assert (VarE x1))
  -- Childless forms: every remaining constructor.
  , ("ReadScalar", ReadScalar (IntS W64) c1)
  , ("ReadTag", ReadTag c1)
  , ("WriteTag", WriteTag "Node" c1)
  , ("TagCursor", TagCursor c1 c2)
  , ("WriteCursorIndirection", WriteCursorIndirection c1 c2 c3)
  , ("UnwrapSelectiveIndirections", UnwrapSelectiveIndirections 3 c1 c2)
  , ("MemCpy", MemCpy c1 c2 (IntTy W64))
  , ("ReadTaggedCursor", ReadTaggedCursor c1)
  , ("ReadCursor", ReadCursor c1)
  , ("GrowRegion", GrowRegion c1 c2)
  , ("ReadList", ReadList c1 (IntTy W64))
  , ("ReadVector", ReadVector c1 (IntTy W64))
  , ("MakeCursorArray", MakeCursorArray 2 [c1, c2])
  , ("IndexCursorArray", IndexCursorArray c1 1)
  , ("DerefMutCursor", DerefMutCursor c1)
  , ("CastPtr", CastPtr c1 CursorTy)
  , ("SubPtr", SubPtr c1 c2)
  , ("NewBuffer", NewBuffer L2.Infinite L2.RegionImmutable)
  , ("ScopedBuffer", ScopedBuffer L2.Infinite)
  , ("NewParBuffer", NewParBuffer L2.Infinite)
  , ("ScopedParBuffer", ScopedParBuffer L2.Infinite)
  , ("EndOfBuffer", EndOfBuffer L2.Infinite L2.RegionImmutable)
  , ("MMapFileSize", MMapFileSize c1)
  , ("SizeOfPacked", SizeOfPacked c1 c2)
  , ("SizeOfScalar", SizeOfScalar c1)
  , ("BoundsCheck", BoundsCheck 18 c1 c2 Nothing L2.Output)
  , ("BoundsCheckVector", BoundsCheckVector [(18, c1, c2, (c3, c1))])
  , ("IndirectionBarrier", IndirectionBarrier "Tree" (c1, c2, c3, c1))
  , ("BumpArenaRefCount", BumpArenaRefCount c1 c2)
  , ("NullCursor", NullCursor)
  , ("InitCursor", InitCursor CursorTy)
  , ("GetCilkWorkerNum", GetCilkWorkerNum)
  , ("AllocateTagHere", AllocateTagHere c1 "Tree")
  , ("AllocateScalarsHere", AllocateScalarsHere c1)
  , ("StartTagAllocation", StartTagAllocation c1)
  , ("EndTagAllocation", EndTagAllocation c1)
  , ("StartScalarsAllocation", StartScalarsAllocation c1)
  , ("EndScalarsAllocation", EndScalarsAllocation c1)
  , ("ScalarCountBump", ScalarCountBump "Node" [(c1, 0)])
  , ("ScalarCountBind", ScalarCountBind 0 2 c1)
  , ("ScalarCountFinalize", ScalarCountFinalize 0 2 c1)
  , ("ScalarCountSet", ScalarCountSet c1 c2)
  , ("ScalarCountCopyAll", ScalarCountCopyAll 2 c1 c2)
  , ("ReadScalarCount", ReadScalarCount c1)
  , ("ReadScalarCountFirstFooter", ReadScalarCountFirstFooter c1)
  , ("ReadScalarCountNextFooter", ReadScalarCountNextFooter c1)
  , ("VecLoad", VecLoad (IntS W64) 4 c1)
  , ("SSPush", SSPush Write c1 c2 "Tree")
  , ("SSPop", SSPop Write c1 c2)
  ]
  where
    c1 = toVar "c1"; c2 = toVar "c2"; c3 = toVar "c3"
    x1 = toVar "x1"; x2 = toVar "x2"; x3 = toVar "x3"

-- Keep in step with the number of E3Ext constructors in Gibbon.L3.Syntax.
case_every_ext_constructor_is_listed :: Assertion
case_every_ext_constructor_is_listed = 74 @=? length allNodes

-- The real hazard: two hand-written enumerations agreeing on counts but not on
-- WHICH child, or in what order.
case_extExps_and_traverseExtExps_agree_positionally :: Assertion
case_extExps_and_traverseExtExps_agree_positionally = mapM_ check allNodes
  where
    check (name, ext) =
      let n = length (extExps ext)
      in assertEqual (name ++ ": extExps and traverseExtExps disagree on which children, or on order")
                     (map (mkLitE64 . fromIntegral) [0 .. n - 1])
                     (extExps (numberChildren ext))

-- mapExtExps must not touch anything but the children.
case_mapExtExps_preserves_everything_else :: Assertion
case_mapExtExps_preserves_everything_else = mapM_ check allNodes
  where
    check (name, ext) = assertEqual (name ++ ": mapExtExps id changed the node") ext (mapExtExps id ext)

