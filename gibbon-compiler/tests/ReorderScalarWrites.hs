{-# LANGUAGE TemplateHaskell #-}

-- | VW-31: what 'Gibbon.Passes.ReorderScalarWrites' may and may not lift.
--
-- The pass moves a constructor's tag and scalar writes back to the
-- @AllocateTagHere@ / @AllocateScalarsHere@ marker, so that they land before
-- any packed field written into the same node.  The marker sits on the
-- straight-line path, and the pass DROPS what it lifts from where it was, so a
-- bind may only be lifted if it executes on every path through that marker.
--
-- It used to lift from both arms of a conditional and concatenate the results.
-- Two mutually exclusive constructor writes then became two unconditional
-- writes to the same cursor, in sequence, and the second one won -- a silent
-- miscompilation at plain @--packed@, in both layouts.  See
-- Note [A hoisted write must be control-independent] in that module.
--
-- These tests drive the real pass over hand-built L3 in exactly the shape
-- Cursorize emits, so both the refusal and the reordering it must still
-- perform are pinned.
module ReorderScalarWrites
  ( reorderScalarWritesTests
  ) where

import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language
import Gibbon.L3.Syntax
import Gibbon.Passes.ReorderScalarWrites ( reorderScalarWrites )

--------------------------------------------------------------------------------
-- Fixtures

-- | The marker-delimited write group Cursorize emits for one constructor.
tagGroup :: String -> DataCon -> [(Var, [()], Ty3, Exp3)]
tagGroup nm dcon =
  [ (toVar (nm ++ "_start"), [], ProdTy [], Ext $ StartTagAllocation "loc")
  , (toVar (nm ++ "_tag"),   [], CursorTy,  Ext $ WriteTag dcon "loc")
  , (toVar (nm ++ "_end"),   [], ProdTy [], Ext $ EndTagAllocation "loc")
  ]

-- | @AllocateTagHere loc; <recursive call>; if c then <write A> else <write B>@
-- -- the shape a let-bound packed tail consumed by two constructor
-- alternatives produces.
sharedTailBody :: Exp3
sharedTailBody =
  mkLets
    ( [ ("alloc", [], ProdTy [], Ext $ AllocateTagHere "loc" "T")
      , ("rst",   [], CursorTy,  AppE "mkT" NotTailRec [] [VarE "n"])
      , ("cond",  [], BoolTy,    PrimAppE ltP64 [VarE "n", mkLitE64 3])
      , ("branch",[], ProdTy [],
          IfE (VarE "cond")
              (mkLets (tagGroup "a" "A") (MkProdE []))
              (mkLets (tagGroup "b" "B") (MkProdE [])))
      ])
    (MkProdE [])

-- | The one-constructor shape: marker, then the write, on one straight line.
-- This is what the pass exists to reorder and must keep doing.
straightLineBody :: Exp3
straightLineBody =
  mkLets
    ( [ ("alloc", [], ProdTy [], Ext $ AllocateTagHere "loc" "T") ]
      ++ tagGroup "a" "A"
      ++ [ ("rst", [], CursorTy, AppE "mkT" NotTailRec [] [VarE "n"]) ])
    (MkProdE [])

runPass :: Exp3 -> Exp3
runPass body =
    funBody (fds M.! "probe")
  where
    fn  = FunDef "probe" ["n"] ([IntTy W64], ProdTy []) body
                 (FunMeta Rec NoInline False [] Nothing)
    prg = Prog M.empty (M.fromList [("probe", fn)]) Nothing
    Prog{fundefs = fds} = fst (defaultPackedRunPassM (reorderScalarWrites prg))

--------------------------------------------------------------------------------
-- Counting

countWriteTags :: Exp3 -> Int
countWriteTags = go
  where
    go ex =
      case ex of
        Ext (WriteTag _ _) -> 1
        LetE (_,_,_,rhs) bod -> go rhs + go bod
        IfE a b c -> go a + go b + go c
        CaseE scrt brs -> go scrt + sum [ go r | (_,_,r) <- brs ]
        MkProdE ls -> sum (map go ls)
        ProjE _ e -> go e
        PrimAppE _ args -> sum (map go args)
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        Ext (LetAvail _ bod) -> go bod
        _ -> 0

-- | Tag writes reachable WITHOUT entering a conditional -- i.e. on the
-- straight-line spine from the top of the body.
countWriteTagsOnSpine :: Exp3 -> Int
countWriteTagsOnSpine ex =
  case ex of
    LetE (_,_,_,rhs) bod ->
      (case rhs of Ext (WriteTag _ _) -> 1; _ -> 0) + countWriteTagsOnSpine bod
    _ -> 0

-- | The two arms of the first conditional found on the spine.
armsOfFirstIf :: Exp3 -> Maybe (Exp3, Exp3)
armsOfFirstIf ex =
  case ex of
    LetE (_,_,_,IfE _ b c) _ -> Just (b,c)
    LetE (_,_,_,_) bod -> armsOfFirstIf bod
    IfE _ b c -> Just (b,c)
    _ -> Nothing

--------------------------------------------------------------------------------
-- Tests

-- | The regression.  Neither arm's tag write may end up on the spine, and
-- neither may be duplicated.
case_vw31_conditional_tag_writes_are_not_lifted :: Assertion
case_vw31_conditional_tag_writes_are_not_lifted = do
  let body = runPass sharedTailBody
  assertEqual "control: the fixture has two tag writes to begin with"
              2 (countWriteTags sharedTailBody)
  assertEqual "no tag write may be lifted out of a conditional arm"
              0 (countWriteTagsOnSpine body)
  assertEqual "and none may be duplicated or dropped"
              2 (countWriteTags body)

case_vw31_each_arm_keeps_exactly_its_own_tag_write :: Assertion
case_vw31_each_arm_keeps_exactly_its_own_tag_write =
  case armsOfFirstIf (runPass sharedTailBody) of
    Nothing -> assertFailure "the conditional itself was lost"
    Just (b,c) -> do
      assertEqual "then-arm writes exactly one tag" 1 (countWriteTags b)
      assertEqual "else-arm writes exactly one tag" 1 (countWriteTags c)

-- | The other half: refusing to lift across a join must not become refusing to
-- lift at all.  With one constructor and no conditional, the write still moves
-- to the marker, ahead of the packed field written after it.
case_vw31_straight_line_write_is_still_reordered :: Assertion
case_vw31_straight_line_write_is_still_reordered = do
  let body = runPass straightLineBody
  assertEqual "the single tag write survives" 1 (countWriteTags body)
  assertEqual "and it is on the spine, at the marker" 1 (countWriteTagsOnSpine body)
  assertBool "the allocation marker itself is consumed"
             (not (mentionsAllocateTagHere body))
  where
    mentionsAllocateTagHere ex =
      case ex of
        LetE (_,_,_,Ext AllocateTagHere{}) _ -> True
        LetE (_,_,_,_) bod -> mentionsAllocateTagHere bod
        _ -> False

--------------------------------------------------------------------------------

reorderScalarWritesTests :: TestTree
reorderScalarWritesTests = $(testGroupGenerator)
