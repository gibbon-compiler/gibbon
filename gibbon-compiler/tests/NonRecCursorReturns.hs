{-# LANGUAGE TemplateHaskell #-}

-- | Tests for eliding end-of-input-region cursors from the returns of
-- non-recursive SoA readers (@--opt-mutable-cursors-nonrec@).
module NonRecCursorReturns (nonRecCursorReturnsTests) where

import Control.Exception (ErrorCall (..), evaluate, try)
import Data.List (isInfixOf)
import qualified Data.Map as M
import qualified Data.Set as S
import Gibbon.Common hiding (FunDef)
import Gibbon.L2.Syntax as OldL2 hiding (Ty2, FunDef2, FunDefs2, Exp2)
import Gibbon.NewL2.Syntax as L2
import Gibbon.Passes.Cursorize (dropInRegEndsFromRetE, markSpawnTargets)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

-- A two-field SoA location and its region.
soaLoc :: String -> LocVar
soaLoc n = SoA (toVar n) [(("Node", 0), Single (toVar (n ++ "_f0")))]

soaReg :: String -> Region
soaReg n = SoAR (VarR (toVar n)) [(("Node", 0), VarR (toVar (n ++ "_f0")))]

soaRegVar :: String -> RegVar
soaRegVar n = SoARv (SingleR (toVar n)) [(("Node", 0), SingleR (toVar (n ++ "_f0")))]

inLRM :: LRM
inLRM = LRM (soaLoc "l") (soaReg "r") Input

-- | @T -> Int@ over one SoA input: the shape of an accessor like @massOf@.
readerTy :: ArrowTy2 Ty2
readerTy =
  ArrowTy2
    { locVars = [inLRM]
    , arrIns = [MkTy2 (PackedTy "T" (soaLoc "l"))]
    , arrEffs = S.empty
    , arrOut = MkTy2 (IntTy W64)
    , locRets = []
    , hasParallelism = False
    }

nonRec :: FunMeta
nonRec = FunMeta NotRec NoInline False [] Nothing

elides :: FunMeta -> ArrowTy2 Ty2 -> Bool
elides = elidesInRegEnds True True

case_pure_soa_reader_elides :: Assertion
case_pure_soa_reader_elides = elides nonRec readerTy @?= True

case_flag_off :: Assertion
case_flag_off = elidesInRegEnds False True nonRec readerTy @?= False

case_recursive_uses_mutable_convention :: Assertion
case_recursive_uses_mutable_convention = elides nonRec {funRec = Rec} readerTy @?= False

case_packed_output :: Assertion
case_packed_output =
  elides nonRec readerTy {arrOut = MkTy2 (ProdTy [IntTy W64, PackedTy "T" (soaLoc "l")])} @?= False

case_end_of_input_witness_returned :: Assertion
case_end_of_input_witness_returned = elides nonRec readerTy {locRets = [EndOf inLRM]} @?= False

case_non_input_location :: Assertion
case_non_input_location =
  elides nonRec readerTy {locVars = [LRM (soaLoc "l") (soaReg "r") InputMutable]} @?= False

-- Two input locations in one region: two end-of-region cursors formals, one region.
case_region_count_mismatch :: Assertion
case_region_count_mismatch =
  elides nonRec readerTy
    { locVars = [inLRM, LRM (soaLoc "l2") (soaReg "r") Input]
    , arrIns = [MkTy2 (PackedTy "T" (soaLoc "l")), MkTy2 (PackedTy "T" (soaLoc "l2"))]
    }
    @?= False

case_aos_reader :: Assertion
case_aos_reader =
  elides nonRec readerTy
    { locVars = [LRM (Single "l") (VarR "r") Input]
    , arrIns = [MkTy2 (PackedTy "T" (Single "l"))]
    }
    @?= False

case_spawn_target :: Assertion
case_spawn_target = elides nonRec {funOpt = [SpawnTarget]} readerTy @?= False

-- markSpawnTargets finds a spawn in main, including one under a location binding.
case_mark_spawn_targets :: Assertion
case_mark_spawn_targets = do
  let fd n = FunDef (toVar n) [] readerTy (VarE "x") nonRec
      fundefs = M.fromList [(toVar "valOf", fd "valOf"), (toVar "other", fd "other")]
      mainE =
        Ext $ LetLocE (Loc (LREM (Single "m") (SingleR "rm") (SingleR "end_rm") Output)) (StartOfRegionLE (VarR "rm")) $
          LetE ("x", [], MkTy2 (IntTy W64), SpawnE (toVar "valOf") [] []) (VarE "x")
      marked = markSpawnTargets fundefs (Just (mainE, MkTy2 (IntTy W64)))
      optsOf n = funOpt (funMeta (marked M.! toVar n))
  optsOf "valOf" @?= [SpawnTarget]
  optsOf "other" @?= []

inEnd :: LocArg
inEnd = EndOfReg (soaRegVar "r") Input (soaRegVar "end_r")

case_drop_strips_input_region_ends :: Assertion
case_drop_strips_input_region_ends = dropInRegEndsFromRetE "f" body @?= expected
  where
    body =
      CaseE (VarE "t")
        [ ("Leaf", [], Ext (RetE [inEnd] "a"))
        , ("Node", [], LetE ("b", [], MkTy2 (IntTy W64), VarE "a") (Ext (RetE [inEnd] "b")))
        ]
    expected =
      CaseE (VarE "t")
        [ ("Leaf", [], Ext (RetE [] "a"))
        , ("Node", [], LetE ("b", [], MkTy2 (IntTy W64), VarE "a") (Ext (RetE [] "b")))
        ]

dropErrors :: LocArg -> Assertion
dropErrors other = do
  r <- try (evaluate (length (show (dropInRegEndsFromRetE "f" (Ext (RetE [inEnd, other] "a"))))))
  case r of
    Left (ErrorCallWithLocation msg _) ->
      assertBool ("unexpected message: " ++ msg) ("returns more than its end-of-input-region cursors" `isInfixOf` msg)
    Right _ -> assertFailure "expected dropInRegEndsFromRetE to reject a non-input-region-end return"

case_drop_rejects_output_region_end :: Assertion
case_drop_rejects_output_region_end = dropErrors (EndOfReg (soaRegVar "o") Output (soaRegVar "end_o"))

case_drop_rejects_end_witness :: Assertion
case_drop_rejects_end_witness =
  dropErrors (EndWitness (LREM (soaLoc "l") (soaRegVar "r") (soaRegVar "end_r") Input) (Single "w"))

nonRecCursorReturnsTests :: TestTree
nonRecCursorReturnsTests = $(testGroupGenerator)
