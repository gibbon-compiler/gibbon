{-# LANGUAGE TemplateHaskell #-}

-- | Tests for HoistBoundsCheck
module HoistBoundsCheck where

import Data.Map as M
import Data.Set as S
import Gibbon.Common hiding (FunDef)
import Gibbon.NewL2.Syntax as L2
import Gibbon.Passes.HoistExpressions
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

case_t1 :: Assertion
case_t1 = expected @=? actual
  where
    actual = fst $ defaultPackedRunPassM $ hoistBoundsCheck test1 S.empty

    test1 :: L2.Exp2
    test1 =
      LetE ("b", [], MkTy2 BoolTy, LitE 1) $
        IfE
          (VarE "b")
          ( Ext
              $ LetRegionE (VarR "r1") Undefined Nothing
              $ LetE
                ( "_",
                  [],
                  MkTy2 IntTy,
                  Ext $
                    BoundsCheck
                      10
                      (Loc (LREM (singleLocVar "l1") (SingleR "r1") (SingleR "end_r1") Output))
                      (EndOfReg (SingleR "r1") Output (SingleR "end_r1"))
                )
              $ Ext
              $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1"))
              $ (MkProdE [])
          )
          (MkProdE [])

    expected :: L2.Exp2
    expected =
      Ext
        $ LetRegionE (VarR "r1") Undefined Nothing
        $ Ext
        $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1"))
        $ LetE
          ( "_",
            [],
            MkTy2 IntTy,
            Ext $
              BoundsCheck
                10
                (Loc (LREM (singleLocVar "l1") (SingleR "r1") (SingleR "end_r1") Output))
                (EndOfReg (SingleR "r1") Output (SingleR "end_r1"))
          )
        $ LetE ("b", [], MkTy2 BoolTy, LitE 1)
        $ IfE
          (VarE "b")
          (MkProdE [])
          (MkProdE [])

hoistBoundsCheckTests :: TestTree
hoistBoundsCheckTests = $(testGroupGenerator)
