{-# LANGUAGE TemplateHaskell #-}

-- | Tests for HoistBoundsCheck
module HoistBoundsCheck where

import Data.Map as M
import Data.Set as S
import Gibbon.Common hiding (FunDef)
import Gibbon.NewL2.Syntax as L2
import Gibbon.Passes.HoistBoundsCheck
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


case_t2 :: Assertion
case_t2 = expected @=? actual
  where
    actual = fst $ defaultPackedRunPassM $ hoistBoundsCheck test2 S.empty

    test2 :: L2.Exp2
    test2 =
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
                    BoundsCheckVector
                      [
                        (
                          10,
                          (Loc (LREM (singleLocVar "l1") (SingleR "r1") (SingleR "end_r1") Output)),
                          (EndOfReg (SingleR "r1") Output (SingleR "end_r1"))
                        ) , 
                        (
                          10,
                          (Loc (LREM (singleLocVar "l2") (SingleR "r2") (SingleR "end_r2") Output)),
                          (EndOfReg (SingleR "r2") Output (SingleR "end_r2"))
                        )
                      ]
                )
              $ Ext
              $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1"))
              $ Ext 
              $ LetRegionE (VarR "r2") Undefined Nothing
              $ Ext
              $ LetLocE (singleLocVar "l2") (StartOfRegionLE (VarR "r2"))
              $ (MkProdE [])
          )
          (MkProdE [])

    expected :: L2.Exp2
    expected =
      Ext
        $ LetRegionE (VarR "r2") Undefined Nothing
        $ Ext
        $ LetRegionE (VarR "r1") Undefined Nothing
        $ Ext
        $ LetLocE (singleLocVar "l1") (StartOfRegionLE (VarR "r1"))
        $ Ext 
        $ LetLocE (singleLocVar "l2") (StartOfRegionLE (VarR "r2"))
        $ LetE
          ( "_",
            [],
            MkTy2 IntTy,
            Ext $
              BoundsCheckVector 
              [
                (
                  10,
                  (Loc (LREM (singleLocVar "l1") (SingleR "r1") (SingleR "end_r1") Output)),
                  (EndOfReg (SingleR "r1") Output (SingleR "end_r1"))
                )
                ,
                (
                  10,
                  (Loc (LREM (singleLocVar "l2") (SingleR "r2") (SingleR "end_r2") Output)),
                  (EndOfReg (SingleR "r2") Output (SingleR "end_r2"))
                )
              ]
          )
        $ LetE ("b", [], MkTy2 BoolTy, LitE 1)
        $ IfE
          (VarE "b")
          (MkProdE [])
          (MkProdE [])


-- changes branch compared to test1
case_t3 :: Assertion
case_t3 = expected @=? actual
  where
    actual = fst $ defaultPackedRunPassM $ hoistBoundsCheck test3 S.empty

    test3 :: L2.Exp2
    test3 =
      LetE ("b", [], MkTy2 BoolTy, LitE 1) $
        IfE
          (VarE "b")
          (MkProdE [])
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
