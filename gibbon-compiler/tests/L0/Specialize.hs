{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Tests for the L0 specializer
module L0.Specialize where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Control.Monad.Except
import Data.Loc
import Data.Map as M
import Data.Set as S

import Gibbon.Common 
import Gibbon.L0.Syntax as L0
import Gibbon.L1.Syntax as L1 hiding (FunDef(..), FunDefs)
import Gibbon.L0.Specialize

type Exp = L Exp0

-- |
assertValue :: CurFun -> CCall -> (L0Fun, FCall) -> Assertion
assertValue f call expected = let actual = tester f call
                              in expected @=? actual


tester :: CurFun -> CCall -> (L0Fun, FCall)
tester f c = let (newf, newc) = specialize f c in (newf, newc $ c)

specializeTests :: TestTree
specializeTests = $(testGroupGenerator)

--------------------------------------------------------------------------------

-- function f \ x -> x of type Int -> Int
t1Fun :: CurFun
t1Fun = VarDef (toVar "f") (ArrowTy L0.IntTy L0.IntTy) (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy) $ l $ VarE $ toVar "x")

-- call (f 3)
t1Call :: CCall
t1Call = l $ Ext $ PolyAppE (l $ VarE (toVar "f")) (l $ LitE 3)

t1Ex :: (L0Fun, FCall)
t1Ex = (FunDef (toVar "f1") (toVar "x") (L0.ProdTy [], L0.IntTy) (l $ LitE 3), l $ AppE (toVar "f1") [] $ l$ MkProdE [])

case_t1 :: Assertion
case_t1 = assertValue t1Fun t1Call t1Ex

-- function f1 \ (f) (x) (y) -> (+ (f x) y)
t2Fun :: CurFun
t2Fun = VarDef (toVar "f1") (ArrowTy (ArrowTy L0.IntTy L0.IntTy) (ArrowTy L0.IntTy (ArrowTy L0.IntTy L0.IntTy)))
        (l $ Ext $ LambdaE ((toVar "f"), ArrowTy L0.IntTy L0.IntTy) 
          (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy)
            (l $ Ext $ LambdaE ((toVar "y"), L0.IntTy)
               (l $ PrimAppE AddP [(l $ Ext $ PolyAppE (l $ VarE $ toVar "f") (l $ VarE $ toVar "x")),
                                   (l $ VarE $ toVar "y")]))))

-- call (f1 (\ x -> x) 4 6)
t2Call :: CCall
t2Call = (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ VarE $ toVar "f1") (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy)
                                                                                                         (l $ VarE $ toVar "x")))
                                                 (l $ LitE 4))
                             (l $ LitE 6))
           

t2Ex :: (L0Fun, FCall)
t2Ex = (FunDef (toVar "f11") (toVar "x") (L0.ProdTy [], L0.IntTy) (l $ PrimAppE AddP [(l $ LitE 4),(l $ LitE 6)]),
        l $ AppE (toVar "f11") [] $ l$ MkProdE [])
  
case_t2 :: Assertion
case_t2 = assertValue t2Fun t2Call t2Ex

-- function f1 \ (f) (x) (y) -> (+ (f x) y)
t3Fun :: CurFun
t3Fun = VarDef (toVar "f1") (ArrowTy (ArrowTy L0.IntTy L0.IntTy) (ArrowTy L0.IntTy (ArrowTy L0.IntTy L0.IntTy)))
        (l $ Ext $ LambdaE ((toVar "f"), ArrowTy L0.IntTy L0.IntTy)
          (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy)
            (l $ Ext $ LambdaE ((toVar "y"), L0.IntTy)
               (l $ PrimAppE AddP [(l $ Ext $ PolyAppE (l $ VarE $ toVar "f") (l $ VarE $ toVar "x")),
                                   (l $ VarE $ toVar "y")]))))

-- call (f1 (\ x -> (+ x x)) 4 6)
t3Call :: CCall
t3Call = (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ VarE $ toVar "f1")
                                                                     (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy)
                                                                                (l $ PrimAppE AddP [(l $ VarE $ toVar "x"),
                                                                                                    (l $ VarE $ toVar "x")])))
                                                 (l $ LitE 4))
                             (l $ LitE 6))
           

t3Ex :: (L0Fun, FCall)
t3Ex = (FunDef (toVar "f11") (toVar "x") (L0.ProdTy [], L0.IntTy) (l $ PrimAppE AddP [(l $ PrimAppE AddP [(l $ LitE 4), (l $ LitE 4)]),(l $ LitE 6)]),
        l $ AppE (toVar "f11") [] $ l$ MkProdE [])
  
case_t3 :: Assertion
case_t3 = assertValue t3Fun t3Call t3Ex

-- function f1 \ (x) (f) (y) -> (+ (f x) y)
t4Fun :: CurFun
t4Fun = VarDef (toVar "f1") (ArrowTy L0.BoolTy (ArrowTy (ArrowTy L0.BoolTy L0.IntTy) (ArrowTy L0.IntTy L0.IntTy)))
        (l $ Ext $ LambdaE ((toVar "x"), L0.BoolTy)
          (l $ Ext $ LambdaE ((toVar "f"), ArrowTy L0.BoolTy L0.IntTy)
            (l $ Ext $ LambdaE ((toVar "y"), L0.IntTy)
               (l $ PrimAppE AddP [(l $ Ext $ PolyAppE (l $ VarE $ toVar "f") (l $ VarE $ toVar "x")),
                                   (l $ VarE $ toVar "y")]))))

-- call (f1 y (\ x -> (if x 2 4)) z) -- specialize on lambda
t4Call :: CCall
t4Call = (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ VarE $ toVar "f1")
                                                                     (l $ VarE $ toVar "y"))
                                                 (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy)
                                                   (l $ IfE (l $ VarE $ toVar "x")
                                                            (l $ LitE 2)
                                                            (l $ LitE 4))))
                             (l $ VarE $ toVar "z"))
           

t4Ex :: (L0Fun, FCall)
t4Ex = (FunDef (toVar "f11") (toVar "x") (L0.ProdTy [L0.BoolTy , L0.IntTy], L0.IntTy)
        (l $ PrimAppE AddP [(l $ IfE (l $ ProjE 0 $ l$ VarE $ toVar "x") (l $ LitE 2) (l $ LitE 4)),(l $ ProjE 1 $ l$ VarE $ toVar "x")]),
        l $ AppE (toVar "f11") [] $ l$ MkProdE [(l $ VarE $ toVar "y") , (l $ VarE $ toVar "z")])
  
case_t4 :: Assertion
case_t4 = assertValue t4Fun t4Call t4Ex

-- map example
listTy :: Ty0
listTy = L0.PackedTy "List" []

mapF :: CurFun
mapF = VarDef (toVar "map") (ArrowTy (ArrowTy L0.IntTy L0.IntTy) (ArrowTy listTy listTy)) mapBod

mapBod :: Exp
mapBod = l $ Ext $ LambdaE ((toVar "f"), ArrowTy L0.IntTy L0.IntTy)
         (l $ Ext $ LambdaE ((toVar "l"), listTy)
          (l $ CaseE (l $ VarE $ toVar "l")
            [ ("Empty", [], l$ DataConE () "Empty" []),
              ("Cons", [(toVar "a", ()), (toVar "d",())],
               l$ DataConE () "Cons"
                [ l$ Ext $ PolyAppE (l $ VarE $ toVar "f") (l$ VarE $ toVar "a")
                , l$ Ext $ PolyAppE (l$ Ext $ PolyAppE (l $ VarE $ toVar "map") (l$ VarE $ toVar "f"))
                                    (l$ VarE $ toVar "d")])
            ]))

mapCall :: CCall
mapCall = l $ Ext $ PolyAppE (l $ Ext $ PolyAppE (l $ VarE $ toVar "map")
                              (l $ Ext $ LambdaE ((toVar "x"), L0.IntTy) (l $ PrimAppE AddP [(l $ VarE $ toVar "x"), (l $ LitE 2)])))
                             (l $ VarE $ toVar "ls")

mapEx :: (L0Fun, FCall)
mapEx = (FunDef (toVar "map1") (toVar "x") (L0.ProdTy [listTy], listTy) mapBodEx,
         l $ AppE (toVar "map1") [] $ l$ MkProdE [(l $ VarE $ toVar "ls")])

mapBodEx :: Exp
mapBodEx = l $ CaseE (l$ ProjE 0 $ l $ VarE $ toVar "x")
             [ ("Empty", [], l$ DataConE () "Empty" []),
               ("Cons", [(toVar "a", ()), (toVar "d",())],
                l$ DataConE () "Cons"
                [ l$ PrimAppE AddP [(l$ VarE $ toVar "a"), (l$ LitE 2)]
                , l$ AppE (toVar "map1") [] $ l$ MkProdE [l$ VarE $ toVar "d"]])
             ]

case_map :: Assertion
case_map = assertValue mapF mapCall mapEx

