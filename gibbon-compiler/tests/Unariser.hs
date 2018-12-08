{-# LANGUAGE TemplateHaskell #-}

-- | Tests for Unariser2
--
module Unariser
  (unariser2Tests) where

import Data.Set as S
import Data.Map as M
import Data.Loc

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common hiding (FunDef, FunDefs)
import Gibbon.L1.Syntax hiding (FunDef, Prog, PreProg(..), FunDefs)
import Gibbon.L3.Syntax
import Gibbon.Passes.Unariser


run :: L Exp3 -> L Exp3
run x = fst $ defaultRunPassM $ unariserExp undefined [] (Env2 M.empty M.empty) x

case_t1 :: Assertion
case_t1 = expected @=? actual
  where
    actual = run test1

    test1 :: L Exp3
    test1 = l$ LetE ("v1",[],ProdTy [IntTy, IntTy],
                     l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
            l$ LetE ("v2",[],ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ MkProdE [l$ LitE 3, l$ VarE "v1"]) $
            l$ LetE ("v6",[],ProdTy [IntTy, ProdTy [IntTy, IntTy]] ,
                     l$ MkProdE [l$ LitE 1, l$ MkProdE [l$ LitE 1, l$ LitE 2]]) $
            l$ LetE ("v4",[],ProdTy [IntTy, IntTy],
                     l$ ProjE 1 (l$ VarE "v6")) $
            l$ LetE ("v3",[], ProdTy [IntTy, ProdTy [IntTy, ProdTy [IntTy, IntTy]]],
                      l$ MkProdE [l$ LitE 4, l$ VarE "v2"]) $
            l$ LetE ("v5",[], ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ ProjE 1 (l$ VarE "v3")) $
            l$ VarE "v5"

    expected :: L Exp3
    expected =  l$ LetE ("v1",[],ProdTy [IntTy, IntTy],
                         l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
                l$ LetE ("v2",[],ProdTy [IntTy,IntTy,IntTy],
                         l$ MkProdE [l$ LitE 3, l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1")]) $
                l$ LetE ("v6",[],ProdTy [IntTy,IntTy,IntTy] ,
                         l$ MkProdE [l$ LitE 1, l$ LitE 1, l$ LitE 2]) $
                l$ LetE ("v4",[],ProdTy [IntTy, IntTy],
                         l$ MkProdE [l$ ProjE 1 (l$ VarE "v6"), l$ ProjE 2 (l$ VarE "v6")]) $
                l$ LetE ("v3",[], ProdTy [IntTy,IntTy,IntTy,IntTy],
                         l$ MkProdE [l$ LitE 4, l$ ProjE 0 (l$ VarE "v2"), l$ ProjE 1 (l$ VarE "v2"),
                                     l$ ProjE 2 (l$ VarE "v2")]) $
                l$ LetE ("v5",[], ProdTy [IntTy,IntTy,IntTy],
                         l$ MkProdE [l$ ProjE 1 (l$ VarE "v3"), l$ ProjE 2 (l$ VarE "v3"),
                                     l$ ProjE 3 (l$ VarE "v3")]) $
                l$ VarE "v5"

case_t2 :: Assertion
case_t2 = expected @=? actual
  where
    actual = run test2

    test2 :: L Exp3
    test2 = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
            l$ LetE ("v2",[],ProdTy [ProdTy [CursorTy, CursorTy], IntTy],
                     l$ MkProdE [l$ VarE "v1", l$ LitE 3]) $
            l$ LetE ("v3",[], IntTy, l$ ProjE 1 (l$ VarE "v2")) $
            l$ VarE "v3"

    expected :: L Exp3
    expected = l$ LetE ("v1",[],ProdTy [IntTy, IntTy],
                        l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
               l$ LetE ("v2",[],ProdTy [CursorTy, CursorTy, IntTy],
                        l$ MkProdE [l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1"), l$ LitE 3]) $
               l$ LetE ("v3",[], IntTy, l$ ProjE 2 (l$ VarE "v2")) $
               l$ VarE "v3"

case_t3 :: Assertion
case_t3 = expected @=? actual
  where
    actual = run test3

    test3 :: L Exp3
    test3 = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
            l$ LetE ("v2",[],ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ MkProdE [l$ LitE 3, l$ VarE "v1"]) $
            l$ LetE ("v3",[], IntTy,
                     l$ ProjE 1 (l$ ProjE 1 (l$ VarE "v2"))) $
            l$ VarE "v3"


    expected :: L Exp3
    expected = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
               l$ LetE ("v2",[],ProdTy [IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ LitE 3, l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1")]) $
               l$ LetE ("v3",[], IntTy,
                        l$ ProjE 2 (l$ VarE "v2")) $
               l$ VarE "v3"


case_t4 :: Assertion
case_t4 = expected @=? actual
  where
    actual = run test4

    test4 :: L Exp3
    test4 = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
            l$ LetE ("v2",[],ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ MkProdE [l$ LitE 3, l$ VarE "v1"]) $
            l$ LetE ("v3",[],ProdTy [IntTy, ProdTy [IntTy, ProdTy [IntTy, IntTy]]],
                     l$ MkProdE [l$ LitE 4, l$ VarE "v2"]) $
            l$ LetE ("v4",[], ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ ProjE 1 (l$ VarE "v3")) $
            l$ VarE "v4"


    expected :: L Exp3
    expected = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
               l$ LetE ("v2",[],ProdTy [IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ LitE 3, l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1")]) $
               l$ LetE ("v3",[],ProdTy [IntTy, IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ LitE 4, l$ ProjE 0 (l$ VarE "v2"), l$ ProjE 1 (l$ VarE "v2"), l$ ProjE 2 (l$ VarE "v2")]) $
               l$ LetE ("v4",[], ProdTy [IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ ProjE 1 (l$ VarE "v3"), l$ ProjE 2 (l$ VarE "v3"), l$ ProjE 3 (l$ VarE "v3")]) $
               l$ VarE "v4"


case_t5 :: Assertion
case_t5 = expected @=? actual
  where
    actual = run test5

    test5 :: L Exp3
    test5 = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
            l$ LetE ("v2",[],ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ MkProdE [l$ LitE 1, l$ MkProdE [l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1")]]) $
            l$ LetE ("v3",[], ProdTy [IntTy, ProdTy [IntTy, IntTy]],
                     l$ MkProdE [l$ LitE 1, l$ MkProdE [l$ LitE 2, l$ ProjE 0 $ l$ ProjE 1 (l$ VarE "v2")]]) $
            l$ VarE "v3"

    expected :: L Exp3
    expected = l$ LetE ("v1",[],ProdTy [IntTy, IntTy], l$ MkProdE [l$ LitE 1, l$ LitE 2]) $
               l$ LetE ("v2",[],ProdTy [IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ LitE 1, l$ ProjE 0 (l$ VarE "v1"), l$ ProjE 1 (l$ VarE "v1")]) $
               l$ LetE ("v3",[], ProdTy [IntTy, IntTy, IntTy],
                        l$ MkProdE [l$ LitE 1, l$ LitE 2, l$ ProjE 1 (l$ VarE "v2")]) $
               l$ VarE "v3"


unariser2Tests :: TestTree
unariser2Tests = $(testGroupGenerator)
