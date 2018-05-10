{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Tests for the L1 typechecker
module L1.Typecheck where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Control.Monad.Except
import Data.Loc
import Data.Map as M
import Data.Set as S

import Gibbon.Common hiding (FunDef)
import Gibbon.L1.Syntax
import Gibbon.L1.Typecheck

type Exp = L Exp1

-- |
assertValue :: Exp -> Ty1 -> Assertion
assertValue exp expected =
  case tester exp of
    Left err -> assertFailure $ show err
    Right actual -> expected @=? actual


-- |
assertError :: Exp -> (TCError Exp) -> Assertion
assertError exp expected =
  case tester exp of
    Left actual -> expected @=? actual
    Right err -> assertFailure $ show err

tester :: Exp -> Either (TCError Exp) Ty1
tester = runExcept . (tcExp ddfs env)
  where env = Env2 M.empty funEnv
        funEnv = M.fromList [ ("add", (ProdTy [IntTy, IntTy], IntTy))
                            , ("mul", (ProdTy [IntTy, IntTy], IntTy))]

ddfs :: DDefs Ty1
ddfs = M.fromList
        [("Foo",
          DDef {tyName = "Foo",
                dataCons = [("A", [(False, IntTy)]),
                            ("B", [(False, IntTy),(False, IntTy)])]}),
         ("Nat",
           DDef {tyName = "Nat",
                 dataCons = [("Zero", []),("Suc", [(False, PackedTy "Nat" ())])]})]

l1TypecheckerTests :: TestTree
l1TypecheckerTests = $(testGroupGenerator)

--------------------------------------------------------------------------------

t6 :: Exp
t6 = l$ LetE ("d0",
              [],
              SymDictTy IntTy,
              l$ PrimAppE (DictEmptyP IntTy) [])
     (l$ LetE ("d21",
               [],
               SymDictTy IntTy,
               l$ PrimAppE (DictInsertP IntTy) [l$ VarE "d0",l$ LitSymE "hi",l$ LitE 200])
      (l$ LitE 44))

case_test_6 :: Assertion
case_test_6 = assertValue t6 IntTy

t5 :: Exp
t5 = l$  CaseE (l$ DataConE () "B" [l$  LitE 2, l$ LitE 4])
     [("A", [("x", ())], l$ VarE "x"),
      ("B", [("x", ()),("y", ())], l$ PrimAppE MkFalse [])]


case_test_5 :: Assertion
case_test_5 = assertError t5 expected
  where expected =  GenericTC "Case branches have mismatched types: IntTy, BoolTy"
                    (l$ PrimAppE MkFalse [])

case_test_4 :: Assertion
case_test_4 = assertError t4 expected
  where expected = GenericTC "Expected these types to be the same: IntTy, BoolTy"
                   (l$ PrimAppE MkTrue [])


t4 :: Exp
t4 = l$ LetE ("ev",[], PackedTy "Foo" (), l$ DataConE () "A" [l$ PrimAppE MkTrue []]) $
     l$ CaseE (l$ VarE "ev")
     [("A", [], (l$ LitE 10)),
      ("B", [("x", ()),("y", ())], l$ LitE 200)]

case_test_3 :: Assertion
case_test_3 = assertValue t3 IntTy

t3 :: Exp
t3 = l$ IfE (l$ PrimAppE EqIntP [l$  LitE 1, l$  LitE 1])
     (l$ IfE (l$  PrimAppE EqIntP [l$  LitE 2, l$  LitE 2])
       (l$  LitE 100)
       (l$  LitE 1))
     (l$  LitE 2)

case_test_2 :: Assertion
case_test_2 = assertValue t2 (PackedTy "Foo" ())

t2 :: Exp
t2 = l$  DataConE () "A" [l$  LitE 10]


case_test_1 :: Assertion
case_test_1 = assertValue t1 IntTy

t1 :: Exp
t1 = l$  AppE "mul" []
     (l$ MkProdE [l$ LitE 10, l$ AppE "add" [] (l$ MkProdE [l$ LitE 40, l$ LitE 2])])


t1Prog :: Prog
t1Prog = Prog {ddefs = M.fromList [],
        fundefs = M.fromList
                  [("mul2",
                    FunDef {funName = "mul2",
                            funArg = ("x_y1", ProdTy [IntTy,IntTy]),
                            funRetTy = IntTy,
                            funBody = l$ PrimAppE MulP
                                      [l$ ProjE 0 (l$ VarE "x_y1"), l$ ProjE 1 (l$ VarE "x_y1")]}),
                   ("add2",
                    FunDef {funName = "add2",
                            funArg = ("x_y0", ProdTy [IntTy,IntTy]),
                            funRetTy = IntTy,
                            funBody = l$ PrimAppE AddP
                                      [l$ ProjE 0 (l$ VarE "x_y0"),
                                       l$ ProjE 1 (l$ VarE "x_y0")]})],
        mainExp = Just $ l$  AppE "mul2"
                  []
                  (l$ MkProdE [l$ LitE 10, l$ AppE "add2" [] (l$ MkProdE [l$ LitE 40, l$ LitE 2])])}

-- | upon successful typechecking, it just returns the same program
case_run_tcProg :: Assertion
case_run_tcProg = t1Prog @=? res
  where res = fst $ runSyM 0 $ tcProg t1Prog
