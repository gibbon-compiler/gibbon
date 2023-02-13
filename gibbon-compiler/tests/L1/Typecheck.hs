{-# LANGUAGE TemplateHaskell #-}

-- | Tests for the L1 typechecker
module L1.Typecheck where

import Test.Tasty.HUnit
import Test.Tasty.TH
import Test.Tasty

import Control.Monad.Except
import Data.Map as M
import Data.Set as S

import Gibbon.Common hiding (FunDef)
import Gibbon.L1.Syntax
import Gibbon.L1.Typecheck

type Exp = Exp1

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
        funEnv = M.fromList [ ("add", ([IntTy, IntTy], IntTy))
                            , ("mul", ([IntTy, IntTy], IntTy))]

ddfs :: DDefs Ty1
ddfs = M.fromList
        [("Foo",
          DDef {tyName = "Foo",
                tyArgs = [],
                dataCons = [("A", [(False, IntTy)]),
                            ("B", [(False, IntTy),(False, IntTy)])]}),
         ("Nat",
           DDef {tyName = "Nat",
                 tyArgs = [],
                 dataCons = [("Zero", []),("Suc", [(False, PackedTy "Nat" ())])]})]

l1TypecheckerTests :: TestTree
l1TypecheckerTests = $(testGroupGenerator)

--------------------------------------------------------------------------------

-- t6 :: Exp
-- t6 = LetE ("d0",
--               [],
--               SymDictTy IntTy,
--               PrimAppE (DictEmptyP IntTy) [])
--      (LetE ("d21",
--                [],
--                SymDictTy IntTy,
--                PrimAppE (DictInsertP IntTy) [VarE "d0",LitSymE "hi",LitE 200])
--       (LitE 44))

-- case_test_6 :: Assertion
-- case_test_6 = assertValue t6 IntTy

t5 :: Exp
t5 =  CaseE (DataConE () "B" [ LitE 2, LitE 4])
     [("A", [("x", ())], VarE "x"),
      ("B", [("x", ()),("y", ())], PrimAppE MkFalse [])]


case_test_5 :: Assertion
case_test_5 = assertError t5 expected
  where expected =  GenericTC "Case branches have mismatched types: IntTy, BoolTy"
                    (PrimAppE MkFalse [])

case_test_4 :: Assertion
case_test_4 = assertError t4 expected
  where expected = GenericTC "Expected these types to be the same: IntTy, BoolTy"
                   (PrimAppE MkTrue [])


t4 :: Exp
t4 = LetE ("ev",[], PackedTy "Foo" (), DataConE () "A" [PrimAppE MkTrue []]) $
     CaseE (VarE "ev")
     [("A", [], (LitE 10)),
      ("B", [("x", ()),("y", ())], LitE 200)]

case_test_3 :: Assertion
case_test_3 = assertValue t3 IntTy

t3 :: Exp
t3 = IfE (PrimAppE EqIntP [ LitE 1,  LitE 1])
     (IfE ( PrimAppE EqIntP [ LitE 2,  LitE 2])
       ( LitE 100)
       ( LitE 1))
     ( LitE 2)

case_test_2 :: Assertion
case_test_2 = assertValue t2 (PackedTy "Foo" ())

t2 :: Exp
t2 =  DataConE () "A" [ LitE 10]


case_test_1 :: Assertion
case_test_1 = assertValue t1 IntTy

t1 :: Exp
t1 =  AppE "mul" []
     [LitE 10, AppE "add" [] [LitE 40, LitE 2]]


t1Prog :: Prog1
t1Prog = Prog {ddefs = M.fromList [],
        fundefs = M.fromList
                  [("mul2",
                    FunDef {funName = "mul2",
                            funArgs = ["x_y1"],
                            funTy = ([IntTy,IntTy] , IntTy),
                            funBody = PrimAppE MulP
                                      [(VarE "x_y1"), (VarE "x_y1")],
                            funMeta = FunMeta { funInline = Inline,
                                                funRec = NotRec,
                                                funCanTriggerGC = False

                                              }
                           }),
                   ("add2",
                    FunDef {funName = "add2",
                            funArgs = ["x_y0"],
                            funTy = ([IntTy,IntTy], IntTy),
                            funBody = PrimAppE AddP
                                      [(VarE "x_y0"),
                                       (VarE "x_y0")],
                            funMeta = FunMeta { funInline = Inline,
                                                funRec = NotRec,
                                                funCanTriggerGC = False
                                              }
                           })],
        mainExp = Just
                  (  AppE "mul2" [] [LitE 10, AppE "add2" [] [LitE 40, LitE 2]]
                  , IntTy)
              }

-- | upon successful typechecking, it just returns the same program
case_run_tcProg :: Assertion
case_run_tcProg = t1Prog @=? res
  where res = fst $ defaultRunPassM $ tcProg t1Prog
