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
        funEnv = M.fromList [ ("add", ([IntTy W64, IntTy W64], IntTy W64))
                            , ("mul", ([IntTy W64, IntTy W64], IntTy W64))]

ddfs :: DDefs Ty1
ddfs = M.fromList
        [("Foo",
          DDef {tyName = "Foo",
                tyArgs = [],
                dataCons = [("A", [(False, IntTy W64)]),
                            ("B", [(False, IntTy W64),(False, IntTy W64)])],
                 memLayout = Linear}),
         ("Nat",
           DDef {tyName = "Nat",
                 tyArgs = [],
                 dataCons = [("Zero", []),("Suc", [(False, PackedTy "Nat" ())])],
                 memLayout = Linear})
        ]

l1TypecheckerTests :: TestTree
l1TypecheckerTests = $(testGroupGenerator)

--------------------------------------------------------------------------------

-- t6 :: Exp
-- t6 = LetE ("d0",
--               [],
--               SymDictTy IntTy W64,
--               PrimAppE (DictEmptyP IntTy W64) [])
--      (LetE ("d21",
--                [],
--                SymDictTy IntTy W64,
--                PrimAppE (DictInsertP IntTy W64) [VarE "d0",LitSymE "hi",mkLitE64 200])
--       (mkLitE64 44))

-- case_test_6 :: Assertion
-- case_test_6 = assertValue t6 IntTy W64

t5 :: Exp
t5 =  CaseE (DataConE () "B" [ mkLitE64 2, mkLitE64 4])
     [("A", [("x", ())], VarE "x"),
      ("B", [("x", ()),("y", ())], PrimAppE MkFalse [])]


case_test_5 :: Assertion
case_test_5 = assertError t5 expected
  where expected =  GenericTC "Case branches have mismatched types: IntTy W64, BoolTy"
                    (PrimAppE MkFalse [])

case_test_4 :: Assertion
case_test_4 = assertError t4 expected
  where expected = GenericTC "Expected these types to be the same: IntTy W64, BoolTy"
                   (PrimAppE MkTrue [])


t4 :: Exp
t4 = LetE ("ev",[], PackedTy "Foo" (), DataConE () "A" [PrimAppE MkTrue []]) $
     CaseE (VarE "ev")
     [("A", [], (mkLitE64 10)),
      ("B", [("x", ()),("y", ())], mkLitE64 200)]

case_test_3 :: Assertion
case_test_3 = assertValue t3 (IntTy W64)

t3 :: Exp
t3 = IfE (PrimAppE eqIntP64 [ mkLitE64 1,  mkLitE64 1])
     (IfE ( PrimAppE eqIntP64 [ mkLitE64 2,  mkLitE64 2])
       ( mkLitE64 100)
       ( mkLitE64 1))
     ( mkLitE64 2)

case_test_2 :: Assertion
case_test_2 = assertValue t2 (PackedTy "Foo" ())

t2 :: Exp
t2 =  DataConE () "A" [ mkLitE64 10]


case_test_1 :: Assertion
case_test_1 = assertValue t1 (IntTy W64)

t1 :: Exp
t1 =  AppE "mul" UnknownTailType []
     [mkLitE64 10, AppE "add" UnknownTailType [] [mkLitE64 40, mkLitE64 2]]


t1Prog :: Prog1
t1Prog = Prog {ddefs = M.fromList [],
        fundefs = M.fromList
                  [("mul2",
                    FunDef {funName = "mul2",
                            funArgs = ["x_y1"],
                            funTy = ([IntTy W64,IntTy W64] , IntTy W64),
                            funBody = PrimAppE mulP64
                                      [(VarE "x_y1"), (VarE "x_y1")],
                            funMeta = FunMeta { funInline = Inline,
                                                funRec = NotRec,
                                                funCanTriggerGC = False,
                                                funOpt = []
                                                , funCursorAbi = Nothing
                                              }
                           }),
                   ("add2",
                    FunDef {funName = "add2",
                            funArgs = ["x_y0"],
                            funTy = ([IntTy W64,IntTy W64], IntTy W64),
                            funBody = PrimAppE addP64
                                      [(VarE "x_y0"),
                                       (VarE "x_y0")],
                            funMeta = FunMeta { funInline = Inline,
                                                funRec = NotRec,
                                                funCanTriggerGC = False,
                                                funOpt = []
                                                , funCursorAbi = Nothing
                                              }
                           })],
        mainExp = Just
                  (  AppE "mul2" UnknownTailType [] [mkLitE64 10, AppE "add2" UnknownTailType [] [mkLitE64 40, mkLitE64 2]]
                  , IntTy W64)
              }

-- | upon successful typechecking, it just returns the same program
case_run_tcProg :: Assertion
case_run_tcProg = t1Prog @=? res
  where res = fst $ defaultRunPassM $ tcProg t1Prog
