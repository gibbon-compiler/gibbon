{-# LANGUAGE TemplateHaskell #-}

-- | Tests for InferLocations
--
module InferLocations where

import Data.Set as S
import Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common hiding (FunDef)
import Gibbon.L2.Syntax as L2
import Gibbon.L2.Examples
import Gibbon.Passes.InferLocations
import qualified Gibbon.L1.Syntax as L1


import qualified Control.Monad.Trans.State.Strict as St
import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans (lift)

-- some basic tests of unification, some should succeed and others should fail
utest1 = defaultPackedRunPassM $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u2
            unify l1 l2 (return True) (return False)

utest2 = defaultPackedRunPassM $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u1
            unify l1 l2 (return True) (return False)

utest3 = defaultPackedRunPassM $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            u3 <- freshUnifyLoc
            l1 <- fresh
            l2 <- fresh
            l3 <- fresh
            assocLoc l1 u1
            assocLoc l2 u2
            assocLoc l3 u3
            unify l1 l3 (unify l2 l3 (return True) (return False)) (return False)

utest4 = defaultPackedRunPassM $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            u3 <- freshUnifyLoc
            l1 <- fresh
            l2 <- fresh
            l3 <- fresh
            l4 <- fresh
            assocLoc l1 u1
            assocLoc l2 u2
            assocLoc l3 u3
            unify l1 l3 (unify l4 l2 (return True) (return False)) (return False)

case_unify1 :: Assertion
case_unify1 = (Right False) @=? (fst $ fst utest1)

case_unify2 :: Assertion
case_unify2 = (Right True) @=? (fst $ fst utest2)

case_unify3 :: Assertion
case_unify3 = (Right False) @=? (fst $ fst utest3)

case_unify4 :: Assertion
case_unify4 = (Right True) @=? (fst $ fst utest4)

etest1 = defaultPackedRunPassM $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u1
            unify l1 l2 (return True) (return False)
            finishExp $ DataConE l1 "Node" [VarE "x",VarE "y"]

case_etest1 :: Assertion
case_etest1 = (Right (DataConE "a" "Node" [VarE "x", VarE "y"])) @=? (fst $ fst etest1)

tester1 :: L1.Exp1 -> Exp2
tester1 e = case fst $ fst $ defaultPackedRunPassM $ St.runStateT (runExceptT (inferExp emptyEnv e NoDest)) M.empty of
              Right a -> (\(a,_,_)->a) a
              Left a -> error $ show a

t1 :: Exp2
t1 = tester1 (L1.LitE 3)

t2 :: Exp2
t2 = tester1 $
     L1.LetE ("x",[],IntTy,L1.LitE 1) $
     L1.LetE ("y",[],IntTy,L1.LitE 2) $
     L1.LetE ("z",[],IntTy,L1.PrimAppE L1.AddP [L1.VarE "x", L1.VarE "y"]) $
     L1.VarE "z"

case_t1 :: Assertion
case_t1 = t1 @=? (LitE 3)

case_t2 :: Assertion
case_t2 = t2 @=? (LetE ("x",[],IntTy,LitE 1) $
                  LetE ("y",[],IntTy,LitE 2) $
                  LetE ("z",[],IntTy,PrimAppE L2.AddP [VarE "x", VarE "y"]) $
                  VarE "z")


inferLocations2Tests :: TestTree
inferLocations2Tests = $(testGroupGenerator)
