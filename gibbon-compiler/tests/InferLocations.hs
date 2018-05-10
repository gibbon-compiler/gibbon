{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

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

import Data.Loc

-- l = L NoLoc


-- some basic tests of unification, some should succeed and others should fail
utest1 = runSyM 0 $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh 
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u2 
            unify l1 l2 (return True) (return False)

utest2 = runSyM 0 $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh 
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u1 
            unify l1 l2 (return True) (return False)

utest3 = runSyM 0 $ St.runStateT (runExceptT m) M.empty
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

utest4 = runSyM 0 $ St.runStateT (runExceptT m) M.empty
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

etest1 = runSyM 0 $ St.runStateT (runExceptT m) M.empty
    where m = do
            u1 <- fixLoc "a"
            u2 <- fixLoc "b"
            l1 <- fresh 
            l2 <- fresh
            assocLoc l1 u1
            assocLoc l2 u1 
            unify l1 l2 (return True) (return False)
            finishExp $ l$ DataConE l1 "Node" [l$ VarE "x",l$ VarE "y"]

case_etest1 :: Assertion
case_etest1 = (Right (l$ DataConE "a" "Node" [l$ VarE "x", l$ VarE "y"])) @=? (fst $ fst etest1)

tester1 :: L L1.Exp1 -> L Exp2
tester1 e = case fst $ fst $ runSyM 0 $ St.runStateT (runExceptT (inferExp emptyEnv e NoDest)) M.empty of
              Right a -> (\(a,_,_)->a) a
              Left a -> error $ show a

t1 :: L Exp2
t1 = tester1 (l$ L1.LitE 3)

t2 :: L Exp2
t2 = tester1 $
     l$ L1.LetE ("x",[],IntTy,l$ L1.LitE 1) $
     l$ L1.LetE ("y",[],IntTy,l$ L1.LitE 2) $
     l$ L1.LetE ("z",[],IntTy,l$ L1.PrimAppE L1.AddP [l$ L1.VarE "x", l$ L1.VarE "y"]) $
     l$ L1.VarE "z"

case_t1 :: Assertion
case_t1 = t1 @=? (l$ LitE 3)

case_t2 :: Assertion
case_t2 = t2 @=? (l$ LetE ("x",[],IntTy,l$ LitE 1) $
                  l$ LetE ("y",[],IntTy,l$ LitE 2) $
                  l$ LetE ("z",[],IntTy,l$ PrimAppE (prim L1.AddP) [l$ VarE "x", l$ VarE "y"]) $
                  l$ VarE "z")


inferLocations2Tests :: TestTree
inferLocations2Tests = $(testGroupGenerator)
