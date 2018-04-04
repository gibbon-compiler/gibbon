{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Tests for the compiler pipeline after L2
--
--   This is temporary and can be removed after the whole pipeline is ready
--
module Compiler where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import System.FilePath
import System.Directory

import Packed.FirstOrder.Common hiding (FunDef)
import Packed.FirstOrder.L1.Syntax hiding (FunDef, Prog, add1Prog)
import Packed.FirstOrder.L2.Syntax as L2
import Packed.FirstOrder.L2.Typecheck
import Packed.FirstOrder.L2.Examples
import Packed.FirstOrder.Passes.InferEffects
import Packed.FirstOrder.Passes.RouteEnds
import Packed.FirstOrder.Passes.Cursorize
import Packed.FirstOrder.Passes.Unariser
import Packed.FirstOrder.Passes.ShakeTree
import Packed.FirstOrder.Passes.HoistNewBuf
import Packed.FirstOrder.Passes.FindWitnesses
import Packed.FirstOrder.Passes.Lower
import Packed.FirstOrder.TargetInterp
import Packed.FirstOrder.Passes.Codegen
import Packed.FirstOrder.Passes.Flatten
import Packed.FirstOrder.Compiler
import qualified Packed.FirstOrder.L3.Typecheck as L3
import qualified Packed.FirstOrder.L3.Syntax as L3
import qualified Packed.FirstOrder.L4.Syntax as L4


-- | Directory to write out *.c and *.exe files
--   Relative to the gibbon-compiler dir
testDir :: FilePath
testDir = makeValid ("examples" </> "build_tmp")

-- | The compiler pipeline after inferLocations
--   It's divided into 2 functions for easy debugging. There's a good chance that we'd
--   want to inspect the output of Cursorize in most cases
runT :: Prog -> L3.Prog
runT prg = fst $ runSyM 0 $ do
    l2 <- flattenL2 prg
    l2 <- inferEffects prg
    l2 <- tcProg l2
    l2 <- routeEnds l2
    l2 <- tcProg l2
    l3 <- cursorize l2
    return l3


run2T :: L3.Prog -> L4.Prog
run2T l3 = fst $ runSyM 0 $ do
    l3 <- flattenL3 l3
    -- l3 <- findWitnesses l3
    -- l3 <- shakeTree l3
    l3 <- L3.tcProg l3
    l3 <- hoistNewBuf l3
    l3 <- unariser l3
    let mainTyPre = fmap snd $ L3.mainExp l3
    l3 <- flattenL3 l3
    l3 <- L3.tcProg l3
    lower (True, mainTyPre) l3


cg :: Prog -> IO String
cg = codegenProg True . run2T . runT


type Expected = String

runner :: FilePath -> Prog -> Expected -> Assertion
runner fp prg exp = do
    _ <- createDirectoryIfMissing True testDir
    fp <- makeAbsolute $ testDir </> fp
    op <- cg prg
    writeFile fp op
    res <- compileAndRunExe (defaultConfig { mode = RunExe }) fp
    let res' = init res -- strip trailing newline
    exp @=? res'


case_add1 :: Assertion
case_add1 = runner "add1.c" add1Prog "(Node (Leaf 2) (Leaf 3))"

case_copy_tree :: Assertion
case_copy_tree = runner "copytree.c" copyTreeProg "(Node (Leaf 1) (Leaf 2))"

case_copy_on_id1 :: Assertion
case_copy_on_id1 = runner "copyid1.c" copyOnId1Prog "(Node (Leaf 1) (Leaf 2))"

case_id3 :: Assertion
case_id3 = runner "id3.c" id3Prog "42"

case_int_add :: Assertion
case_int_add = runner "intAdd.c" id3Prog "42"

case_node :: Assertion
case_node = runner "node.c" nodeProg "(Node (Leaf 1) (Leaf 2))"

case_leaf :: Assertion
case_leaf = runner "leaf.c" leafProg "(Leaf 1)"

case_leftmost :: Assertion
case_leftmost = runner "leftmost.c" leftmostProg "1"

case_rightmost :: Assertion
case_rightmost = runner "rightmost.c" rightmostProg "2"

case_buildleaf :: Assertion
case_buildleaf = runner "buildleaf.c" buildLeafProg "(Leaf 42)"

case_buildtree :: Assertion
case_buildtree = runner "buildtree.c" buildTreeProg
                 "(Node (Node (Node (Leaf 1) (Leaf 1)) (Node (Leaf 1) (Leaf 1))) (Node (Node (Leaf 1) (Leaf 1)) (Node (Leaf 1) (Leaf 1))))"

case_buildtreesum :: Assertion
case_buildtreesum = runner "buildtreesum.c" buildTreeSumProg
                 "'#(8 (Node (Node (Node (Leaf 1) (Leaf 1)) (Node (Leaf 1) (Leaf 1))) (Node (Node (Leaf 1) (Leaf 1)) (Node (Leaf 1) (Leaf 1)))))"

case_printtup :: Assertion
case_printtup = runner "printtup.c" printTupProg "'#(42 (Leaf 1))"

case_printtup2 :: Assertion
case_printtup2 = runner "printtup2.c" printTupProg2 "'#((Node (Node (Leaf 1) (Leaf 1)) (Node (Leaf 1) (Leaf 1))) (Node (Leaf 1) (Leaf 1)))"

case_addtrees :: Assertion
case_addtrees = runner "addtrees.c" addTreesProg "(Node (Node (Leaf 2) (Leaf 2)) (Node (Leaf 2) (Leaf 2)))"

{-

[2018.04.03]: Changing the inlining policy of ProjE and MkProdE causes this test to
fail. Either Unariser or Lower or both seem to be the having problems with
flattened programs. If we don't flatten the program before
those passes, this example works. Also, even if we increase the depth of the tree,
only the last node is incorrect.

case_sumupseteven :: Assertion
case_sumupseteven = runner "sumupseteven.c" sumUpSetEvenProg "'#((Inner 8 1 (Inner 4 1 (Inner 2 1 (Leaf 1) (Leaf 1)) (Inner 2 1 (Leaf 1) (Leaf 1))) (Inner 4 1 (Inner 2 1 (Leaf 1) (Leaf 1)) (Inner 2 1 (Leaf 1) (Leaf 1)))) 8)"

-}
case_subst :: Assertion
case_subst = runner "subst.c" substProg "(LETE 1 (VARREF 42) (VARREF 10))"

compilerTests :: TestTree
compilerTests = $(testGroupGenerator)
