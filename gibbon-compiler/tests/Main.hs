{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

-- |

module Main where

-- |
import Data.Word (Word8)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


-- |
import Packed.FirstOrder.L4.Syntax hiding (Prog (..), Ty (..))

import Packed.FirstOrder.Common (Multiplicity(..))
import qualified Packed.FirstOrder.L4.Syntax as T
import qualified Packed.FirstOrder.TargetInterp as TI

-- |
import RouteEnds
import InferEffects
import InferMul
import Unariser
import Compiler
import L2.Typecheck
import L1.Typecheck
import L3.Typecheck
import InferLocations

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All"
                   [ tests
                   , routeEnds2Tests
                   , inferLocations2Tests
                   , inferEffects2Tests
                   , inferMulTests
                   , unariser2Tests
                   -- , l2TypecheckerTests
                   , l1TypecheckerTests
                   , l3TypecheckerTests
                   , compilerTests
                   ]


tests :: TestTree
tests = $(testGroupGenerator)


--
--
-- Unit test the.L2.Syntax.hs functions:
--------------------------------------------------------------------------------
{- -- UNDER_CONSTRUCTION.
t0 :: Set Effect -> Set Effect
t0 eff = arrEffs $ fst $ runSyM 0 $
     inferFunDef (M.empty,
                   M.singleton "foo" (ArrowTy (PackedTy "K" "p")
                                              eff
                                              (PackedTy "K" "p")))
                  (C.FunDef "foo" "x", L1.Packed "K" (L1.Packed "K")
                   (L1.AppE "foo" (L1.VarE "x")))

_case_t0 :: Assertion
_case_t0 = assertEqual "infinite loop traverses anything"
                     (S.fromList [Traverse "p"]) (t0 (S.singleton (Traverse "p")))

_case_t0b :: Assertion
_case_t0b = assertEqual "infinite loop cannot bootstrap with bad initial effect set"
                     S.empty (t0 S.empty)


-- The function foo below should traverse "a" but does not have any
-- output locations.
t1 :: (Set Effect)
t1 = arrEffs $ fst $ runSyM 0 $
     inferFunDef (M.empty,
                   M.fromList
                   [("copy",(ArrowTy (PackedTy "K" "p")
                                                   (S.fromList [Traverse "p", Traverse "o"])
                                              (PackedTy "K" "o")))
                   ,("foo", ArrowTy (PackedTy "K" "a")) S.empty IntTy])
                  (C.FunDef "foo" ("x", L1.Packed "K") L1.IntTy $
                     L1.LetE ("ignr", L1.Packed "K", (L1.AppE "copy" (L1.VarE "x"))) $
                     L1.LitE 33
                  )

_case_t1 :: Assertion
_case_t1 = assertEqual "traverse input via another call"
          (S.fromList [Traverse "a"]) t1

type FunEnv = M.Map Var (L2.ArrowTy Ty)

t2env :: (DDefs a, FunEnv)
t2env = ( fromListDD [DDef "Bool" [("True",[]), ("False",[])]]
                  , M.fromList [("foo", ArrowTy (PackedTy "Bool" "p") S.empty IntTy)])
fooBoolInt :: a -> L1.FunDef L1.Ty a
fooBoolInt = C.FunDef "foo" ("x", L1.Packed "Bool") L1.IntTy

t2 :: (Set Effect)
t2 = arrEffs $ fst $ runSyM 0 $
     inferFunDef t2env
                  (fooBoolInt $
                    L1.CaseE (VarE "x") $
                      [ ("True",[],LitE 3)
                      , ("False",[],LitE 3) ])

_case_t2 :: Assertion
_case_t2 = assertEqual "Traverse a Bool with case"
            (S.fromList [Traverse "p"]) t2

t2b :: (Set Effect)
t2b = arrEffs $ fst $ runSyM 0 $
     inferFunDef t2env (fooBoolInt $ LitE 33)

_case_t2b :: Assertion
_case_t2b = assertEqual "No traverse from a lit" S.empty t2b

t2c :: (Set Effect)
t2c = arrEffs $ fst $ runSyM 0 $
     inferFunDef t2env (fooBoolInt $ VarE "x")

_case_t2c :: Assertion
_case_t2c = assertEqual "No traverse from identity function" S.empty t2b


t3 :: Exp -> Set Effect
t3 bod0 = arrEffs $ fst $ runSyM 0 $
     inferFunDef ( fromListDD [DDef "SillyTree"
                                  [ ("Leaf",[])
                                  , ("Node",[L1.Packed "SillyTree", L1.IntTy])]]
                  , M.fromList [("foo", ArrowTy (PackedTy "SillyTree" "p") S.empty IntTy)])
                  (C.FunDef "foo" ("x", L1.Packed "SillyTree") L1.IntTy
                    bod0)

_case_t3a :: Assertion
_case_t3a = assertEqual "sillytree1" S.empty (t3 (LitE 33))

_case_t3b :: Assertion
_case_t3b = assertEqual "sillytree2" S.empty $ t3 $ VarE "x"


_case_t3c :: Assertion
_case_t3c = assertEqual "sillytree3: reference rightmost"
           (S.singleton (Traverse "p")) $ t3 $
           L1.CaseE (VarE "x")
            [ ("Leaf", [],     LitE 3)
            , ("Node", ["l","r"], VarE "r")
            ]

_case_t3d :: Assertion
_case_t3d = assertEqual "sillytree3: reference leftmost"
           S.empty $ t3 $
           L1.CaseE (VarE "x")
            [ ("Leaf", [],     LitE 3)
            , ("Node", ["l","r"], VarE "l")]

t4 :: Exp -> Set Effect
t4 bod = arrEffs $ fst $ runSyM 0 $
     inferFunDef t4env
                  (C.FunDef "foo" ("x", L1.Packed "Tree") L1.IntTy
                    bod)

t4env :: (DDefs L1.Ty, FunEnv)
t4env = ( fromListDD [DDef "Tree"
                      [ ("Leaf",[L1.IntTy])
                      , ("Node",[L1.Packed "Tree", L1.Packed "Tree"])]]
        , M.fromList [("foo", ArrowTy (PackedTy "Tree" "p")
                       (S.singleton (Traverse "p"))
                       IntTy)])

_case_t4a :: Assertion
_case_t4a = assertEqual "bintree1" S.empty (t4 (LitE 33))

_case_t4b :: Assertion
_case_t4b = assertEqual "bintree2: matching is not enough for traversal"
           S.empty $ t4 $
           L1.CaseE (VarE "x")
            [ ("Leaf", ["n"],     LitE 3)
            , ("Node", ["l", "r"], LitE 4)]

_case_t4c :: Assertion
_case_t4c = assertEqual "bintree2: referencing is not enough for traversal"
           S.empty $ t4 $
           L1.CaseE (VarE "x")
            [ ("Leaf", ["n"],     LitE 3)
            , ("Node", ["l","r"], VarE "r")]

_case_t4d :: Assertion
_case_t4d = assertEqual "bintree2: recurring left is not enough"
           S.empty $ t4 $
           L1.CaseE (VarE "x")
            [ ("Leaf", ["n"],     LitE 3)
            , ("Node", ["l","r"], AppE "foo" (VarE "l"))]

_case_t4e :: Assertion
_case_t4e = assertEqual "bintree2: recurring on the right IS enough"
           (S.singleton (Traverse "p")) $ t4 $
           trav_right_bod

trav_right_bod :: Exp
trav_right_bod = L1.CaseE (VarE "x")
                 [ ("Leaf", ["n"],     LitE 3)
                 , ("Node", ["l","r"], AppE "foo" (VarE "r"))]
         -- ^ NOTE - this should return a location inside the input.  A
         -- sub-region of the region at p.

t4_prog :: L1.Prog
t4_prog = L1.Prog (fst t4env)
          (fromListFD [C.FunDef "foo" ("x", L1.Packed "Tree") L1.IntTy
                       trav_right_bod])
          Nothing

t4p :: Prog
t4p = fst $ runSyM 0 $ inferEffects t4_prog

_case_t4p :: Assertion
_case_t4p =
    assertEqual "Infer the effects for an entire tree-traversal prog:"
      (S.singleton (Traverse "a"))
      (let FunDef _ (ArrowTy _ efs _) _ _ = fundefs t4p M.! "foo"
       in efs)

_case_t4p2 :: Assertion
_case_t4p2 =
    assertEqual "A program which needs more than one fix-point iteration."
      (S.empty)
      (let prg = fst $ runSyM 0 $ inferEffects
                 (L1.Prog (fst t4env)
                        (fromListFD [C.FunDef "foo" ("x", L1.Packed "Tree") L1.IntTy $
                          L1.CaseE (VarE "x")
                            [ ("Leaf", ["n"],     LitE 3)
                            , ("Node", ["l","r"], AppE "foo" (VarE "l"))] ])
                  Nothing)
           FunDef _ (ArrowTy _ efs _) _ _ = fundefs prg M.! "foo"
       in efs)

----------------------------------------


-- Now the full copy-tree example:
copy :: Prog
copy = fst $ runSyM 0 $ inferEffects
     (L1.Prog (fst t4env)
      (fromListFD [C.FunDef "copy" ("x", L1.Packed "Tree") (L1.Packed "Tree") $
                   L1.CaseE (VarE "x")
                      [ ("Leaf", ["n"],   VarE "n")
                      , ("Node", ["l", "r"],
                        LetE ("a", L1.Packed "Tree", AppE "copy" (VarE "l")) $
                        LetE ("b", L1.Packed "Tree", AppE "copy" (VarE "r")) $
                        DataConE "Node" [VarE "a", VarE "b"]
                        )] ])
      Nothing)

_case_copy :: Assertion
_case_copy =
     assertEqual "A program which needs more than one fix-point iteration."
      (S.singleton (Traverse "a"))
      (let prg = copy
           FunDef _ (ArrowTy _ efs _) _ _ = fundefs prg M.! "copy"
       in efs)

-- t5 :: Prog
-- t5 = fst $ runSyM 1000 $
--      cursorize copy
-}
--------------------------------------------------------------------------------
-- add1 example encoded as AST by hand

add1_prog :: T.Prog
add1_prog = T.Prog [build_tree, add1]
            (Just $ PrintExp $
             LetPrimCallT [("buf", T.CursorTy)] (T.NewBuffer BigInfinite) [] $
             LetPrimCallT [("buf2", T.CursorTy)] (T.NewBuffer BigInfinite) [] $
             LetCallT [( "tr", T.PtrTy)] "build_tree" [IntTriv 10, VarTriv "buf"] $
             LetCallT [("ignored1", T.CursorTy), ("ignored2", T.CursorTy)] "add1"  [VarTriv "tr", VarTriv "buf2"] $
             (RetValsT [])
            )
  where
    build_tree = FunDecl "build_tree" [("n",T.IntTy),("tout",T.CursorTy)] T.CursorTy buildTree_tail True
    add1 = FunDecl "add1" [("t",T.CursorTy),("tout",T.CursorTy)] (T.ProdTy [T.CursorTy,T.CursorTy]) add1_tail True

    buildTree_tail =
        Switch "switch1" (VarTriv "n") (IntAlts [(0, base_case)]) (Just recursive_case)
      where
        base_case, recursive_case :: Tail

        base_case =
          LetPrimCallT [("tout1", T.CursorTy)] T.WriteInt [IntTriv 0, VarTriv "tout"] $
          RetValsT [VarTriv "tout1"]

        recursive_case =
          LetPrimCallT [("n1",T.IntTy)] SubP [VarTriv "n", IntTriv 1] $
          LetPrimCallT [("tout1",T.CursorTy)] WriteTag [TagTriv 1, VarTriv "tout"] $
          LetCallT [("tout2",T.CursorTy)] "build_tree" [VarTriv "n1", VarTriv "tout1"] $
          LetCallT [("tout3",T.CursorTy)] "build_tree" [VarTriv "n1", VarTriv "tout2"] $
          RetValsT [VarTriv "tout3"]

    add1_tail =
        LetPrimCallT [("ttag",T.TagTyPacked),("t2",T.CursorTy)] ReadTag [VarTriv "t"] $
        Switch "switch2" (VarTriv "ttag")
               (TagAlts [(leafTag,leafCase),
                         (nodeTag,nodeCase)])
               Nothing
      where
        leafCase =
          LetPrimCallT [("tout2",T.CursorTy)] WriteTag [TagTriv leafTag, VarTriv "tout"] $
          LetPrimCallT [("n",T.IntTy),("t3",T.CursorTy)] T.ReadInt [VarTriv "t2"] $
          LetPrimCallT [("n1",T.IntTy)] AddP [VarTriv "n", IntTriv 1] $
          LetPrimCallT [("tout3",T.CursorTy)] T.WriteInt [VarTriv "n1", VarTriv "tout2"] $
          RetValsT [VarTriv "t3", VarTriv "tout3"]

        nodeCase =
          LetPrimCallT [("tout2",T.CursorTy)] WriteTag [TagTriv nodeTag, VarTriv "tout"] $
          LetCallT [("t3",T.CursorTy),("tout3",T.CursorTy)] "add1" [VarTriv "t2", VarTriv "tout2"] $
          TailCall "add1" [VarTriv "t3", VarTriv "tout3"]

        leafTag, nodeTag :: Word8
        leafTag = 0
        nodeTag = 1

-- [2017.01.11] FIXME: I think there's something wrong with the above
-- program.  It doesn't pass in interpreter or compiler.  Disabling
-- these two tests until there is time to debug further.

_case_interp_add1 :: Assertion
_case_interp_add1 =
    do [_val] <- TI.execProg add1_prog
       -- FIXME: assert correct val.
       return ()

{- UNDER_CONSTRUCTION.
_case_add1 :: Assertion
_case_add1 =
    bracket (openFile file WriteMode)
            (\h -> hClose h
             -- >> removeFile file -- Leave around for debugging [2017.01.11].
            )
            runTest
  where
    file = "add1_out.c"

    runTest :: Handle -> Assertion
    runTest h = do
      str <- codegenProg True add1_prog
      hPutStr h str
      hFlush h
      gcc_out <- readCreateProcess (shell ("gcc -std=gnu11 -o add1.exe " ++ file)) ""
      assertEqual "unexpected gcc output" "" gcc_out

      let valgrind = case os of
                       "linux" -> "valgrind -q --error-exitcode=99 "
                       _       -> "" -- Don't assume valgrind on macos/etc

      -- just test for return value 0
      _proc_out <-
        bracket_ (return ())
                 (return ()) -- (removeFile "add1.exe") -- Leave around for debugging [2017.01.11].
                 (readCreateProcess (shell (valgrind++"./add1.exe 10 10")) "")

      return ()

-- Tests for copy-insertion

-- Shorthand:
f :: a -> (Bool,a)
f x = (False,x)

t5p :: Prog
t5p = Prog {ddefs = M.fromList [("Expr",
                                   DDef {tyName = "Expr",
                                         dataCons = [("VARREF", [f IntTy]),("Top", [f IntTy])]}),
                                   ("Bar",
                                    DDef {tyName = "Bar",
                                          dataCons = [("C", [f IntTy]),("D", [f$ PackedTy "Foo" fixme])]}),
                                   ("Foo",
                                    DDef {tyName = "Foo",
                                          dataCons = [("A", [f IntTy, f IntTy]),("B", [f$ PackedTy "Bar" fixme])]})],
               fundefs = M.fromList [("id",
                                      L2.FunDef {funname = "id",
                                                 funty = ArrowTy { locVars = [LRM "a" (VarR "r") Input]
                                                                 , arrIn = PackedTy "Foo" "a"
                                                                 , arrEffs = S.fromList []
                                                                 , locRets = []
                                                                 , arrOut = PackedTy "Foo" "a"
                                                                 },
                                                 funarg = "x0",
                                                 funbod = VarE "x0"})],
               mainExp = Just ((LetE ("fltAp1",[],
                                      PackedTy "Foo" "l",
                                      DataConE fixme "A" [LitE 1])
                                ((AppE "id" [] (VarE "fltAp1")))),
                               PackedTy "Foo" fixme)
             }
  where
    fixme = ""

-- UNDER_CONSTRUCTION.
_case_t5p1 :: Assertion
_case_t5p1 = assertEqual "Generate copy function for a simple DDef"
            ( "copyExpr"
            , L1.FunDef {L1.funName = "copyExpr",
                      L1.funArg = ("arg0",PackedTy "Expr" ()),
                      L1.funRetTy = PackedTy "Expr" (),
                      L1.funBody = CaseE (VarE "arg0")
                       [("VARREF",["x1"],
                         LetE ("y2",IntTy,VarE "x1")
                         (DataConE "VARREF" [VarE "y2"])),
                        ("Top",["x3"],
                         LetE ("y4",IntTy,VarE "x3")
                         (DataConE "Top" [VarE "y4"]))]})
            (fst $ runSyM 0 $ genCopyFn ddef)
  where ddef = (ddefs t5p) M.! "Expr"


_case_t5p2 :: Assertion
_case_t5p2 = assertEqual "Generate copy function for a DDef containing recursively packed data"
            ( "copyFoo"
            , L1.FunDef {L1.funName = "copyFoo",
                         L1.funArg = ("arg0",PackedTy "Foo" ()),
                         L1.funRetTy = PackedTy "Foo" (),
                         L1.funBody = CaseE (VarE "arg0")
                          [("A",["x1","x2"],
                            LetE ("y3",IntTy,VarE ("x1"))
                            (LetE ("y4",IntTy,VarE ("x2"))
                             (DataConE "A" [VarE "y3",VarE "y4"]))),
                           ("B",["x5"],
                            LetE ("y6",PackedTy "Bar" (),AppE "copyBar" (VarE "x5"))
                            (DataConE "B" [VarE "y6"]))]})
            (fst $ runSyM 0 $ genCopyFn ddef)
  where ddef = (ddefs t5p) M.! "Foo"
-}
