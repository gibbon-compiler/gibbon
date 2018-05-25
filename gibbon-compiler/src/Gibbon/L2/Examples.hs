{-# LANGUAGE OverloadedStrings #-}

module Gibbon.L2.Examples
  ( -- * Data definitions
    ddtree, stree

    -- * Functions
  , add1Fun, add1TraversedFun, id1Fun, copyTreeFun, id2Fun, id3Fun, intAddFun
  , leftmostFun, buildLeafFun, testProdFun

    -- * Programs
  , add1Prog, id1Prog, copyTreeProg, id2Prog, copyOnId1Prog, id3Prog, intAddProg
  , leftmostProg, buildLeafProg, testProdProg, nodeProg, leafProg, testFlattenProg
  , rightmostProg, buildTreeProg, buildTreeSumProg, printTupProg, addTreesProg
  , printTupProg2, buildSTreeProg, sumUpProg, setEvenProg, sumUpSetEvenProg, substProg
  , buildTwoTreesProg, sumTreeProg, sumSTreeProg, indrRightmostProg, indrBuildTreeProg
  , indrIDProg, indrIDSumProg
  ) where

import Data.Loc
import Data.Set as S
import Data.Map as M
-- import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L2.Syntax
import Gibbon.L1.Syntax hiding (FunDefs)
import Gibbon.GenericOps

ddtree :: DDefs Ty2
ddtree = fromListDD [DDef (toVar "Tree")
                      [ ("Leaf",[(False,IntTy)])
                      , ("Node",[ (False,PackedTy "Tree" "l")
                                , (False,PackedTy "Tree" "l")])
                      ]]


tTypeable :: L Exp2
tTypeable =  l$ Ext $ LetRegionE (VarR "r500") $
             l$ Ext $ LetLocE "l501" (StartOfLE (VarR "r500")) $
             l$ LetE ("v502",[], IntTy, l$ LitE 42) $
             l$ (VarE "v502")

testTypeable :: UrTy LocVar
testTypeable = gTypeExp ddtree emptyEnv2 tTypeable

--------------------------------------------------------------------------------
-- Add1

add1TraversedFun :: FunDef2
add1TraversedFun = FunDef "add1" "tr1" add1TraversedFunTy add1FunBod
  where add1TraversedFunTy = add1FunTy { arrEffs = S.fromList [Traverse "lin2"] }


add1Fun :: FunDef2
add1Fun = FunDef "add1" "tr1" add1FunTy add1FunBod


add1FunTy :: ArrowTy2
add1FunTy = (ArrowTy2
             [LRM "lin2" (VarR "r3") Input, LRM "lout4" (VarR "r750") Output]
             (PackedTy "Tree" "lin2")
             (S.empty)
             (PackedTy "Tree" "lout4")
             [])


add1FunBod :: L Exp2
add1FunBod = l$ CaseE (l$ VarE "tr1") $
  [ ("Leaf", [("n5","l6")],
      l$ LetE ("v7",[],IntTy,
               l$ PrimAppE AddP [l$ VarE "n5", l$ LitE 1]) $
      l$ LetE ("lf8",[],PackedTy "Tree" "lout4",
               l$ DataConE "lout4" "Leaf" [l$ VarE "v7"]) $
      l$ VarE "lf8")

  , ("Node", [("x9","l10"),("y11","l12")],
     l$ Ext $ LetLocE "l13" (AfterConstantLE 1 "lout4") $
     l$ LetE ("x14",[],PackedTy "Tree" "l13",
               l$ AppE "add1" ["l10","l13"] (l$ VarE "x9")) $
     l$ Ext $ LetLocE "l15" (AfterVariableLE "x14" "l13") $
     l$ LetE ("y16",[],PackedTy "Tree" "l15", l$ AppE "add1" ["l12","l15"] (l$ VarE "y11")) $
     l$ LetE ("z17",[],PackedTy "Tree" "lout4",
              l$ DataConE "lout4" "Node" [ l$ VarE "x14" , l$ VarE "y16"]) $
     l$ VarE "z17")
  ]

add1MainExp :: L Exp2
add1MainExp = l$ Ext $ LetRegionE (VarR "r99") $
              l$ Ext $ LetLocE "l100" (StartOfLE (VarR "r99")) $
              l$ Ext $ LetLocE "l101" (AfterConstantLE 1 "l100") $
              l$ LetE ("x102",[],PackedTy "Tree" "l101",
                      l$ DataConE "l101" "Leaf" [l$ LitE 1]) $
              l$ Ext $ LetLocE "l103" (AfterVariableLE "x102" "l101") $
              l$ LetE ("y104",[],PackedTy "Tree" "l103",
                      l$ DataConE "l103" "Leaf" [l$ LitE 2]) $
              l$ LetE ("z105",[],PackedTy "Tree" "l100",
                      l$ DataConE "l100" "Node" [l$ VarE "x102",
                                                 l$ VarE "y104"]) $
              l$ Ext $ LetRegionE (VarR "r106") $
              l$ Ext $ LetLocE "l107" (StartOfLE (VarR "r106")) $
              l$ LetE ("a108",[], PackedTy "Tree" "l107",
                      l$ AppE "add1" ["l100", "l107"] (l$ VarE "z105")) $
              l$ VarE "a108"


add1Prog :: Prog2
add1Prog = Prog ddtree (M.fromList [("add1", add1Fun)])
           (Just (add1MainExp, PackedTy "Tree" "l107"))

--------------------------------------------------------------------------------

leafMainExp :: L Exp2
leafMainExp = l$ Ext $ LetRegionE (VarR "r150") $
              l$ Ext $ LetLocE "l151" (StartOfLE (VarR "r150")) $
              l$ LetE ("x152",[],PackedTy "Tree" "l151",
                       l$ DataConE "l151" "Leaf" [l$ LitE 1]) $
              l$ VarE "x152"

leafProg :: Prog2
leafProg = Prog ddtree (M.empty) (Just (leafMainExp, PackedTy "Tree" "l151"))


--------------------------------------------------------------------------------

-- writes node
nodeMainExp :: L Exp2
nodeMainExp = l$ Ext $ LetRegionE (VarR "r155") $
               l$ Ext $ LetLocE "l156" (StartOfLE (VarR "r155")) $
               l$ Ext $ LetLocE "l157" (AfterConstantLE 1 "l156") $
               l$ LetE ("x158",[],PackedTy "Tree" "l157",
                       l$ DataConE "l157" "Leaf" [l$ LitE 1]) $
               l$ Ext $ LetLocE "l159" (AfterVariableLE "x158" "l157") $
               l$ LetE ("y160",[],PackedTy "Tree" "l159",
                       l$ DataConE "l159" "Leaf" [l$ LitE 2]) $
               l$ LetE ("z161",[],PackedTy "Tree" "l156",
                       l$ DataConE "l156" "Node" [l$ VarE "x158", l$ VarE "y160"]) $
               l$ VarE "z161"


nodeProg :: Prog2
nodeProg = Prog ddtree (M.empty) (Just (nodeMainExp, PackedTy "Tree" "l156"))

--------------------------------------------------------------------------------

id1Fun :: FunDef2
id1Fun = FunDef "id1" "tr18" idFunTy idFunBod
  where
    idFunBod = (l$ VarE "tr18")

    idFunTy :: ArrowTy2
    idFunTy = (ArrowTy2
               [LRM "lin19" (VarR "r20") Input, LRM "lout21" (VarR "r751") Output]
               (PackedTy "Tree" "lin19")
               (S.empty)
               (PackedTy "Tree" "lout21")
               [])


id1Prog :: Prog2
id1Prog = Prog ddtree (M.fromList [("id1", id1Fun)]) Nothing

--------------------------------------------------------------------------------

copyTreeFun :: FunDef2
copyTreeFun = FunDef "copyTree" "tr22" copyFunTy copyBod
  where
    copyFunTy = (ArrowTy2
                 [LRM "lin23" (VarR "r24") Input, LRM "lout25" (VarR "r752") Output]
                 (PackedTy "Tree" "lin23")
                 S.empty
                 (PackedTy "Tree" "lout25")
                 [])

    copyBod = l$ CaseE (l$ VarE "tr22") $
                 [ ("Leaf", [("n27","lin26")],
                     l$ LetE ("n28",[],PackedTy "Tree" "lout25",
                               l$ DataConE "lout25" "Leaf" [l$ VarE "n27"]) $
                     l$ VarE "n28")

                 , ("Node", [("x29","lx30"),("y31","ly32")],
                    l$ Ext  $ LetLocE "lx33" (AfterConstantLE 1 "lout25") $
                    l$ LetE ("x34", [], PackedTy "Tree" "lx33",
                             l$ AppE "copyTree" ["lx30","lx33"] (l$ VarE "x29")) $
                    l$ Ext  $ LetLocE "ly35" (AfterVariableLE "x34" "lx33") $
                    l$ LetE ("y36", [], PackedTy "Tree" "ly35",
                            l$ AppE "copyTree" ["ly32","ly35"] (l$ VarE "y31")) $
                    l$ DataConE "lout25" "Node" [l$ VarE "x34", l$ VarE "y36"])
                 ]

copyTreeMainExp :: L Exp2
copyTreeMainExp = l$ Ext $ LetRegionE (VarR "r200") $
                  l$ Ext $ LetLocE "l201" (StartOfLE (VarR "r200")) $
                  l$ Ext $ LetLocE "l202" (AfterConstantLE 1 "l201") $
                  l$ LetE ("x203",[],PackedTy "Tree" "l202",
                          l$ DataConE "l202" "Leaf" [l$ LitE 1]) $
                  l$ Ext $ LetLocE "r204" (AfterVariableLE "x203" "l202") $
                  l$ LetE ("y205",[],PackedTy "Tree" "r204",
                           l$ DataConE "r204" "Leaf" [l$ LitE 2]) $
                  l$ LetE ("z206",[],PackedTy "Tree" "l201",
                           l$ DataConE "l201" "Node" [l$ VarE "x203", l$ VarE "y205"]) $
                  l$ Ext $ LetRegionE (VarR "r207") $
                  l$ Ext $ LetLocE "l208" (StartOfLE (VarR "r207")) $
                  l$ LetE ("a209",[], PackedTy "Tree" "l208",
                           l$ AppE "copyTree" ["l201", "l208"] (l$ VarE "z206")) $
                  l$ VarE "a209"

copyTreeProg :: Prog2
copyTreeProg = Prog ddtree (M.fromList [("copyTree", copyTreeFun)]) $
               Just (copyTreeMainExp, PackedTy "Tree" "l208")

--------------------------------------------------------------------------------

id2Fun :: FunDef2
id2Fun = FunDef "id2" "tr41" id2Ty id2Bod
  where
    id2Ty :: ArrowTy2
    id2Ty = (ArrowTy2
             [LRM "lin37" (VarR "r38") Input, LRM "lout39" (VarR "r753") Output]
             (PackedTy "Tree" "lin37")
             (S.empty)
             (PackedTy "Tree" "lout39")
             [])

    id2Bod = l$ IfE (l$ PrimAppE EqIntP [l$ LitE 20, l$ LitE 20])
             (l$ (VarE "tr41"))
             (l$ (VarE "tr41"))

id2Prog :: Prog2
id2Prog = Prog ddtree (M.fromList [("id2", id2Fun)]) Nothing

--------------------------------------------------------------------------------

copyOnId1Prog :: Prog2
copyOnId1Prog = Prog ddtree funs $ Just (copyOnId1MainExp, PackedTy "Tree" "l228")
  where
    funs  = (M.fromList [("copyTree" , copyTreeFun),
                         ("id1WithCopy", id1WithCopyFun)])

copyOnId1MainExp :: L Exp2
copyOnId1MainExp = l$ Ext $ LetRegionE (VarR "r220") $
                   l$ Ext $ LetLocE "l221" (StartOfLE (VarR "r220")) $
                   l$ Ext $ LetLocE "l222" (AfterConstantLE 1 "l221") $
                   l$ LetE ("l223",[],PackedTy "Tree" "l222",
                           l$ DataConE "l222" "Leaf" [l$ LitE 1]) $
                   l$ Ext $ LetLocE "l224" (AfterVariableLE "l223" "l222") $
                   l$ LetE ("l225",[],PackedTy "Tree" "l224",
                            l$ DataConE "l224" "Leaf" [l$ LitE 2]) $
                   l$ LetE ("z226",[],PackedTy "Tree" "l221",
                            l$ DataConE "l221" "Node" [l$ VarE "l223", l$ VarE "l225"]) $
                   l$ Ext $ LetRegionE (VarR "r227") $
                   l$ Ext $ LetLocE "l228" (StartOfLE (VarR "r227")) $
                   l$ LetE ("a229",[], PackedTy "Tree" "l228",
                            l$ AppE "id1WithCopy" ["l221", "l228"] (l$ VarE "z226")) $
                   l$ VarE "a229"

id1WithCopyFun :: FunDef2
id1WithCopyFun = id1Fun { funBody = l$ AppE "copyTree" ["lin19","lout21"]
                                   (l$ VarE "tr18")
                        , funName = "id1WithCopy"
                        }

--------------------------------------------------------------------------------

id3Fun :: FunDef2
id3Fun = FunDef "id3" "i42" id3Ty id3Bod
  where
    id3Ty :: ArrowTy2
    id3Ty = (ArrowTy2
             []
             (IntTy)
             (S.empty)
             (IntTy)
             [])
    id3Bod = l$ VarE "i42"

id3MainExp :: L Exp2
id3MainExp = l$ AppE "id3" [] (l$ LitE 42)

id3Prog :: Prog2
id3Prog = Prog ddtree (M.fromList [("id3", id3Fun)]) $ Just (id3MainExp, IntTy)


--------------------------------------------------------------------------------

intAddFun :: FunDef2
intAddFun = FunDef "intAdd" "i109" intAddTy id3Bod
  where
    intAddTy :: ArrowTy2
    intAddTy = (ArrowTy2
                []
                (ProdTy [IntTy, IntTy])
                (S.empty)
                (IntTy)
                [])
    id3Bod = l$ PrimAppE AddP [l$ ProjE 0 (l$ VarE "i109"), l$ ProjE 1 (l$ VarE "i109")]

intAddMainExp :: L Exp2
intAddMainExp = l$ LetE ("sum110", [], IntTy,
                         l$ AppE "intAdd" []
                         (l$ MkProdE [l$LitE 40,l$LitE 2])) $
                l$ (VarE "sum110")

intAddProg :: Prog2
intAddProg = Prog M.empty (M.fromList [("intAdd", intAddFun)]) (Just (intAddMainExp, IntTy))

--------------------------------------------------------------------------------

leftmostFun :: FunDef2
leftmostFun = FunDef "leftmost" "t111" leftmostTy leftmostBod
  where
    leftmostTy :: ArrowTy2
    leftmostTy = (ArrowTy2
                 [LRM "lin112" (VarR "r113") Input]
                 (PackedTy "Tree" "lin112")
                 (S.empty)
                 (IntTy)
                 [])

leftmostBod :: L Exp2
leftmostBod = l$ CaseE (l$ VarE "t111")
              [("Leaf", [("n114","l115")],
                l$ VarE "n114"),
               ("Node", [("x117","l118"), ("y119","l120")],
                l$ LetE ("lm121",[],IntTy, l$ AppE "leftmost" ["l118"] (l$ VarE "x117")) $
                l$ VarE "lm121")]

leftmostMainExp :: L Exp2
leftmostMainExp = l$ Ext $ LetRegionE (VarR "r122") $
                  l$ Ext $ LetLocE "l123" (StartOfLE (VarR "r122")) $
                  l$ Ext $ LetLocE "l124" (AfterConstantLE 1 "l123") $
                  l$ LetE ("x125",[],PackedTy "Tree" "l124",
                          l$ DataConE "l124" "Leaf" [l$ LitE 1]) $
                  l$ Ext $ LetLocE "l126" (AfterVariableLE "x125" "l124") $
                  l$ LetE ("y128",[],PackedTy "Tree" "l126",
                          l$ DataConE "l126" "Leaf" [l$ LitE 2]) $
                  l$ LetE ("z127",[],PackedTy "Tree" "l123",
                          l$ DataConE "l123" "Node" [l$ VarE "x125", l$ VarE "y128"]) $
                  l$ LetE ("a131",[], IntTy,
                          l$ AppE "leftmost" ["l123"] (l$ VarE "z127")) $
                  l$ VarE "a131"

leftmostProg :: Prog2
leftmostProg = Prog ddtree (M.fromList [("leftmost", leftmostFun)]) (Just (leftmostMainExp, IntTy))


--------------------------------------------------------------------------------

rightmostFun :: FunDef2
rightmostFun = FunDef "rightmost" "t242" rightmostTy rightmostBod
  where
    rightmostTy :: ArrowTy2
    rightmostTy = (ArrowTy2
                   [LRM "lin241" (VarR "r240") Input]
                   (PackedTy "Tree" "lin241")
                   (S.empty)
                   (IntTy)
                   [])

rightmostBod :: L Exp2
rightmostBod = l$ CaseE (l$ VarE "t242")
               [("Leaf", [("n246","l247")],
                 l$ VarE "n246"),
                ("Node", [("x248","l249"), ("y250","l251")],
                 -- l$ Ext $ LetRegionE (VarR "r252") $
                 -- l$ Ext $ LetLocE "l253" (StartOfLE (VarR "r252")) $
                 -- l$ LetE ("x254",[],PackedTy "Tree" "l253",
                 --          l$ AppE "copyTree" ["l249", "l253"] (l$ VarE "x248")) $
                 l$ AppE "rightmost" ["l251"] (l$ VarE "y250")
                )]

rightmostMainExp :: L Exp2
rightmostMainExp = l$ Ext $ LetRegionE (VarR "r253") $
                   l$ Ext $ LetLocE "l254" (StartOfLE (VarR "r253")) $
                   l$ Ext $ LetLocE "l255" (AfterConstantLE 1 "l254") $
                   l$ LetE ("x256",[],PackedTy "Tree" "l255",
                            l$ DataConE "l255" "Leaf" [l$ LitE 1]) $
                   l$ Ext $ LetLocE "l257" (AfterVariableLE "x256" "l255") $
                   l$ LetE ("y258",[],PackedTy "Tree" "l257",
                            l$ DataConE "l257" "Leaf" [l$ LitE 2]) $
                   l$ LetE ("z259",[],PackedTy "Tree" "l254",
                            l$ DataConE "l254" "Node" [l$ VarE "x256", l$ VarE "y258"]) $
                   l$ LetE ("a260",[], IntTy,
                            l$ AppE "rightmost" ["l254"] (l$ VarE "z259")) $
                   l$ VarE "a260"

rightmostProg :: Prog2
rightmostProg = Prog ddtree (M.fromList [("rightmost", rightmostFun)])
                (Just (rightmostMainExp, IntTy))


--------------------------------------------------------------------------------

buildLeafFun :: FunDef2
buildLeafFun = FunDef "buildLeaf" "i125" buildLeafTy buildLeafBod
  where
    buildLeafTy :: ArrowTy2
    buildLeafTy = (ArrowTy2
                   [LRM "lout126" (VarR "r127") Output]
                   (IntTy)
                   (S.empty)
                   (PackedTy "Tree" "lout126")
                   [])

    buildLeafBod :: L Exp2
    buildLeafBod = l$ DataConE "lout126" "Leaf" [l$ VarE "i125"]


buildLeafMainExp :: L Exp2
buildLeafMainExp = l$ Ext $ LetRegionE (VarR "r128") $
                   l$ Ext $ LetLocE "l129" (StartOfLE (VarR "r128")) $
                   l$ AppE "buildLeaf" ["l129"] (l$ LitE 42)

buildLeafProg :: Prog2
buildLeafProg = Prog ddtree (M.fromList [("buildLeaf", buildLeafFun)]) (Just (buildLeafMainExp, PackedTy "Tree" "l129"))


--------------------------------------------------------------------------------

buildTreeFun :: FunDef2
buildTreeFun = FunDef "buildTree" "i270" buildTreeTy buildTreeBod
  where
    buildTreeTy :: ArrowTy2
    buildTreeTy = (ArrowTy2
                   [LRM "lout272" (VarR "r271") Output]
                   (IntTy)
                   (S.empty)
                   (PackedTy "Tree" "lout272")
                   [])

    buildTreeBod :: L Exp2
    buildTreeBod = l$ LetE ("b279",[], BoolTy, l$ PrimAppE EqIntP [l$ VarE "i270", l$ LitE 0]) $
                   l$ IfE (l$ VarE "b279")
                   (l$ DataConE "lout272" "Leaf" [l$ LitE 1])
                   (l$ LetE ("i273",[], IntTy, l$ PrimAppE SubP [l$ VarE "i270", l$ LitE 1]) $
                    l$ Ext $ LetLocE "l274" (AfterConstantLE 1 "lout272") $
                    l$ LetE ("x275",[],PackedTy "Tree" "l274",
                             l$ AppE "buildTree" ["l274"] (l$ VarE "i273")) $
                    l$ Ext $ LetLocE "l276" (AfterVariableLE "x275" "l274") $
                    l$ LetE ("y277",[],PackedTy "Tree" "l276",
                             l$ AppE "buildTree" ["l276"] (l$ VarE "i273")) $
                    l$ LetE ("a278",[],PackedTy "Tree" "lout272",
                             l$ DataConE "lout272" "Node" [l$ VarE "x275", l$ VarE "y277"]) $
                    l$ VarE "a278")


buildTreeMainExp :: L Exp2
buildTreeMainExp = l$ Ext $ LetRegionE (VarR "r279") $
                   l$ Ext $ LetLocE "l280" (StartOfLE (VarR "r279")) $
                   l$ AppE "buildTree" ["l280"] (l$ LitE 3)

buildTreeProg :: Prog2
buildTreeProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun)]) (Just (buildTreeMainExp, PackedTy "Tree" "l280"))


--------------------------------------------------------------------------------


buildTwoTreesFun :: FunDef2
buildTwoTreesFun = FunDef "buildTwoTrees" "i750" buildTreeTy buildTreeBod
  where
    buildTreeTy :: ArrowTy2
    buildTreeTy = (ArrowTy2
                   [LRM "lout752" (VarR "r751") Output, LRM "lout754" (VarR "r753") Output]
                   (IntTy)
                   (S.empty)
                   (ProdTy [PackedTy "Tree" "lout752", PackedTy "Tree" "lout754"])
                   [])

    buildTreeBod :: L Exp2
    buildTreeBod = l$ LetE ("tree1",[],PackedTy "Tree" "lout752",
                            l$ AppE "buildTree" ["lout752"] (l$ VarE "i750")) $
                   l$ LetE ("tree2",[],PackedTy "Tree" "lout754",
                            l$ AppE "buildTree" ["lout754"] (l$ VarE "i750")) $
                   l$ LetE ("a755",[], ProdTy [PackedTy "Tree" "lout752", PackedTy "Tree" "lout754"],
                            l$ MkProdE [l$ VarE "tree1", l$ VarE "tree2"]) $
                   l$ VarE "a755"

buildTwoTreesMainExp :: L Exp2
buildTwoTreesMainExp = l$ Ext $ LetRegionE (VarR "r756") $
                       l$ Ext $ LetLocE "l757" (StartOfLE (VarR "r756")) $
                       l$ Ext $ LetRegionE (VarR "r758") $
                       l$ Ext $ LetLocE "l759" (StartOfLE (VarR "r758")) $
                       l$ LetE ("treeprod", [], ProdTy [PackedTy "Tree" "lout757", PackedTy "Tree" "lout759"],
                                l$ AppE "buildTwoTrees" ["l757", "l759"] (l$ LitE 2)) $
                       l$ VarE "treeprod"

buildTwoTreesProg :: Prog2
buildTwoTreesProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun),
                                             ("buildTwoTrees", buildTwoTreesFun)])
                         (Just (buildTwoTreesMainExp, ProdTy [PackedTy "Tree" "lout757", PackedTy "Tree" "lout759"]))

--------------------------------------------------------------------------------

buildTreeSumFun :: FunDef2
buildTreeSumFun = FunDef "buildTreeSum" "i302" buildTreeSumTy buildTreeSumBod
  where
    buildTreeSumTy :: ArrowTy2
    buildTreeSumTy = (ArrowTy2
                      [LRM "lout301" (VarR "r300") Output]
                      (IntTy)
                      (S.empty)
                      (ProdTy [IntTy, PackedTy "Tree" "lout301"])
                      [])

    buildTreeSumBod :: L Exp2
    buildTreeSumBod = l$ LetE ("b303",[], BoolTy, l$ PrimAppE EqIntP [l$ VarE "i302", l$ LitE 0]) $
                      l$ IfE (l$ VarE "b303")
                      (l$ LetE ("c316",[],PackedTy "Tree" "lout301",
                                l$ DataConE "lout301" "Leaf" [l$ LitE 1]) $
                       l$ LetE ("t317",[],ProdTy [IntTy, PackedTy "Tree" "lout301"],
                               l$ MkProdE [l$ LitE 1, l$ VarE "c316"]) $
                       l$ VarE "t317")
                      (l$ LetE ("i303",[], IntTy, l$ PrimAppE SubP [l$ VarE "i302", l$ LitE 1]) $
                       l$ Ext $ LetLocE "l304" (AfterConstantLE 1 "lout301") $
                       l$ LetE ("t318",[],ProdTy [IntTy, PackedTy "Tree" "l304"],
                                l$ AppE "buildTreeSum" ["l304"] (l$ VarE "i303")) $
                       l$ LetE ("i309",[],IntTy, l$ ProjE 0 (l$ VarE "t318")) $
                       l$ LetE ("x305",[],PackedTy "Tree" "l304", l$ ProjE 1 (l$ VarE "t318")) $
                       l$ Ext $ LetLocE "l306" (AfterVariableLE "x305" "l304") $
                       l$ LetE ("t319",[],ProdTy [IntTy, PackedTy "Tree" "l306"],
                                l$ AppE "buildTreeSum" ["l306"] (l$ VarE "i303")) $
                       l$ LetE ("i310",[],IntTy, l$ ProjE 0 (l$ VarE "t319")) $
                       l$ LetE ("y307",[],PackedTy "Tree" "l306", l$ ProjE 1 (l$ VarE "t319")) $
                       l$ LetE ("j311",[],IntTy, l$ PrimAppE AddP [l$ VarE "i309", l$ VarE "i310"]) $
                       l$ LetE ("a308",[],PackedTy "Tree" "lout301",
                                l$ DataConE "lout301" "Node" [l$ VarE "x305", l$ VarE "y307"]) $
                       l$ LetE ("b312",[], ProdTy [IntTy, PackedTy "Tree" "lout301"],
                                l$ MkProdE [l$ VarE "j311", l$ VarE "a308"]) $
                       l$ VarE "b312")


buildTreeSumMainExp :: L Exp2
buildTreeSumMainExp = l$ Ext $ LetRegionE (VarR "r313") $
                      l$ Ext $ LetLocE "l314" (StartOfLE (VarR "r313")) $
                      l$ LetE ("z315",[],ProdTy [IntTy, PackedTy "Tree" "l314"],
                               l$ AppE "buildTreeSum" ["l314"] (l$ LitE 3)) $
                      l$ VarE "z315"


buildTreeSumProg :: Prog2
buildTreeSumProg = Prog ddtree (M.fromList [("buildTreeSum", buildTreeSumFun)]) (Just (buildTreeSumMainExp, ProdTy [IntTy, PackedTy "Tree" "l314"]))

--------------------------------------------------------------------------------

sumTreeFun :: FunDef2
sumTreeFun = FunDef "sumTree" "tr762" sumTreeTy sumTreeBod
  where
    sumTreeTy :: ArrowTy2
    sumTreeTy = (ArrowTy2
                      [LRM "lin761" (VarR "r760") Input]
                      (PackedTy "Tree" "lin761")
                      (S.empty)
                      (IntTy)
                      [])

    sumTreeBod :: L Exp2
    sumTreeBod = l$ CaseE (l$ VarE "tr762")
                 [ ("Leaf", [("n763", "l764")],
                   l$ VarE "n763")
                 , ("Node", [("x764","l765"), ("y766","l767")],
                   l$ LetE ("sx768", [], IntTy,
                            l$ AppE "sumTree" ["l765"] (l$ VarE "x764")) $
                   l$ LetE ("sy769", [], IntTy,
                            l$ AppE "sumTree" ["l767"] (l$ VarE "y766")) $
                   l$ LetE ("total770", [], IntTy ,
                            l$ PrimAppE AddP [l$ VarE "sx768", l$ VarE "sy769"]) $
                   l$ VarE "total770"
                   )]

sumTreeMainExp :: L Exp2
sumTreeMainExp = l$ Ext $ LetRegionE (VarR "r771") $
                 l$ Ext $ LetLocE "l772" (StartOfLE (VarR "r771")) $
                 l$ LetE ("tr773", [], PackedTy "Tree" "l772",
                          l$ AppE "buildTree" ["l772"] (l$ LitE 3)) $
                 l$ LetE ("sum774", [], IntTy,
                          l$ AppE "sumTree" ["l772"] (l$ VarE "tr773")) $
                 l$ VarE "sum774"

sumTreeProg :: Prog2
sumTreeProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun),
                                       ("sumTree", sumTreeFun)
                                      ])
                   (Just (sumTreeMainExp, IntTy))

--------------------------------------------------------------------------------

printTupMainExp :: L Exp2
printTupMainExp = l$ Ext $ LetRegionE (VarR "r325") $
                  l$ Ext $ LetLocE "l326" (StartOfLE (VarR "r325")) $
                  l$ LetE ("i327",[], IntTy, l$ LitE 42) $
                  l$ LetE ("x328",[], PackedTy "Tree" "l326",
                           l$ DataConE "l326" "Leaf" [l$ LitE 1]) $
                  l$ LetE ("t329",[], ProdTy [IntTy, PackedTy "Tree" "l326"],
                           l$ MkProdE [l$ VarE "i327", l$ VarE "x328"]) $
                  l$ VarE "t329"

printTupProg :: Prog2
printTupProg = Prog ddtree M.empty (Just (printTupMainExp, ProdTy [IntTy, PackedTy "Tree" "l326"]))

--------------------------------------------------------------------------------

printTupMainExp2 :: L Exp2
printTupMainExp2 = l$ Ext $ LetRegionE (VarR "r400") $
                  l$ Ext $ LetLocE "l401" (StartOfLE (VarR "r400")) $
                  l$ LetE ("x402",[], PackedTy "Tree" "l401",
                           l$ AppE "buildTree" ["l401"] (l$ LitE 2)) $
                  l$ Ext $ LetLocE "l403" (AfterVariableLE "x402" "l401") $
                  l$ LetE ("y404",[], PackedTy "Tree" "l403",
                           l$ AppE "buildTree" ["l403"] (l$ LitE 1)) $
                  l$ LetE ("z405",[], ProdTy [PackedTy "Tree" "l401", PackedTy "Tree" "l403"],
                           l$ MkProdE [l$ VarE "x402", l$ VarE "y404"]) $
                  l$ VarE "z405"

printTupProg2 :: Prog2
printTupProg2 = Prog ddtree (M.fromList [("buildTree", buildTreeFun)])
                (Just (printTupMainExp2,
                       ProdTy [PackedTy "Tree" "l401", PackedTy "Tree" "l403"]))

--------------------------------------------------------------------------------

{-

addTrees :: Tree -> Tree -> Tree
addTrees t1 t2 =
  case t1 of
    Leaf n1    -> case t2 of
                    Leaf n2 -> Leaf (n1 + n2)
                    Node l2 r2 -> error "expected leaf here"
    Node l1 r1 -> case t2 of
                    Leaf n2 -> error "expected node here"
                    Node l2 r2 -> Node (addTrees l1 l2) (addTrees r1 r2)
-}

addTreesFun :: FunDef2
addTreesFun = FunDef "addTrees" "trees354" addTreesTy addTreesBod
  where
    addTreesTy :: ArrowTy2
    addTreesTy = (ArrowTy2
                  [LRM "lin351" (VarR "r350") Input,
                   LRM "lin352" (VarR "r351") Input,
                   LRM "lout353" (VarR "r754") Output]
                  (ProdTy [PackedTy "Tree" "lin351", PackedTy "Tree" "lin352"])
                  (S.empty)
                  (PackedTy "Tree" "lout353")
                  [])

    addTreesBod :: L Exp2
    addTreesBod = l$ LetE ("tree1",[],PackedTy "Tree" "lin351",
                           l$ ProjE 0 (l$ VarE "trees354")) $
                  l$ LetE ("tree2",[],PackedTy "Tree" "lin352",
                           l$ ProjE 1 (l$ VarE "trees354")) $
                  l$ CaseE (l$ VarE "tree1")
                  [("Leaf", [("n355","l356")],
                    l$ CaseE (l$ VarE "tree2")
                       [("Leaf",[("n357","l358")],
                         l$ LetE ("n358",[],IntTy,l$ PrimAppE AddP [l$ VarE "n355",l$ VarE "n357"]) $
                         l$ LetE ("x359",[],PackedTy "Tree" "lout353",
                                  l$ DataConE "lout353" "Leaf" [l$ VarE "n358"]) $
                         l$ VarE "x359"
                        )]
                   ),
                    ("Node", [("x360","l361"), ("y362","l363")],
                     l$ CaseE (l$ VarE "tree2")
                        [("Node", [("x364","l365"), ("y366","l367")],
                          l$ Ext $ LetLocE "l368" (AfterConstantLE 1 "lout353") $
                          l$ LetE ("tree3",[],ProdTy [PackedTy "Tree" "l361",
                                                      PackedTy "Tree" "l365"],
                                   l$ MkProdE [l$ VarE "x360", l$ VarE "x364"]) $
                          l$ LetE ("x369",[],PackedTy "Tree" "l368",
                                   l$ AppE "addTrees" ["l361","l365","l368"] (l$ VarE "tree3")) $
                          l$ Ext $ LetLocE "l370" (AfterVariableLE "x369" "l368") $
                          l$ LetE ("tree4",[],ProdTy [PackedTy "Tree" "l363",
                                                      PackedTy "Tree" "l367"],
                                   l$ MkProdE [l$ VarE "y362", l$ VarE "y366"]) $
                          l$ LetE ("y371",[],PackedTy "Tree" "l370",
                                   l$ AppE "addTrees" ["l363","l367","l370"] (l$ VarE "tree4")) $
                          l$ LetE ("z372",[],PackedTy "Tree" "lout353",
                                    l$ DataConE "lout353" "Node" [l$ VarE "x369", l$ VarE "y371"]) $
                          l$ VarE "z372"
                         )]
                    )]

addTreesMainExp :: L Exp2
addTreesMainExp = l$ Ext $ LetRegionE (VarR "r400") $
                  l$ Ext $ LetLocE "l401" (StartOfLE (VarR "r400")) $
                  l$ LetE ("x402",[], PackedTy "Tree" "l401",
                           l$ AppE "buildTree" ["l401"] (l$ LitE 2)) $
                  -- l$ Ext $ LetLocE "l403" (AfterVariableLE "x402" "l401") $
                  l$ Ext $ LetRegionE (VarR "r403") $
                  l$ Ext $ LetLocE "l403" (StartOfLE (VarR "r403")) $
                  l$ LetE ("y404",[], PackedTy "Tree" "l403",
                           l$ AppE "buildTree" ["l403"] (l$ LitE 2)) $
                  l$ LetE ("z405",[], ProdTy [PackedTy "Tree" "l401", PackedTy "Tree" "l403"],
                           l$ MkProdE [l$ VarE "x402", l$ VarE "y404"]) $
                  l$ Ext $ LetRegionE (VarR "r405") $
                  l$ Ext $ LetLocE "l406" (StartOfLE (VarR "r405")) $
                  l$ LetE ("a407",[],PackedTy "Tree" "l406",
                           l$ AppE "addTrees" ["l401","l403","l406"] (l$ VarE "z405")) $
                  l$ VarE "a407"

addTreesProg :: Prog2
addTreesProg = Prog ddtree (M.fromList [("addTrees", addTreesFun)
                                       ,("buildTree", buildTreeFun)])
                    (Just (addTreesMainExp, PackedTy "Tree" "l406"))

--------------------------------------------------------------------------------

testProdFun :: FunDef2
testProdFun = FunDef "testprod" "tup130" testprodTy testprodBod
  where
    testprodTy = (ArrowTy2
                  [LRM "lin131" (VarR "r132") Input, LRM "lout133" (VarR "r755") Output]
                  (ProdTy [(PackedTy "Tree" "lin131"), IntTy])
                  (S.empty)
                  (ProdTy [(PackedTy "Tree" "lout133"), IntTy])
                  [])
    testprodBod = l$ LetE ("t134",[], PackedTy "Tree" "lin131", l$ ProjE 0 (l$ VarE "tup130")) $
                  l$ LetE ("i135",[], IntTy, l$ ProjE 1 (l$ VarE "tup130")) $
                  l$ CaseE (l$ VarE "t134")
                  [("Leaf",[("n136","l137")],
                    l$ LetE ("v138",[],IntTy, l$ PrimAppE AddP [l$ VarE "n136", l$ LitE 1]) $
                    l$ LetE ("lf139",[],PackedTy "Tree" "lout133",
                            l$ DataConE "lout133" "Leaf" [l$ VarE "v138"]) $
                    l$ LetE ("tup148",[], ProdTy [PackedTy "Tree" "lout133", IntTy],
                       l$ MkProdE [l$ VarE "lf139", l$ VarE "i135"]) $
                    l$ VarE "tup148"
                   ),
                   ("Node",[("x140","l141"), ("y142","l143")],
                    l$ Ext $ LetLocE "l144" (AfterConstantLE 1 "lout133") $
                    l$ LetE ("tup145",[], ProdTy [PackedTy "Tree" "l144", IntTy],
                             l$ AppE "testprod" ["l141","l144"]
                             (l$ MkProdE [l$ VarE "x140", l$ VarE "i135"])) $

                    l$ LetE ("x149",[], PackedTy "Tree" "l144", l$ ProjE 0 (l$ VarE "tup145")) $
                    l$ Ext $ LetLocE "l146" (AfterVariableLE "x149" "l144") $
                    l$ LetE ("tup147",[], ProdTy [PackedTy "Tree" "l146", IntTy],
                            l$ AppE "testprod" ["l143","l146"]
                            (l$ MkProdE [l$ VarE "y142", l$ VarE "i135"])) $
                    l$ LetE ("y150",[], PackedTy "Tree" "l146", l$ ProjE 0 (l$ VarE "tup147")) $
                    l$ LetE ("node151",[], PackedTy "Tree" "lout133",
                            l$ DataConE "lout133" "Node" [l$ VarE "x149", l$ VarE "y150"]) $
                    l$ LetE ("tup152",[],ProdTy [PackedTy "Tree" "lout133", IntTy],
                            l$ MkProdE [l$ VarE "node151", l$ VarE "i135"]) $
                    l$ VarE "tup152")
                  ]

testProdProg :: Prog2
testProdProg = Prog ddtree (M.fromList [("testprod", testProdFun)]) Nothing

--------------------------------------------------------------------------------

-- Meaningless program, just to test flattenL2
testFlattenProg :: Prog2
testFlattenProg = Prog M.empty (M.fromList [("intAdd",intAddFun)]) $ Just (testFlattenBod, IntTy)
  where
    testFlattenBod :: L Exp2
    testFlattenBod =
      l$ Ext $ LetRegionE (VarR "_") $
      l$ Ext $ LetLocE "_" (StartOfLE (VarR "_")) $
      l$ Ext $ LetLocE "_" (AfterConstantLE 1 "_") $
      l$ LetE ("v170",[],IntTy,
               l$ LetE ("v171",[],IntTy,
                        l$ AppE "intAdd" []
                        (l$ MkProdE [l$ PrimAppE AddP [l$ LitE 40, l$ LitE 2],
                                     l$ PrimAppE SubP [l$ LitE 44, l$ LitE 2]])) $
                l$ VarE "v171") $
      l$ VarE "v170"

--------------------------------------------------------------------------------

-- sumUp + setEven example in L2
-- gensym starts at 500

stree :: DDefs Ty2
stree = fromListDD [DDef (toVar "STree")
                    [ ("Leaf",[(False,IntTy)])
                    , ("Inner",[ (False, IntTy)
                               , (False, IntTy) -- this should be a boolean.
                                                -- for now, 1 is true, 0 is false
                               , (False, PackedTy "STree" "l")
                               , (False, PackedTy "STree" "l")])
                    ]]

{-

sumUp :: Tree -> Tree
sumUp tree =
  case tree of
    Leaf x -> Leaf x
    Inner sum x l r ->
      let l'   = sum_up l
          r'   = sum_up r
          v1   = value l'
          v2   = value  r'
          sum' = v1 + v2
      in Inner sum' x l' r'

-}

sumUpFun :: FunDef2
sumUpFun = FunDef "sumUp" "tr1" sumUpFunTy sumUpFunBod
  where
    sumUpFunTy :: ArrowTy2
    sumUpFunTy = (ArrowTy2
                  [LRM "lin501" (VarR "r500") Input, LRM "lout502" (VarR "r756") Output]
                  (PackedTy "STree" "lin501")
                  (S.empty)
                  (PackedTy "STree" "lout502")
                  [])


    sumUpFunBod :: L Exp2
    sumUpFunBod = l$ CaseE (l$ VarE "tr1") $
      [ ("Leaf", [("n503","l504")],
          l$ LetE ("x505",[],PackedTy "STree" "lout502",
                   l$ DataConE "lout502" "Leaf" [l$ VarE "n503"]) $
          l$ VarE "x505")

      , ("Inner", [("i506","l507"),("b508","l509"),("x510","l511"),("y512","l513")],
         l$ Ext $ LetLocE "l514" (AfterConstantLE 1 "lout502") $
         l$ Ext $ LetLocE "l550" (AfterVariableLE "i506" "l514") $
         l$ Ext $ LetLocE "l551" (AfterVariableLE "b508" "l550") $
         l$ LetE ("x515",[],PackedTy "STree" "l551",
                   l$ AppE "sumUp" ["l511","l551"] (l$ VarE "x510")) $
         l$ Ext $ LetLocE "l516" (AfterVariableLE "x515" "l551") $
         l$ LetE ("y517",[],PackedTy "STree" "l516",
                  l$ AppE "sumUp" ["l513","l516"] (l$ VarE "y512")) $
         l$ LetE ("v518",[],IntTy, l$ AppE "valueSTree" ["l551"] (l$ VarE "x515")) $
         l$ LetE ("v519",[],IntTy, l$ AppE "valueSTree" ["l516"] (l$ VarE "y517")) $
         l$ LetE ("v520",[],IntTy, l$ PrimAppE AddP [l$ VarE "v518", l$ VarE "v519"]) $
         l$ LetE ("z521",[],PackedTy "STree" "lout502",
                  l$ DataConE "lout502" "Inner" [l$ VarE "v520", l$ VarE "b508",
                                                 l$ VarE "x515", l$ VarE "y517"]) $
         l$ VarE "z521"
        )]


valueSTreeFun :: FunDef2
valueSTreeFun = FunDef "valueSTree" "tr522" valueSTreeFunTy valueSTreeFunBod
  where
    valueSTreeFunTy :: ArrowTy2
    valueSTreeFunTy = (ArrowTy2
                       [LRM "lin524" (VarR "r523") Input]
                       (PackedTy "STree" "lin524")
                       (S.empty)
                       (IntTy)
                       [])

    valueSTreeFunBod :: L Exp2
    valueSTreeFunBod = l$ CaseE (l$ VarE "tr522") $
      [ ("Leaf", [("n523","l524")],
          l$ VarE "n523")

      , ("Inner", [("i525","l526"),("b527","l528"),("x529","l530"),("y531","l532")],
         l$ VarE "i525"
      )]


buildSTreeFun :: FunDef2
buildSTreeFun = FunDef "buildSTree" "i543" buildSTreeTy buildSTreeBod
  where
    buildSTreeTy :: ArrowTy2
    buildSTreeTy = (ArrowTy2
                    [LRM "lout541" (VarR "r540") Output]
                    (IntTy)
                    (S.empty)
                    (PackedTy "STree" "lout541")
                    [])

    buildSTreeBod :: L Exp2
    buildSTreeBod = l$ LetE ("b542",[], BoolTy, l$ PrimAppE EqIntP [l$ VarE "i543", l$ LitE 0]) $
                   l$ IfE (l$ VarE "b542")
                   (l$ DataConE "lout541" "Leaf" [l$ LitE 1])
                   (l$ LetE ("i548",[], IntTy, l$ PrimAppE SubP [l$ VarE "i543", l$ LitE 1]) $
                    l$ LetE ("i554",[], IntTy, l$ LitE 0) $
                    l$ LetE ("b555",[], IntTy, l$ LitE 0) $
                    l$ Ext $ LetLocE "l544" (AfterConstantLE 1 "lout541") $
                    l$ Ext $ LetLocE "l552" (AfterVariableLE "i554" "l544") $
                    l$ Ext $ LetLocE "l553" (AfterVariableLE "b555" "l552") $
                    l$ LetE ("x545",[],PackedTy "STree" "l553",
                             l$ AppE "buildSTree" ["l553"] (l$ VarE "i548")) $
                    l$ Ext $ LetLocE "l545" (AfterVariableLE "x545" "l553") $
                    l$ LetE ("y546",[],PackedTy "STree" "l545",
                             l$ AppE "buildSTree" ["l545"] (l$ VarE "i548")) $
                    l$ LetE ("a547",[],PackedTy "STree" "lout541",
                             l$ DataConE "lout541" "Inner" [l$ VarE "i554", l$ VarE "b555",
                                                            l$ VarE "x545", l$ VarE "y546"]) $
                    l$ VarE "a547")


buildSTreeMainExp :: L Exp2
buildSTreeMainExp = l$ Ext $ LetRegionE (VarR "r530") $
                    l$ Ext $ LetLocE "l531" (StartOfLE (VarR "r530")) $
                    l$ LetE ("x532",[], PackedTy "STree" "l531",
                             l$ AppE "buildSTree" ["l531"] (l$ LitE 3)) $
                    l$ VarE "x532"


buildSTreeProg :: Prog2
buildSTreeProg = Prog stree (M.fromList [("buildSTree", buildSTreeFun)])
                      (Just (buildSTreeMainExp, PackedTy "STree" "l531"))


--------------------------------------------------------------------------------

sumSTreeFun :: FunDef2
sumSTreeFun = FunDef "sumSTree" "tr762" sumSTreeTy sumSTreeBod
  where
    sumSTreeTy :: ArrowTy2
    sumSTreeTy = (ArrowTy2
                      [LRM "lin761" (VarR "r760") Input]
                      (PackedTy "STree" "lin761")
                      (S.empty)
                      (IntTy)
                      [])

    sumSTreeBod :: L Exp2
    sumSTreeBod = l$ CaseE (l$ VarE "tr762")
                 [ ("Leaf", [("n763", "l764")],
                   l$ VarE "n763")
                 , ("Inner", [("i775","l776"),("b777","l778"),
                              ("x764","l765"), ("y766","l767")],
                   l$ LetE ("sx768", [], IntTy,
                            l$ AppE "sumSTree" ["l765"] (l$ VarE "x764")) $
                   l$ LetE ("sy769", [], IntTy,
                            l$ AppE "sumSTree" ["l767"] (l$ VarE "y766")) $
                   l$ LetE ("total770", [], IntTy ,
                            l$ PrimAppE AddP [l$ VarE "sx768", l$ VarE "sy769"]) $
                   l$ VarE "total770"
                   )]

sumSTreeMainExp :: L Exp2
sumSTreeMainExp = l$ Ext $ LetRegionE (VarR "r771") $
                 l$ Ext $ LetLocE "l772" (StartOfLE (VarR "r771")) $
                 l$ LetE ("tr773", [], PackedTy "STree" "l772",
                          l$ AppE "buildSTree" ["l772"] (l$ LitE 3)) $
                 l$ LetE ("sum774", [], IntTy,
                          l$ AppE "sumSTree" ["l772"] (l$ VarE "tr773")) $
                 l$ VarE "sum774"

sumSTreeProg :: Prog2
sumSTreeProg = Prog stree (M.fromList [("buildSTree", buildSTreeFun),
                                       ("sumSTree", sumSTreeFun)])
                   (Just (sumSTreeMainExp, IntTy))

--------------------------------------------------------------------------------

sumUpMainExp :: L Exp2
sumUpMainExp = l$ Ext $ LetRegionE (VarR "r530") $
                  l$ Ext $ LetLocE "l531" (StartOfLE (VarR "r530")) $
                  l$ LetE ("x532",[], PackedTy "STree" "l531",
                           l$ AppE "buildSTree" ["l531"] (l$ LitE 2)) $
                  l$ Ext $ LetRegionE (VarR "r536") $
                  l$ Ext $ LetLocE "l537" (StartOfLE (VarR "r536")) $
                  l$ LetE ("z538",[],PackedTy "STree" "l537",
                           l$ AppE "sumUp" ["l531","l537"] (l$ VarE "x532")) $
                  l$ VarE "z538"

sumUpProg :: Prog2
sumUpProg = Prog stree (M.fromList [("sumUp", sumUpFun)
                                   ,("valueSTree", valueSTreeFun)
                                   ,("buildSTree", buildSTreeFun)
                                   ])
            (Just (sumUpMainExp, PackedTy "STree" "l537"))

--------------------------------------------------------------------------------

evenFun :: FunDef2
evenFun = FunDef "even" "i560" evenFunTy evenFunBod
  where
    evenFunTy :: ArrowTy2
    evenFunTy = (ArrowTy2
                 []
                 (IntTy)
                 (S.empty)
                 (IntTy)
                 [])

    evenFunBod :: L Exp2
    evenFunBod = l$ LetE ("i561",[],IntTy, l$ PrimAppE ModP [l$ VarE "i560", l$ LitE 2]) $
                 l$ LetE ("b562",[],BoolTy,l$ PrimAppE EqIntP [l$ VarE "i561", l$ LitE 0]) $
                 l$ IfE (l$ VarE "b562")
                    (l$ LitE 1) -- True
                    (l$ LitE 0) -- False
{-

setEven :: Tree -> Tree
setEven tree =
  case tree of
    Leaf x -> Leaf x
    Inner sum x l r ->
      let l' = setEven l
          r' = setEven r
          v1 = value l'
          v2 = value r'
          v3 = v1 + v2
          x' = even sum
      in Inner sum x' l' r'

-}


setEvenFun :: FunDef2
setEvenFun = FunDef "setEven" "tr570" setEvenFunTy setEvenFunBod
  where
    setEvenFunTy :: ArrowTy2
    setEvenFunTy = (ArrowTy2
                    [LRM "lin571" (VarR "r570") Input, LRM "lout572" (VarR "r757") Output]
                    (PackedTy "STree" "lin571")
                    (S.empty)
                    (PackedTy "STree" "lout572")
                    [])


    setEvenFunBod :: L Exp2
    setEvenFunBod = l$ CaseE (l$ VarE "tr570") $
      [ ("Leaf", [("n573","l574")],
          l$ LetE ("x575",[],PackedTy "STree" "lout572",
                   l$ DataConE "lout572" "Leaf" [l$ VarE "n573"]) $
          l$ VarE "x575")

      , ("Inner", [("i576","l577"),("b578","l579"),("x580","l581"),("y582","l583")],
         l$ Ext $ LetLocE "l584" (AfterConstantLE 1 "lout572") $
         l$ Ext $ LetLocE "l585" (AfterVariableLE "i576" "l584") $
         l$ Ext $ LetLocE "l586" (AfterVariableLE "b578" "l585") $
         l$ LetE ("x587",[],PackedTy "STree" "l586",
                  l$ AppE "setEven" ["l581","l586"] (l$ VarE "x580")) $
         l$ Ext $ LetLocE "l588" (AfterVariableLE "x587" "l586") $
         l$ LetE ("y589",[],PackedTy "STree" "l588",
                  l$ AppE "setEven" ["l583","l588"] (l$ VarE "y582")) $
         l$ LetE ("v590",[],IntTy, l$ AppE "valueSTree" ["l586"] (l$ VarE "x587")) $
         l$ LetE ("v591",[],IntTy, l$ AppE "valueSTree" ["l588"] (l$ VarE "y589")) $
         l$ LetE ("v592",[],IntTy, l$ PrimAppE AddP [l$ VarE "v590", l$ VarE "v591"]) $
         l$ LetE ("b593",[],IntTy, l$ AppE "even" [] (l$ VarE "v592")) $
         l$ LetE ("z594",[],PackedTy "STree" "lout572",
                  l$ DataConE "lout572" "Inner" [l$ VarE "i576", l$ VarE "b593",
                                                 l$ VarE "x587", l$ VarE "y589"]) $
         l$ VarE "z594"
        )]


setEvenMainExp :: L Exp2
setEvenMainExp = l$ Ext $ LetRegionE (VarR "r592") $
                 l$ Ext $ LetLocE "l593" (StartOfLE (VarR "r592")) $
                 l$ LetE ("x594",[], PackedTy "STree" "l593",
                          l$ AppE "buildSTree" ["l593"] (l$ LitE 2)) $
                 l$ Ext $ LetRegionE (VarR "r595") $
                 l$ Ext $ LetLocE "l596" (StartOfLE (VarR "r595")) $
                 l$ LetE ("z597",[],PackedTy "STree" "l596",
                          l$ AppE "setEven" ["l593","l596"] (l$ VarE "x594")) $
                 l$ VarE "z597"


setEvenProg :: Prog2
setEvenProg = Prog stree (M.fromList [("setEven"   , setEvenFun)
                                     ,("even"      , evenFun )
                                     ,("buildSTree", buildSTreeFun)
                                     ,("valueSTree", valueSTreeFun)
                                     ])
            (Just (setEvenMainExp, PackedTy "STree" "l596"))

--------------------------------------------------------------------------------

{-

merged  :: Tree  -> (Tree, Int)
merged tr =
  case (tr) of
    Leaf x ->
      let ret1 = Leaf x
          ret2 = x
      in (ret1, ret2)

    Inner sum x left right ->
      let (left' , v1)  = merged left
          (right', v2)  = merged right
          sum' = v1 + v2
          even'= even  sum'
          ret1 = Inner sum' even' left' right'
          ret2 = sum
      in (ret1, ret2)

-}

sumUpSetEvenFun :: FunDef2
sumUpSetEvenFun = FunDef "sumUpSetEven" "tr600" sumUpSetEvenFunTy sumUpSetEvenFunBod
  where
    sumUpSetEvenFunTy :: ArrowTy2
    sumUpSetEvenFunTy = (ArrowTy2
                         [LRM "lin601" (VarR "r600") Input, LRM "lout602" (VarR "r758") Output]
                         (PackedTy "STree" "lin601")
                         (S.empty)
                         (ProdTy [PackedTy "STree" "lout602", IntTy])
                         [])


    sumUpSetEvenFunBod :: L Exp2
    sumUpSetEvenFunBod = l$ CaseE (l$ VarE "tr600") $
      [ ("Leaf", [("n603","l604")],
          l$ LetE ("x605",[],PackedTy "STree" "lout602",
                   l$ DataConE "lout602" "Leaf" [l$ VarE "n603"]) $
          l$ LetE ("tx606",[], ProdTy [PackedTy "STree" "lout602", IntTy],
                   l$ MkProdE [l$ VarE "x605", l$ VarE "n603"]) $
          l$ VarE "tx606")

      , ("Inner", [("i607","l608"),("b609","l610"),("x611","l612"),("y613","l622")],
         l$ Ext $ LetLocE "l614" (AfterConstantLE 1 "lout602") $
         l$ Ext $ LetLocE "l615" (AfterVariableLE "i607" "l614") $
         l$ Ext $ LetLocE "l616" (AfterVariableLE "b609" "l615") $
         l$ LetE ("tx617",[], ProdTy [PackedTy "STree" "l616", IntTy],
                  l$ AppE "sumUpSetEven" ["l612","l616"] (l$ VarE "x611")) $
         l$ LetE ("x618",[],PackedTy "STree" "l616", l$ ProjE 0 (l$ VarE "tx617")) $
         l$ LetE ("v619",[],IntTy, l$ ProjE 1 (l$ VarE "tx617")) $
         l$ Ext $ LetLocE "l620" (AfterVariableLE "x618" "l616") $
         l$ LetE ("tx621",[],ProdTy [PackedTy "STree" "l620", IntTy],
                  l$ AppE "sumUpSetEven" ["l622","l620"] (l$ VarE "y613")) $
         l$ LetE ("y623",[],PackedTy "STree" "l620", l$ ProjE 0 (l$ VarE "tx621")) $
         l$ LetE ("v624",[],IntTy, l$ ProjE 1 (l$ VarE "tx621")) $
         l$ LetE ("v625",[],IntTy, l$ PrimAppE AddP [l$ VarE "v619", l$ VarE "v624"]) $
         l$ LetE ("b626",[],IntTy, l$ AppE "even" [] (l$ VarE "v625")) $
         l$ LetE ("z627",[],PackedTy "STree" "lout602",
                  l$ DataConE "lout602" "Inner" [l$ VarE "v625", l$ VarE "b626",
                                                 l$ VarE "x618", l$ VarE "y623"]) $
         l$ LetE ("tx638",[], ProdTy [PackedTy "STree" "lout602", IntTy],
                  l$ MkProdE [l$ VarE "z627", l$ VarE "v625"]) $
         l$ VarE "tx638")
      ]


sumUpSetEvenExp :: L Exp2
sumUpSetEvenExp = l$ Ext $ LetRegionE (VarR "r628") $
                  l$ Ext $ LetLocE "l629" (StartOfLE (VarR "r628")) $
                  l$ LetE ("z630",[], PackedTy "STree" "l629",
                           l$ AppE "buildSTree" ["l629"] (l$ LitE 3)) $
                  l$ Ext $ LetRegionE (VarR "r631") $
                  l$ Ext $ LetLocE "l632" (StartOfLE (VarR "r631")) $
                  l$ LetE ("z633",[],ProdTy [PackedTy "STree" "l632", IntTy],
                           l$ AppE "sumUpSetEven" ["l629","l632"] (l$ VarE "z630")) $
                  l$ VarE "z633"


sumUpSetEvenProg :: Prog2
sumUpSetEvenProg = Prog stree (M.fromList [("sumUpSetEven", sumUpSetEvenFun)
                                          ,("even"        , evenFun )
                                          ,("buildSTree"  , buildSTreeFun)
                                          ])
            (Just (sumUpSetEvenExp, ProdTy [PackedTy "STree" "l632", IntTy]))

--------------------------------------------------------------------------------

-- (data Expr
--       (VARREF Int)
--       (INTLIT Int)
--       (LETE Int Expr Expr))

-- type Var = IntTy

-- subst :: Var -> Expr -> Expr
-- subst old new ex =
--   case ex of
--     VarE v | v == old  -> unLoc new
--            | otherwise -> VarE v
--     LitE _ -> ex
--     LetE (v,t,rhs) bod | v == old  -> LetE (v,t,go rhs) bod
--                        | otherwise -> LetE (v,t,go rhs) (go bod)


ddexpr :: DDefs Ty2
ddexpr = fromListDD [DDef (toVar "Expr")
                      [ ("VARREF", [(False,IntTy)])
                      , ("INTLIT", [(False,IntTy)])
                      , ("LETE"  , [(False,IntTy),
                                    (False,PackedTy "Expr" "l"),
                                    (False,PackedTy "Expr" "l")])
                      ]]

copyExprFun :: FunDef2
copyExprFun = FunDef "copyExpr" "e700" copyExprFunTy copyExprFunBod
  where
    copyExprFunTy :: ArrowTy2
    copyExprFunTy = (ArrowTy2
                     [LRM "lin702" (VarR "r701") Input,
                      LRM "lout703" (VarR "r759") Output]
                     (PackedTy "Expr" "lin702")
                     (S.empty)
                     (PackedTy "Expr" "lout703")
                     [])

    copyExprFunBod :: L Exp2
    copyExprFunBod = l$ CaseE (l$ VarE "e700")
                     [ ("VARREF", [("v704","l705")],
                        l$ DataConE "lout703" "VARREF" [l$ VarE "v704"]
                       )
                     , ("LETE", [("v706","l707"), ("rhs708", "l709"), ("bod710", "l711")],
                        l$ Ext $ LetLocE "l712" (AfterConstantLE 1 "lout703") $
                        l$ Ext $ LetLocE "l713" (AfterVariableLE "v706" "l712") $
                        l$ LetE ("rhs714",[], PackedTy "Expr" "l713",
                                 l$ AppE "copyExpr" ["l709","l713"] (l$ VarE "rhs708")) $
                        l$ Ext $ LetLocE "l715" (AfterVariableLE "rhs714" "l713") $
                        l$ LetE ("bod716",[],PackedTy "Expr" "l715",
                                 l$ AppE "copyExpr" ["l711", "l715"] (l$ VarE "bod710")) $
                        l$ LetE ("z717",[],PackedTy "Expr" "lout703",
                                 l$ DataConE "lout703" "LETE" [l$ VarE "v706", l$ VarE "rhs714", l$ VarE "bod716"]) $
                        l$ VarE "z717")
                     ]


substFun :: FunDef2
substFun = FunDef "subst" "tr653" substFunTy substFunBod
  where
    substFunTy :: ArrowTy2
    substFunTy = (ArrowTy2
                  [LRM "lin651" (VarR "r650") Input,
                   LRM "lin652" (VarR "r650") Input,
                   LRM "lout653" (VarR "r760") Output]
                  (ProdTy [IntTy,
                           PackedTy "Expr" "lin651",
                           PackedTy "Expr" "lin652"])
                  (S.empty)
                  (PackedTy "Expr" "lout653")
                  [])

    substFunBod :: L Exp2
    substFunBod = l$ LetE ("old654",[],IntTy, l$ ProjE 0 (l$ VarE "tr653")) $
                  l$ LetE ("new655",[],PackedTy "Expr" "lin651",
                           l$ ProjE 1 (l$ VarE "tr653")) $
                  l$ LetE ("expr656",[],PackedTy "Expr" "lin652",
                           l$ ProjE 2 (l$ VarE "tr653")) $
                  l$ CaseE (l$ VarE "expr656")
                  [ ("VARREF", [("v657","l658")],
                     l$ LetE ("b659",[], BoolTy,
                              l$ PrimAppE EqIntP [l$ VarE "v657", l$ VarE "old654"]) $
                     l$ IfE (l$ VarE "b659")
                     (l$ AppE "copyExpr" ["lin651", "lout653"] (l$ VarE "new655"))
                     (l$ DataConE "lout653" "VARREF" [l$ VarE "v657"]))
                  , ("LETE", [("v656","l657"), ("rhs658","l659"), ("bod660", "l661")],
                     l$ LetE ("b662",[],BoolTy,
                              l$ PrimAppE EqIntP [l$ VarE "v656", l$ VarE "old654"]) $
                     -- l$ IfE (l$ VarE "b662")
                     (l$ Ext $ LetLocE "l663" (AfterConstantLE 1 "lout653") $
                      l$ Ext $ LetLocE "l664" (AfterVariableLE "v656" "l663") $
                      l$ LetE ("p668",[], ProdTy [IntTy, PackedTy "Expr" "lin651", PackedTy "Expr" "l659"],
                               l$ MkProdE [l$ VarE "old654", l$ VarE "new655", l$ VarE "rhs658"]) $
                      l$ LetE ("rhs665",[],PackedTy "Expr" "l664",
                               l$ AppE "subst" ["lin651", "l659", "l664"] (l$ VarE "p668")) $
                      l$ Ext $ LetLocE "l669" (AfterVariableLE "rhs665" "l664") $
                      l$ LetE ("bod670",[], PackedTy "Expr" "l669",
                               l$ AppE "copyExpr" ["l661", "l669"] (l$ VarE "bod660")) $
                      l$ LetE ("z671",[], PackedTy "Expr" "lout653",
                               l$ DataConE "lout653" "LETE" [l$ VarE "v656", l$ VarE "rhs665", l$ VarE "bod670"]) $
                      l$ VarE "z671")
                    )
                  ]


substMainExp :: L Exp2
substMainExp = l$ Ext $ LetRegionE (VarR "r720") $
               l$ Ext $ LetLocE "l721" (StartOfLE (VarR "r720")) $
               l$ Ext $ LetLocE "l722" (AfterConstantLE 1 "l721") $
               l$ Ext $ LetLocE "l723" (AfterConstantLE 8 "l722") $
               l$ LetE ("rhs724",[], PackedTy "Expr" "l723",
                        l$ DataConE "l723" "VARREF" [l$ LitE 1]) $
               l$ Ext $ LetLocE "l724" (AfterVariableLE "rhs724" "l723") $
               l$ LetE ("bod725",[], PackedTy "Expr" "l724",
                        l$ DataConE "l724" "VARREF" [l$ LitE 10]) $
               l$ LetE ("old726",[],IntTy,l$ LitE 1) $
               l$ LetE ("z727",[], PackedTy "Expr" "l721",
                        l$ DataConE "l721" "LETE" [l$ VarE "old726", l$ VarE "rhs724", l$ VarE "bod725"]) $
               l$ Ext $ LetRegionE (VarR "r728") $
               l$ Ext $ LetLocE "l729" (StartOfLE (VarR "r728")) $
               l$ LetE ("new730",[],PackedTy "Expr" "l729",
                        l$ DataConE "l729" "VARREF" [l$ LitE 42]) $
               l$ LetE ("p731",[],ProdTy [IntTy, PackedTy "Expr" "l729", PackedTy "Expr" "l721"],
                        l$ MkProdE [l$ VarE "old726", l$ VarE "new730", l$ VarE "z727"]) $
               l$ Ext $ LetLocE "l730" (AfterVariableLE "new730" "l729") $
               l$ LetE ("z732",[], PackedTy "Expr" "l730",
                        l$ AppE "subst" ["l729", "l721", "l730"] (l$ VarE "p731")) $
               l$ VarE "z732"


substProg :: Prog2
substProg = Prog ddexpr (M.fromList [("subst", substFun),
                                     ("copyExpr", copyExprFun)])
            (Just (substMainExp, PackedTy "Expr" "l730"))

--------------------------------------------------------------------------------

ddtree' :: DDefs Ty2
ddtree' = fromListDD [DDef (toVar "Tree")
                       [ ("Leaf",[(False,IntTy)])
                       , ("Node",[ (False,PackedTy "Tree" "l")
                                 , (False,PackedTy "Tree" "l")])
                       , ("Node^", [ (False,CursorTy)
                                   , (False,PackedTy "Tree" "l")
                                   , (False,PackedTy "Tree" "l")])
                       , (indirectionTag++"1", [(False,CursorTy)])
                       ]]

-- The rightmost function *without* copy-insertion. Gibbon should add and use
-- indirection pointers to get to the rightmost node of the tree.

indrBuildTreeFun :: FunDef2
indrBuildTreeFun = FunDef "indrBuildTree" "i270" indrBuildTreeTy indrBuildTreeBod
  where
    indrBuildTreeTy :: ArrowTy2
    indrBuildTreeTy = (ArrowTy2
                   [LRM "lout272" (VarR "r271") Output]
                   (IntTy)
                   (S.empty)
                   (PackedTy "Tree" "lout272")
                   [])

    indrBuildTreeBod :: L Exp2
    indrBuildTreeBod = l$ LetE ("b279",[], BoolTy, l$ PrimAppE EqIntP [l$ VarE "i270", l$ LitE 0]) $
                       l$ IfE (l$ VarE "b279")
                       (l$ DataConE "lout272" "Leaf" [l$ LitE 1])
                       (l$ LetE ("i273",[], IntTy, l$ PrimAppE SubP [l$ VarE "i270", l$ LitE 1]) $
                        l$ Ext $ LetLocE "loc_indr" (AfterConstantLE 1 "lout272") $
                        l$ Ext $ LetLocE "l274" (AfterConstantLE 8 "loc_indr") $
                        l$ LetE ("x275",[],PackedTy "Tree" "l274",
                                 l$ AppE "indrBuildTree" ["l274"] (l$ VarE "i273")) $
                        l$ Ext $ LetLocE "l276" (AfterVariableLE "x275" "l274") $
                        l$ LetE ("y277",[],PackedTy "Tree" "l276",
                                 l$ AppE "indrBuildTree" ["l276"] (l$ VarE "i273")) $
                        l$ LetE ("indr_cur",[],CursorTy,
                                 l$ PrimAppE PEndOf [l$ VarE "x275"]) $
                        -- l$ LetE ("indr_node",[], PackedTy "Tree" "loc_indr",
                        --          l$ DataConE "loc_indr" (indirectionTag++"1") [l$ VarE "indr_cur"]) $
                        l$ LetE ("a278",[],PackedTy "Tree" "lout272",
                                 l$ DataConE "lout272" "Node^" [l$ VarE "indr_cur",
                                                                l$ VarE "x275",
                                                                l$ VarE "y277"]) $
                        l$ VarE "a278")

indrBuildTreeMainExp :: L Exp2
indrBuildTreeMainExp = l$ Ext $ LetRegionE (VarR "r800") $
                       l$ Ext $ LetLocE "l801" (StartOfLE (VarR "r800")) $
                       l$ LetE ("tr802", [], PackedTy "Tree" "l801",
                                l$ AppE "indrBuildTree" ["l801"] (l$ LitE 3)) $
                       l$ VarE "tr802"

indrBuildTreeProg :: Prog2
indrBuildTreeProg = Prog ddtree' (M.fromList [("indrBuildTree", indrBuildTreeFun)])
                         (Just (indrBuildTreeMainExp, PackedTy "Tree" "l801"))


indrRightmostFun :: FunDef2
indrRightmostFun = FunDef "indrRightmost" "t742" indrRightmostTy indrRightmostBod
  where
    indrRightmostTy :: ArrowTy2
    indrRightmostTy = (ArrowTy2
                       [LRM "lin741" (VarR "r740") Input]
                       (PackedTy "Tree" "lin741")
                       (S.empty)
                       (IntTy)
                       [])

indrRightmostBod :: L Exp2
indrRightmostBod = l$ CaseE (l$ VarE "t742")
               [("Leaf", [("n746","l747")],
                 l$ VarE "n746"),
                ("Node^", [("indr_y750","lindr_y750"),("x748","l749"), ("y750","l751")],
                 l$ LetE ("lm752",[],IntTy, l$ AppE "indrRightmost" ["l751"] (l$ VarE "y750")) $
                 l$ VarE "lm752")]

indrRightmostMainExp :: L Exp2
indrRightmostMainExp = l$ Ext $ LetRegionE (VarR "r753") $
                       l$ Ext $ LetLocE "l754" (StartOfLE (VarR "r753")) $
                       l$ LetE ("tr1", [], PackedTy "Tree" "l754",
                                l$ AppE "indrBuildTree" ["l754"] (l$ LitE 3)) $
                       l$ LetE ("a760",[], IntTy,
                                l$ AppE "indrRightmost" ["l754"] (l$ VarE "tr1")) $
                       l$ VarE "a760"

indrRightmostProg :: Prog2
indrRightmostProg = Prog ddtree' (M.fromList [("indrRightmost", indrRightmostFun)
                                             ,("indrBuildTree",indrBuildTreeFun)])
                    (Just (indrRightmostMainExp, IntTy))

--------------------------------------------------------------------------------

indrIDFun :: FunDef2
indrIDFun = FunDef "indrID" "tr800" indrIDTy indrIDBod
  where
    indrIDTy :: ArrowTy2
    indrIDTy = (ArrowTy2
                [LRM "lin802" (VarR "r801") Input, LRM "lout803" (VarR "r803") Output]
                (PackedTy "Tree" "lin802")
                (S.empty)
                (PackedTy "Tree" "lout803")
                [])

    indrIDBod :: L Exp2
    indrIDBod = l$ LetE ("a804",[], PackedTy "Tree" "lout803",
                         l$ Ext $ IndirectionE "Tree"
                                               (indirectionTag++"1")
                                               ("lout803","r803")
                                               ("lin802", "r801")
                                               (l$ LitE 10)) $
                l$ VarE ("a804")


--------------------------------------------------------------------------------

indrIDMainExp :: L Exp2
indrIDMainExp = l$ Ext $ LetRegionE (VarR "r806") $
                l$ Ext $ LetLocE "l807" (StartOfLE (VarR "r806")) $
                l$ LetE ("tr1",[], PackedTy "Tree" "l807",
                         l$ AppE "indrBuildTree" ["l807"] (l$ LitE 2)) $
                l$ Ext $ LetRegionE (VarR "r808") $
                l$ Ext $ LetLocE "l809" (StartOfLE (VarR "r808")) $
                l$ LetE ("tr2",[], PackedTy "Tree" "l809",
                         l$ AppE "indrID" ["l807", "l809"] (l$ VarE "tr1")) $
                l$ LetE ("rmost",[], IntTy,
                          l$ AppE "indrRightmost" ["l809"] (l$ VarE "tr2")) $
                l$ VarE "rmost"

indrIDProg :: Prog2
indrIDProg = Prog ddtree' (M.fromList [("indrBuildTree", indrBuildTreeFun)
                                      ,("indrID", indrIDFun)
                                      ,("indrRightmost",indrRightmostFun)])
             (Just (indrIDMainExp, IntTy))


--------------------------------------------------------------------------------

indrIDSumMainExp :: L Exp2
indrIDSumMainExp = l$ Ext $ LetRegionE (VarR "r806") $
                   l$ Ext $ LetLocE "l807" (StartOfLE (VarR "r806")) $
                   l$ LetE ("tr1",[], PackedTy "Tree" "l807",
                         l$ AppE "buildTree" ["l807"] (l$ LitE 10)) $
                   l$ Ext $ LetRegionE (VarR "r808") $
                   l$ Ext $ LetLocE "l809" (StartOfLE (VarR "r808")) $
                   l$ LetE ("tr2",[], PackedTy "Tree" "l809",
                            l$ AppE "indrID" ["l807", "l809"] (l$ VarE "tr1")) $
                   l$ LetE ("total",[], IntTy,
                            l$ AppE "sumTree" ["l809"] (l$ VarE "tr2")) $
                   l$ VarE "total"

indrIDSumProg :: Prog2
indrIDSumProg = Prog ddtree' (M.fromList [("buildTree", buildTreeFun)
                                         ,("indrID", indrIDFun)
                                         ,("sumTree",sumTreeFun)])
                (Just (indrIDSumMainExp, IntTy))
