module Gibbon.L2.Examples
  ( -- * Data definitions
    ddtree, stree, ddexpr, ddsnoclist

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

import Data.Set as S
import Data.Map as M

import Gibbon.Common
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

ddtree :: DDefs Ty2
ddtree = fromListDD [DDef (toVar "Tree") []
                      [ ("Leaf",[(False,IntTy)])
                      , ("Node",[ (False,PackedTy "Tree" "l")
                                , (False,PackedTy "Tree" "l")])
                      ]]


tTypeable :: Exp2
tTypeable =  Ext $ LetRegionE (VarR "r500") Undefined Nothing $
             Ext $ LetLocE "l501" (StartOfRegionLE (VarR "r500")) $
             LetE ("v502",[], IntTy, LitE 42) $
             (VarE "v502")

testTypeable :: UrTy LocVar
testTypeable = gRecoverType ddtree emptyEnv2 tTypeable

--------------------------------------------------------------------------------
-- Add1

add1TraversedFun :: FunDef2
add1TraversedFun = FunDef "add1" ["tr1"] add1TraversedFunTy add1FunBod (FunMeta Rec NoInline False)
  where add1TraversedFunTy = add1FunTy { arrEffs = S.fromList [Traverse "lin2"] }


add1Fun :: FunDef2
add1Fun = FunDef "add1" ["tr1"] add1FunTy add1FunBod (FunMeta Rec NoInline False)


add1FunTy :: ArrowTy2 Ty2
add1FunTy = ArrowTy2
             [LRM "lin2" (VarR "r3") Input, LRM "lout4" (VarR "r750") Output]
             [PackedTy "Tree" "lin2"]
             S.empty
             (PackedTy "Tree" "lout4")
             []
             False


add1FunBod :: Exp2
add1FunBod = CaseE (VarE "tr1")
  [ ("Leaf", [("n5","l6")],
      LetE ("v7",[],IntTy,
               PrimAppE AddP [VarE "n5", LitE 1]) $
      LetE ("lf8",[],PackedTy "Tree" "lout4",
               DataConE "lout4" "Leaf" [VarE "v7"]) $
      VarE "lf8")

  , ("Node", [("x9","l10"),("y11","l12")],
     Ext $ LetLocE "l13" (AfterConstantLE 1 "lout4") $
     LetE ("x14",[],PackedTy "Tree" "l13",
               AppE "add1" ["l10","l13"] [VarE "x9"]) $
     Ext $ LetLocE "l15" (AfterVariableLE "x14" "l13" True) $
     LetE ("y16",[],PackedTy "Tree" "l15", AppE "add1" ["l12","l15"] [VarE "y11"]) $
     LetE ("z17",[],PackedTy "Tree" "lout4",
              DataConE "lout4" "Node" [ VarE "x14" , VarE "y16"]) $
     VarE "z17")
  ]

add1MainExp :: Exp2
add1MainExp = Ext $ LetRegionE (VarR "r99") Undefined Nothing $
              Ext $ LetLocE "l100" (StartOfRegionLE (VarR "r99")) $
              Ext $ LetLocE "l101" (AfterConstantLE 1 "l100") $
              LetE ("x102",[],PackedTy "Tree" "l101",
                      DataConE "l101" "Leaf" [LitE 1]) $
              Ext $ LetLocE "l103" (AfterVariableLE "x102" "l101" True) $
              LetE ("y104",[],PackedTy "Tree" "l103",
                      DataConE "l103" "Leaf" [LitE 2]) $
              LetE ("z105",[],PackedTy "Tree" "l100",
                      DataConE "l100" "Node" [VarE "x102",
                                                 VarE "y104"]) $
              Ext $ LetRegionE (VarR "r106") Undefined Nothing $
              Ext $ LetLocE "l107" (StartOfRegionLE (VarR "r106")) $
              LetE ("a108",[], PackedTy "Tree" "l107",
                      AppE "add1" ["l100", "l107"] [VarE "z105"]) $
              VarE "a108"


add1Prog :: Prog2
add1Prog = Prog ddtree (M.fromList [("add1", add1Fun)])
           (Just (add1MainExp, PackedTy "Tree" "l107"))

--------------------------------------------------------------------------------

leafMainExp :: Exp2
leafMainExp = Ext $ LetRegionE (VarR "r150") Undefined Nothing $
              Ext $ LetLocE "l151" (StartOfRegionLE (VarR "r150")) $
              LetE ("x152",[],PackedTy "Tree" "l151",
                       DataConE "l151" "Leaf" [LitE 1]) $
              VarE "x152"

leafProg :: Prog2
leafProg = Prog ddtree M.empty (Just (leafMainExp, PackedTy "Tree" "l151"))


--------------------------------------------------------------------------------

-- writes node
nodeMainExp :: Exp2
nodeMainExp = Ext $ LetRegionE (VarR "r155") Undefined Nothing $
               Ext $ LetLocE "l156" (StartOfRegionLE (VarR "r155")) $
               Ext $ LetLocE "l157" (AfterConstantLE 1 "l156") $
               LetE ("x158",[],PackedTy "Tree" "l157",
                       DataConE "l157" "Leaf" [LitE 1]) $
               Ext $ LetLocE "l159" (AfterVariableLE "x158" "l157" True) $
               LetE ("y160",[],PackedTy "Tree" "l159",
                       DataConE "l159" "Leaf" [LitE 2]) $
               LetE ("z161",[],PackedTy "Tree" "l156",
                       DataConE "l156" "Node" [VarE "x158", VarE "y160"]) $
               VarE "z161"


nodeProg :: Prog2
nodeProg = Prog ddtree M.empty (Just (nodeMainExp, PackedTy "Tree" "l156"))

--------------------------------------------------------------------------------

id1Fun :: FunDef2
id1Fun = FunDef "id1" ["tr18"] idFunTy idFunBod (FunMeta NotRec NoInline False)
  where
    idFunBod = VarE "tr18"

    idFunTy :: ArrowTy2 Ty2
    idFunTy = ArrowTy2
               [LRM "lin19" (VarR "r20") Input, LRM "lout21" (VarR "r751") Output]
               [PackedTy "Tree" "lin19"]
               (S.empty)
               (PackedTy "Tree" "lout21")
               []
               False


id1Prog :: Prog2
id1Prog = Prog ddtree (M.fromList [("id1", id1Fun)]) Nothing

--------------------------------------------------------------------------------

copyTreeFun :: FunDef2
copyTreeFun = FunDef "copyTree" ["tr22"] copyFunTy copyBod (FunMeta NotRec NoInline False)
  where
    copyFunTy = ArrowTy2
                 [LRM "lin23" (VarR "r24") Input, LRM "lout25" (VarR "r752") Output]
                 [PackedTy "Tree" "lin23"]
                 S.empty
                 (PackedTy "Tree" "lout25")
                 []
                 False

    copyBod = CaseE (VarE "tr22")
                 [ ("Leaf", [("n27","lin26")],
                     LetE ("n28",[],PackedTy "Tree" "lout25",
                               DataConE "lout25" "Leaf" [VarE "n27"]) $
                     VarE "n28")

                 , ("Node", [("x29","lx30"),("y31","ly32")],
                    Ext  $ LetLocE "lx33" (AfterConstantLE 1 "lout25") $
                    LetE ("x34", [], PackedTy "Tree" "lx33",
                             AppE "copyTree" ["lx30","lx33"] [VarE "x29"]) $
                    Ext  $ LetLocE "ly35" (AfterVariableLE "x34" "lx33" True) $
                    LetE ("y36", [], PackedTy "Tree" "ly35",
                            AppE "copyTree" ["ly32","ly35"] [VarE "y31"]) $
                    DataConE "lout25" "Node" [VarE "x34", VarE "y36"])
                 ]

copyTreeMainExp :: Exp2
copyTreeMainExp = Ext $ LetRegionE (VarR "r200") Undefined Nothing $
                  Ext $ LetLocE "l201" (StartOfRegionLE (VarR "r200")) $
                  Ext $ LetLocE "l202" (AfterConstantLE 1 "l201") $
                  LetE ("x203",[],PackedTy "Tree" "l202",
                          DataConE "l202" "Leaf" [LitE 1]) $
                  Ext $ LetLocE "r204" (AfterVariableLE "x203" "l202" True) $
                  LetE ("y205",[],PackedTy "Tree" "r204",
                           DataConE "r204" "Leaf" [LitE 2]) $
                  LetE ("z206",[],PackedTy "Tree" "l201",
                           DataConE "l201" "Node" [VarE "x203", VarE "y205"]) $
                  Ext $ LetRegionE (VarR "r207") Undefined Nothing $
                  Ext $ LetLocE "l208" (StartOfRegionLE (VarR "r207")) $
                  LetE ("a209",[], PackedTy "Tree" "l208",
                           AppE "copyTree" ["l201", "l208"] [VarE "z206"]) $
                  VarE "a209"

copyTreeProg :: Prog2
copyTreeProg = Prog ddtree (M.fromList [("copyTree", copyTreeFun)]) $
               Just (copyTreeMainExp, PackedTy "Tree" "l208")

--------------------------------------------------------------------------------

id2Fun :: FunDef2
id2Fun = FunDef "id2" ["tr41"] id2Ty id2Bod (FunMeta NotRec NoInline False)
  where
    id2Ty :: ArrowTy2 Ty2
    id2Ty = ArrowTy2
             [LRM "lin37" (VarR "r38") Input, LRM "lout39" (VarR "r753") Output]
             [PackedTy "Tree" "lin37"]
             (S.empty)
             (PackedTy "Tree" "lout39")
             []
             False

    id2Bod = IfE (PrimAppE EqIntP [LitE 20, LitE 20])
             (VarE "tr41")
             (VarE "tr41")

id2Prog :: Prog2
id2Prog = Prog ddtree (M.fromList [("id2", id2Fun)]) Nothing

--------------------------------------------------------------------------------

copyOnId1Prog :: Prog2
copyOnId1Prog = Prog ddtree funs $ Just (copyOnId1MainExp, PackedTy "Tree" "l228")
  where
    funs  = M.fromList [("copyTree" , copyTreeFun),
                         ("id1WithCopy", id1WithCopyFun)]

copyOnId1MainExp :: Exp2
copyOnId1MainExp = Ext $ LetRegionE (VarR "r220") Undefined Nothing $
                   Ext $ LetLocE "l221" (StartOfRegionLE (VarR "r220")) $
                   Ext $ LetLocE "l222" (AfterConstantLE 1 "l221") $
                   LetE ("l223",[],PackedTy "Tree" "l222",
                           DataConE "l222" "Leaf" [LitE 1]) $
                   Ext $ LetLocE "l224" (AfterVariableLE "l223" "l222" True) $
                   LetE ("l225",[],PackedTy "Tree" "l224",
                            DataConE "l224" "Leaf" [LitE 2]) $
                   LetE ("z226",[],PackedTy "Tree" "l221",
                            DataConE "l221" "Node" [VarE "l223", VarE "l225"]) $
                   Ext $ LetRegionE (VarR "r227") Undefined Nothing $
                   Ext $ LetLocE "l228" (StartOfRegionLE (VarR "r227")) $
                   LetE ("a229",[], PackedTy "Tree" "l228",
                            AppE "id1WithCopy" ["l221", "l228"] [VarE "z226"]) $
                   VarE "a229"

id1WithCopyFun :: FunDef2
id1WithCopyFun = id1Fun { funBody = AppE "copyTree" ["lin19","lout21"]
                                    [VarE "tr18"]
                        , funName = "id1WithCopy"
                        }

--------------------------------------------------------------------------------

id3Fun :: FunDef2
id3Fun = FunDef "id3" ["i42"] id3Ty id3Bod (FunMeta NotRec NoInline False)
  where
    id3Ty :: ArrowTy2 Ty2
    id3Ty = ArrowTy2
             []
             [IntTy]
             (S.empty)
             (IntTy)
             []
             False
    id3Bod = VarE "i42"

id3MainExp :: Exp2
id3MainExp = AppE "id3" [] [LitE 42]

id3Prog :: Prog2
id3Prog = Prog ddtree (M.fromList [("id3", id3Fun)]) $ Just (id3MainExp, IntTy)


--------------------------------------------------------------------------------

intAddFun :: FunDef2
intAddFun = FunDef "intAdd" ["i109"] intAddTy id3Bod (FunMeta NotRec NoInline False)
  where
    intAddTy :: ArrowTy2 Ty2
    intAddTy = ArrowTy2
                []
                [ProdTy [IntTy, IntTy]]
                (S.empty)
                (IntTy)
                []
                False
    id3Bod = PrimAppE AddP [ProjE 0 (VarE "i109"), ProjE 1 (VarE "i109")]

intAddMainExp :: Exp2
intAddMainExp = LetE ("sum110", [], IntTy,
                         AppE "intAdd" []
                         [MkProdE [LitE 40,LitE 2]])
                (VarE "sum110")

intAddProg :: Prog2
intAddProg = Prog M.empty (M.fromList [("intAdd", intAddFun)]) (Just (intAddMainExp, IntTy))

--------------------------------------------------------------------------------

leftmostFun :: FunDef2
leftmostFun = FunDef "leftmost" ["t111"] leftmostTy leftmostBod (FunMeta Rec NoInline False)
  where
    leftmostTy :: ArrowTy2 Ty2
    leftmostTy = ArrowTy2
                 [LRM "lin112" (VarR "r113") Input]
                 [PackedTy "Tree" "lin112"]
                 (S.empty)
                 (IntTy)
                 []
                 False

leftmostBod :: Exp2
leftmostBod = CaseE (VarE "t111")
              [("Leaf", [("n114","l115")],
                VarE "n114"),
               ("Node", [("x117","l118"), ("y119","l120")],
                LetE ("lm121",[],IntTy, AppE "leftmost" ["l118"] [VarE "x117"]) $
                VarE "lm121")]

leftmostMainExp :: Exp2
leftmostMainExp = Ext $ LetRegionE (VarR "r122") Undefined Nothing $
                  Ext $ LetLocE "l123" (StartOfRegionLE (VarR "r122")) $
                  Ext $ LetLocE "l124" (AfterConstantLE 1 "l123") $
                  LetE ("x125",[],PackedTy "Tree" "l124",
                          DataConE "l124" "Leaf" [LitE 1]) $
                  Ext $ LetLocE "l126" (AfterVariableLE "x125" "l124" True) $
                  LetE ("y128",[],PackedTy "Tree" "l126",
                          DataConE "l126" "Leaf" [LitE 2]) $
                  LetE ("z127",[],PackedTy "Tree" "l123",
                          DataConE "l123" "Node" [VarE "x125", VarE "y128"]) $
                  LetE ("a131",[], IntTy,
                          AppE "leftmost" ["l123"] [VarE "z127"]) $
                  VarE "a131"

leftmostProg :: Prog2
leftmostProg = Prog ddtree (M.fromList [("leftmost", leftmostFun)]) (Just (leftmostMainExp, IntTy))


--------------------------------------------------------------------------------

rightmostFun :: FunDef2
rightmostFun = FunDef "rightmost" ["t242"] rightmostTy rightmostBod (FunMeta Rec NoInline False)
  where
    rightmostTy :: ArrowTy2 Ty2
    rightmostTy = ArrowTy2
                   [LRM "lin241" (VarR "r240") Input]
                   [PackedTy "Tree" "lin241"]
                   (S.empty)
                   (IntTy)
                   []
                   False

rightmostBod :: Exp2
rightmostBod = CaseE (VarE "t242")
               [("Leaf", [("n246","l247")],
                 VarE "n246"),
                ("Node", [("x248","l249"), ("y250","l251")],
                 -- Ext $ LetRegionE (VarR "r252") Undefined Nothing $
                 -- Ext $ LetLocE "l253" (StartOfRegionLE (VarR "r252")) $
                 -- LetE ("x254",[],PackedTy "Tree" "l253",
                 --          AppE "copyTree" ["l249", "l253"] (VarE "x248")) $
                 AppE "rightmost" ["l251"] [VarE "y250"]
                )]

rightmostMainExp :: Exp2
rightmostMainExp = Ext $ LetRegionE (VarR "r253") Undefined Nothing $
                   Ext $ LetLocE "l254" (StartOfRegionLE (VarR "r253")) $
                   Ext $ LetLocE "l255" (AfterConstantLE 1 "l254") $
                   LetE ("x256",[],PackedTy "Tree" "l255",
                            DataConE "l255" "Leaf" [LitE 1]) $
                   Ext $ LetLocE "l257" (AfterVariableLE "x256" "l255" True) $
                   LetE ("y258",[],PackedTy "Tree" "l257",
                            DataConE "l257" "Leaf" [LitE 2]) $
                   LetE ("z259",[],PackedTy "Tree" "l254",
                            DataConE "l254" "Node" [VarE "x256", VarE "y258"]) $
                   LetE ("a260",[], IntTy,
                            AppE "rightmost" ["l254"] [VarE "z259"]) $
                   VarE "a260"

rightmostProg :: Prog2
rightmostProg = Prog ddtree (M.fromList [("rightmost", rightmostFun)])
                (Just (rightmostMainExp, IntTy))


--------------------------------------------------------------------------------

buildLeafFun :: FunDef2
buildLeafFun = FunDef "buildLeaf" ["i125"] buildLeafTy buildLeafBod (FunMeta Rec NoInline False)
  where
    buildLeafTy :: ArrowTy2 Ty2
    buildLeafTy = ArrowTy2
                   [LRM "lout126" (VarR "r127") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" "lout126")
                   []
                   False

    buildLeafBod :: Exp2
    buildLeafBod = DataConE "lout126" "Leaf" [VarE "i125"]


buildLeafMainExp :: Exp2
buildLeafMainExp = Ext $ LetRegionE (VarR "r128") Undefined Nothing $
                   Ext $ LetLocE "l129" (StartOfRegionLE (VarR "r128")) $
                   AppE "buildLeaf" ["l129"] [LitE 42]

buildLeafProg :: Prog2
buildLeafProg = Prog ddtree (M.fromList [("buildLeaf", buildLeafFun)]) (Just (buildLeafMainExp, PackedTy "Tree" "l129"))


--------------------------------------------------------------------------------

buildTreeFun :: FunDef2
buildTreeFun = FunDef "buildTree" ["i270"] buildTreeTy buildTreeBod (FunMeta Rec NoInline False)
  where
    buildTreeTy :: ArrowTy2 Ty2
    buildTreeTy = ArrowTy2
                   [LRM "lout272" (VarR "r271") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" "lout272")
                   []
                   False

    buildTreeBod :: Exp2
    buildTreeBod = LetE ("b279",[], BoolTy, PrimAppE EqIntP [VarE "i270", LitE 0]) $
                   IfE (VarE "b279")
                   (DataConE "lout272" "Leaf" [LitE 1])
                   (LetE ("i273",[], IntTy, PrimAppE SubP [VarE "i270", LitE 1]) $
                    Ext $ LetLocE "l274" (AfterConstantLE 1 "lout272") $
                    LetE ("x275",[],PackedTy "Tree" "l274",
                             AppE "buildTree" ["l274"] [VarE "i273"]) $
                    Ext $ LetLocE "l276" (AfterVariableLE "x275" "l274" True) $
                    LetE ("y277",[],PackedTy "Tree" "l276",
                             AppE "buildTree" ["l276"] [VarE "i273"]) $
                    LetE ("a278",[],PackedTy "Tree" "lout272",
                             DataConE "lout272" "Node" [VarE "x275", VarE "y277"]) $
                    VarE "a278")


buildTreeMainExp :: Exp2
buildTreeMainExp = Ext $ LetRegionE (VarR "r279") Undefined Nothing $
                   Ext $ LetLocE "l280" (StartOfRegionLE (VarR "r279")) $
                   AppE "buildTree" ["l280"] [LitE 3]

buildTreeProg :: Prog2
buildTreeProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun)]) (Just (buildTreeMainExp, PackedTy "Tree" "l280"))


--------------------------------------------------------------------------------


buildTwoTreesFun :: FunDef2
buildTwoTreesFun = FunDef "buildTwoTrees" ["i750"] buildTreeTy buildTreeBod (FunMeta Rec NoInline False)
  where
    buildTreeTy :: ArrowTy2 Ty2
    buildTreeTy = ArrowTy2
                   [LRM "lout752" (VarR "r751") Output, LRM "lout754" (VarR "r753") Output]
                   [IntTy]
                   (S.empty)
                   (ProdTy [PackedTy "Tree" "lout752", PackedTy "Tree" "lout754"])
                   []
                   False

    buildTreeBod :: Exp2
    buildTreeBod = LetE ("tree1",[],PackedTy "Tree" "lout752",
                            AppE "buildTree" ["lout752"] [VarE "i750"]) $
                   LetE ("tree2",[],PackedTy "Tree" "lout754",
                            AppE "buildTree" ["lout754"] [VarE "i750"]) $
                   LetE ("a755",[], ProdTy [PackedTy "Tree" "lout752", PackedTy "Tree" "lout754"],
                            MkProdE [VarE "tree1", VarE "tree2"]) $
                   VarE "a755"

buildTwoTreesMainExp :: Exp2
buildTwoTreesMainExp = Ext $ LetRegionE (VarR "r756") Undefined Nothing $
                       Ext $ LetLocE "l757" (StartOfRegionLE (VarR "r756")) $
                       Ext $ LetRegionE (VarR "r758") Undefined Nothing $
                       Ext $ LetLocE "l759" (StartOfRegionLE (VarR "r758")) $
                       LetE ("treeprod", [], ProdTy [PackedTy "Tree" "lout757", PackedTy "Tree" "lout759"],
                                AppE "buildTwoTrees" ["l757", "l759"] [LitE 2]) $
                       VarE "treeprod"

buildTwoTreesProg :: Prog2
buildTwoTreesProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun),
                                             ("buildTwoTrees", buildTwoTreesFun)])
                         (Just (buildTwoTreesMainExp, ProdTy [PackedTy "Tree" "lout757", PackedTy "Tree" "lout759"]))

--------------------------------------------------------------------------------

buildTreeSumFun :: FunDef2
buildTreeSumFun = FunDef "buildTreeSum" ["i302"] buildTreeSumTy buildTreeSumBod (FunMeta Rec NoInline False)
  where
    buildTreeSumTy :: ArrowTy2 Ty2
    buildTreeSumTy = ArrowTy2
                      [LRM "lout301" (VarR "r300") Output]
                      [IntTy]
                      (S.empty)
                      (ProdTy [IntTy, PackedTy "Tree" "lout301"])
                      []
                      False

    buildTreeSumBod :: Exp2
    buildTreeSumBod = LetE ("b303",[], BoolTy, PrimAppE EqIntP [VarE "i302", LitE 0]) $
                      IfE (VarE "b303")
                      (LetE ("c316",[],PackedTy "Tree" "lout301",
                                DataConE "lout301" "Leaf" [LitE 1]) $
                       LetE ("t317",[],ProdTy [IntTy, PackedTy "Tree" "lout301"],
                               MkProdE [LitE 1, VarE "c316"]) $
                       VarE "t317")
                      (LetE ("i303",[], IntTy, PrimAppE SubP [VarE "i302", LitE 1]) $
                       Ext $ LetLocE "l304" (AfterConstantLE 1 "lout301") $
                       LetE ("t318",[],ProdTy [IntTy, PackedTy "Tree" "l304"],
                                AppE "buildTreeSum" ["l304"] [VarE "i303"]) $
                       LetE ("i309",[],IntTy, ProjE 0 (VarE "t318")) $
                       LetE ("x305",[],PackedTy "Tree" "l304", ProjE 1 (VarE "t318")) $
                       Ext $ LetLocE "l306" (AfterVariableLE "x305" "l304" True) $
                       LetE ("t319",[],ProdTy [IntTy, PackedTy "Tree" "l306"],
                                AppE "buildTreeSum" ["l306"] [VarE "i303"]) $
                       LetE ("i310",[],IntTy, ProjE 0 (VarE "t319")) $
                       LetE ("y307",[],PackedTy "Tree" "l306", ProjE 1 (VarE "t319")) $
                       LetE ("j311",[],IntTy, PrimAppE AddP [VarE "i309", VarE "i310"]) $
                       LetE ("a308",[],PackedTy "Tree" "lout301",
                                DataConE "lout301" "Node" [VarE "x305", VarE "y307"]) $
                       LetE ("b312",[], ProdTy [IntTy, PackedTy "Tree" "lout301"],
                                MkProdE [VarE "j311", VarE "a308"]) $
                       VarE "b312")


buildTreeSumMainExp :: Exp2
buildTreeSumMainExp = Ext $ LetRegionE (VarR "r313") Undefined Nothing $
                      Ext $ LetLocE "l314" (StartOfRegionLE (VarR "r313")) $
                      LetE ("z315",[],ProdTy [IntTy, PackedTy "Tree" "l314"],
                               AppE "buildTreeSum" ["l314"] [LitE 3]) $
                      VarE "z315"


buildTreeSumProg :: Prog2
buildTreeSumProg = Prog ddtree (M.fromList [("buildTreeSum", buildTreeSumFun)]) (Just (buildTreeSumMainExp, ProdTy [IntTy, PackedTy "Tree" "l314"]))

--------------------------------------------------------------------------------

sumTreeFun :: FunDef2
sumTreeFun = FunDef "sumTree" ["tr762"] sumTreeTy sumTreeBod (FunMeta Rec NoInline False)
  where
    sumTreeTy :: ArrowTy2 Ty2
    sumTreeTy = ArrowTy2
                      [LRM "lin761" (VarR "r760") Input]
                      [PackedTy "Tree" "lin761"]
                      (S.empty)
                      (IntTy)
                      []
                      False

    sumTreeBod :: Exp2
    sumTreeBod = CaseE (VarE "tr762")
                 [ ("Leaf", [("n763", "l764")],
                   VarE "n763")
                 , ("Node", [("x764","l765"), ("y766","l767")],
                   LetE ("sx768", [], IntTy,
                            AppE "sumTree" ["l765"] [VarE "x764"]) $
                   LetE ("sy769", [], IntTy,
                            AppE "sumTree" ["l767"] [VarE "y766"]) $
                   LetE ("total770", [], IntTy ,
                            PrimAppE AddP [VarE "sx768", VarE "sy769"]) $
                   VarE "total770"
                   )]

sumTreeMainExp :: Exp2
sumTreeMainExp = Ext $ LetRegionE (VarR "r771") Undefined Nothing $
                 Ext $ LetLocE "l772" (StartOfRegionLE (VarR "r771")) $
                 LetE ("tr773", [], PackedTy "Tree" "l772",
                          AppE "buildTree" ["l772"] [LitE 3]) $
                 LetE ("sum774", [], IntTy,
                          AppE "sumTree" ["l772"] [VarE "tr773"]) $
                 VarE "sum774"

sumTreeProg :: Prog2
sumTreeProg = Prog ddtree (M.fromList [("buildTree", buildTreeFun),
                                       ("sumTree", sumTreeFun)
                                      ])
                   (Just (sumTreeMainExp, IntTy))

--------------------------------------------------------------------------------

printTupMainExp :: Exp2
printTupMainExp = Ext $ LetRegionE (VarR "r325") Undefined Nothing $
                  Ext $ LetLocE "l326" (StartOfRegionLE (VarR "r325")) $
                  LetE ("i327",[], IntTy, LitE 42) $
                  LetE ("x328",[], PackedTy "Tree" "l326",
                           DataConE "l326" "Leaf" [LitE 1]) $
                  LetE ("t329",[], ProdTy [IntTy, PackedTy "Tree" "l326"],
                           MkProdE [VarE "i327", VarE "x328"]) $
                  VarE "t329"

printTupProg :: Prog2
printTupProg = Prog ddtree M.empty (Just (printTupMainExp, ProdTy [IntTy, PackedTy "Tree" "l326"]))

--------------------------------------------------------------------------------

printTupMainExp2 :: Exp2
printTupMainExp2 = Ext $ LetRegionE (VarR "r400") Undefined Nothing $
                  Ext $ LetLocE "l401" (StartOfRegionLE (VarR "r400")) $
                  LetE ("x402",[], PackedTy "Tree" "l401",
                           AppE "buildTree" ["l401"] [LitE 2]) $
                  Ext $ LetLocE "l403" (AfterVariableLE "x402" "l401" True) $
                  LetE ("y404",[], PackedTy "Tree" "l403",
                           AppE "buildTree" ["l403"] [LitE 1]) $
                  LetE ("z405",[], ProdTy [PackedTy "Tree" "l401", PackedTy "Tree" "l403"],
                           MkProdE [VarE "x402", VarE "y404"]) $
                  VarE "z405"

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
addTreesFun = FunDef "addTrees" ["trees354"] addTreesTy addTreesBod (FunMeta Rec NoInline False)
  where
    addTreesTy :: ArrowTy2 Ty2
    addTreesTy = ArrowTy2
                  [LRM "lin351" (VarR "r350") Input,
                   LRM "lin352" (VarR "r351") Input,
                   LRM "lout353" (VarR "r754") Output]
                  [ProdTy [PackedTy "Tree" "lin351", PackedTy "Tree" "lin352"]]
                  (S.empty)
                  (PackedTy "Tree" "lout353")
                  []
                  False

    addTreesBod :: Exp2
    addTreesBod = LetE ("tree1",[],PackedTy "Tree" "lin351",
                           ProjE 0 (VarE "trees354")) $
                  LetE ("tree2",[],PackedTy "Tree" "lin352",
                           ProjE 1 (VarE "trees354")) $
                  CaseE (VarE "tree1")
                  [("Leaf", [("n355","l356")],
                    CaseE (VarE "tree2")
                       [("Leaf",[("n357","l358")],
                         LetE ("n358",[],IntTy,PrimAppE AddP [VarE "n355",VarE "n357"]) $
                         LetE ("x359",[],PackedTy "Tree" "lout353",
                                  DataConE "lout353" "Leaf" [VarE "n358"]) $
                         VarE "x359"
                        )]
                   ),
                    ("Node", [("x360","l361"), ("y362","l363")],
                     CaseE (VarE "tree2")
                        [("Node", [("x364","l365"), ("y366","l367")],
                          Ext $ LetLocE "l368" (AfterConstantLE 1 "lout353") $
                          LetE ("tree3",[],ProdTy [PackedTy "Tree" "l361",
                                                      PackedTy "Tree" "l365"],
                                   MkProdE [VarE "x360", VarE "x364"]) $
                          LetE ("x369",[],PackedTy "Tree" "l368",
                                   AppE "addTrees" ["l361","l365","l368"] [VarE "tree3"]) $
                          Ext $ LetLocE "l370" (AfterVariableLE "x369" "l368" True) $
                          LetE ("tree4",[],ProdTy [PackedTy "Tree" "l363",
                                                      PackedTy "Tree" "l367"],
                                   MkProdE [VarE "y362", VarE "y366"]) $
                          LetE ("y371",[],PackedTy "Tree" "l370",
                                   AppE "addTrees" ["l363","l367","l370"] [VarE "tree4"]) $
                          LetE ("z372",[],PackedTy "Tree" "lout353",
                                    DataConE "lout353" "Node" [VarE "x369", VarE "y371"]) $
                          VarE "z372"
                         )]
                    )]

addTreesMainExp :: Exp2
addTreesMainExp = Ext $ LetRegionE (VarR "r400") Undefined Nothing $
                  Ext $ LetLocE "l401" (StartOfRegionLE (VarR "r400")) $
                  LetE ("x402",[], PackedTy "Tree" "l401",
                           AppE "buildTree" ["l401"] [LitE 2]) $
                  -- Ext $ LetLocE "l403" (AfterVariableLE "x402" "l401" True) $
                  Ext $ LetRegionE (VarR "r403") Undefined Nothing $
                  Ext $ LetLocE "l403" (StartOfRegionLE (VarR "r403")) $
                  LetE ("y404",[], PackedTy "Tree" "l403",
                           AppE "buildTree" ["l403"] [LitE 2]) $
                  LetE ("z405",[], ProdTy [PackedTy "Tree" "l401", PackedTy "Tree" "l403"],
                           MkProdE [VarE "x402", VarE "y404"]) $
                  Ext $ LetRegionE (VarR "r405") Undefined Nothing $
                  Ext $ LetLocE "l406" (StartOfRegionLE (VarR "r405")) $
                  LetE ("a407",[],PackedTy "Tree" "l406",
                           AppE "addTrees" ["l401","l403","l406"] [VarE "z405"]) $
                  VarE "a407"

addTreesProg :: Prog2
addTreesProg = Prog ddtree (M.fromList [("addTrees", addTreesFun)
                                       ,("buildTree", buildTreeFun)])
                    (Just (addTreesMainExp, PackedTy "Tree" "l406"))

--------------------------------------------------------------------------------

testProdFun :: FunDef2
testProdFun = FunDef "testprod" ["tup130"] testprodTy testprodBod (FunMeta Rec NoInline False)
  where
    testprodTy = ArrowTy2
                  [LRM "lin131" (VarR "r132") Input, LRM "lout133" (VarR "r755") Output]
                  [ProdTy [(PackedTy "Tree" "lin131"), IntTy]]
                  (S.empty)
                  (ProdTy [(PackedTy "Tree" "lout133"), IntTy])
                  []
                  False
    testprodBod = LetE ("t134",[], PackedTy "Tree" "lin131", ProjE 0 (VarE "tup130")) $
                  LetE ("i135",[], IntTy, ProjE 1 (VarE "tup130")) $
                  CaseE (VarE "t134")
                  [("Leaf",[("n136","l137")],
                    LetE ("v138",[],IntTy, PrimAppE AddP [VarE "n136", LitE 1]) $
                    LetE ("lf139",[],PackedTy "Tree" "lout133",
                            DataConE "lout133" "Leaf" [VarE "v138"]) $
                    LetE ("tup148",[], ProdTy [PackedTy "Tree" "lout133", IntTy],
                       MkProdE [VarE "lf139", VarE "i135"]) $
                    VarE "tup148"
                   ),
                   ("Node",[("x140","l141"), ("y142","l143")],
                    Ext $ LetLocE "l144" (AfterConstantLE 1 "lout133") $
                    LetE ("tup145",[], ProdTy [PackedTy "Tree" "l144", IntTy],
                             AppE "testprod" ["l141","l144"]
                             [MkProdE [VarE "x140", VarE "i135"]]) $

                    LetE ("x149",[], PackedTy "Tree" "l144", ProjE 0 (VarE "tup145")) $
                    Ext $ LetLocE "l146" (AfterVariableLE "x149" "l144" True) $
                    LetE ("tup147",[], ProdTy [PackedTy "Tree" "l146", IntTy],
                            AppE "testprod" ["l143","l146"]
                            [MkProdE [VarE "y142", VarE "i135"]]) $
                    LetE ("y150",[], PackedTy "Tree" "l146", ProjE 0 (VarE "tup147")) $
                    LetE ("node151",[], PackedTy "Tree" "lout133",
                            DataConE "lout133" "Node" [VarE "x149", VarE "y150"]) $
                    LetE ("tup152",[],ProdTy [PackedTy "Tree" "lout133", IntTy],
                            MkProdE [VarE "node151", VarE "i135"]) $
                    VarE "tup152")
                  ]

testProdProg :: Prog2
testProdProg = Prog ddtree (M.fromList [("testprod", testProdFun)]) Nothing

--------------------------------------------------------------------------------

-- Meaningless program, just to test flattenL2
testFlattenProg :: Prog2
testFlattenProg = Prog M.empty (M.fromList [("intAdd",intAddFun)]) $ Just (testFlattenBod, IntTy)
  where
    testFlattenBod :: Exp2
    testFlattenBod =
      Ext $ LetRegionE (VarR "_") Undefined Nothing $
      Ext $ LetLocE "_" (StartOfRegionLE (VarR "_")) $
      Ext $ LetLocE "_" (AfterConstantLE 1 "_") $
      LetE ("v170",[],IntTy,
               LetE ("v171",[],IntTy,
                        AppE "intAdd" []
                        [MkProdE [PrimAppE AddP [LitE 40, LitE 2],
                                     PrimAppE SubP [LitE 44, LitE 2]]]) $
                VarE "v171") $
      VarE "v170"

--------------------------------------------------------------------------------

-- sumUp + setEven example in L2
-- gensym starts at 500

stree :: DDefs Ty2
stree = fromListDD [DDef (toVar "STree") []
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
sumUpFun = FunDef "sumUp" ["tr1"] sumUpFunTy sumUpFunBod (FunMeta Rec NoInline False)
  where
    sumUpFunTy :: ArrowTy2 Ty2
    sumUpFunTy = ArrowTy2
                  [LRM "lin501" (VarR "r500") Input, LRM "lout502" (VarR "r756") Output]
                  [PackedTy "STree" "lin501"]
                  (S.empty)
                  (PackedTy "STree" "lout502")
                  []
                  False


    sumUpFunBod :: Exp2
    sumUpFunBod = CaseE (VarE "tr1")
      [ ("Leaf", [("n503","l504")],
          LetE ("x505",[],PackedTy "STree" "lout502",
                   DataConE "lout502" "Leaf" [VarE "n503"]) $
          VarE "x505")

      , ("Inner", [("i506","l507"),("b508","l509"),("x510","l511"),("y512","l513")],
         Ext $ LetLocE "l514" (AfterConstantLE 1 "lout502") $
         Ext $ LetLocE "l550" (AfterVariableLE "i506" "l514" True) $
         Ext $ LetLocE "l551" (AfterVariableLE "b508" "l550" True) $
         LetE ("x515",[],PackedTy "STree" "l551",
                   AppE "sumUp" ["l511","l551"] [VarE "x510"]) $
         Ext $ LetLocE "l516" (AfterVariableLE "x515" "l551" True) $
         LetE ("y517",[],PackedTy "STree" "l516",
                  AppE "sumUp" ["l513","l516"] [VarE "y512"]) $
         LetE ("v518",[],IntTy, AppE "valueSTree" ["l551"] [VarE "x515"]) $
         LetE ("v519",[],IntTy, AppE "valueSTree" ["l516"] [VarE "y517"]) $
         LetE ("v520",[],IntTy, PrimAppE AddP [VarE "v518", VarE "v519"]) $
         LetE ("z521",[],PackedTy "STree" "lout502",
                  DataConE "lout502" "Inner" [VarE "v520", VarE "b508",
                                                 VarE "x515", VarE "y517"]) $
         VarE "z521"
        )]


valueSTreeFun :: FunDef2
valueSTreeFun = FunDef "valueSTree" ["tr522"] valueSTreeFunTy valueSTreeFunBod (FunMeta Rec NoInline False)
  where
    valueSTreeFunTy :: ArrowTy2 Ty2
    valueSTreeFunTy = ArrowTy2
                       [LRM "lin524" (VarR "r523") Input]
                       [PackedTy "STree" "lin524"]
                       (S.empty)
                       (IntTy)
                       []
                       False

    valueSTreeFunBod :: Exp2
    valueSTreeFunBod = CaseE (VarE "tr522")
      [ ("Leaf", [("n523","l524")],
          VarE "n523")

      , ("Inner", [("i525","l526"),("b527","l528"),("x529","l530"),("y531","l532")],
         VarE "i525"
      )]


buildSTreeFun :: FunDef2
buildSTreeFun = FunDef "buildSTree" ["i543"] buildSTreeTy buildSTreeBod (FunMeta Rec NoInline False)
  where
    buildSTreeTy :: ArrowTy2 Ty2
    buildSTreeTy = ArrowTy2
                    [LRM "lout541" (VarR "r540") Output]
                    [IntTy]
                    (S.empty)
                    (PackedTy "STree" "lout541")
                    []
                    False

    buildSTreeBod :: Exp2
    buildSTreeBod = LetE ("b542",[], BoolTy, PrimAppE EqIntP [VarE "i543", LitE 0]) $
                   IfE (VarE "b542")
                   (DataConE "lout541" "Leaf" [LitE 1])
                   (LetE ("i548",[], IntTy, PrimAppE SubP [VarE "i543", LitE 1]) $
                    LetE ("i554",[], IntTy, LitE 0) $
                    LetE ("b555",[], IntTy, LitE 0) $
                    Ext $ LetLocE "l544" (AfterConstantLE 1 "lout541") $
                    Ext $ LetLocE "l552" (AfterVariableLE "i554" "l544" True) $
                    Ext $ LetLocE "l553" (AfterVariableLE "b555" "l552" True) $
                    LetE ("x545",[],PackedTy "STree" "l553",
                             AppE "buildSTree" ["l553"] [VarE "i548"]) $
                    Ext $ LetLocE "l545" (AfterVariableLE "x545" "l553" True) $
                    LetE ("y546",[],PackedTy "STree" "l545",
                             AppE "buildSTree" ["l545"] [VarE "i548"]) $
                    LetE ("a547",[],PackedTy "STree" "lout541",
                             DataConE "lout541" "Inner" [VarE "i554", VarE "b555",
                                                            VarE "x545", VarE "y546"]) $
                    VarE "a547")


buildSTreeMainExp :: Exp2
buildSTreeMainExp = Ext $ LetRegionE (VarR "r530") Undefined Nothing $
                    Ext $ LetLocE "l531" (StartOfRegionLE (VarR "r530")) $
                    LetE ("x532",[], PackedTy "STree" "l531",
                             AppE "buildSTree" ["l531"] [LitE 3]) $
                    VarE "x532"


buildSTreeProg :: Prog2
buildSTreeProg = Prog stree (M.fromList [("buildSTree", buildSTreeFun)])
                      (Just (buildSTreeMainExp, PackedTy "STree" "l531"))


--------------------------------------------------------------------------------

sumSTreeFun :: FunDef2
sumSTreeFun = FunDef "sumSTree" ["tr762"] sumSTreeTy sumSTreeBod (FunMeta Rec NoInline False)
  where
    sumSTreeTy :: ArrowTy2 Ty2
    sumSTreeTy = ArrowTy2
                      [LRM "lin761" (VarR "r760") Input]
                      [PackedTy "STree" "lin761"]
                      (S.empty)
                      (IntTy)
                      []
                      False

    sumSTreeBod :: Exp2
    sumSTreeBod = CaseE (VarE "tr762")
                 [ ("Leaf", [("n763", "l764")],
                   VarE "n763")
                 , ("Inner", [("i775","l776"),("b777","l778"),
                              ("x764","l765"), ("y766","l767")],
                   LetE ("sx768", [], IntTy,
                            AppE "sumSTree" ["l765"] [VarE "x764"]) $
                   LetE ("sy769", [], IntTy,
                            AppE "sumSTree" ["l767"] [VarE "y766"]) $
                   LetE ("total770", [], IntTy ,
                            PrimAppE AddP [VarE "sx768", VarE "sy769"]) $
                   VarE "total770"
                   )]

sumSTreeMainExp :: Exp2
sumSTreeMainExp = Ext $ LetRegionE (VarR "r771") Undefined Nothing $
                 Ext $ LetLocE "l772" (StartOfRegionLE (VarR "r771")) $
                 LetE ("tr773", [], PackedTy "STree" "l772",
                          AppE "buildSTree" ["l772"] [LitE 3]) $
                 LetE ("sum774", [], IntTy,
                          AppE "sumSTree" ["l772"] [VarE "tr773"]) $
                 VarE "sum774"

sumSTreeProg :: Prog2
sumSTreeProg = Prog stree (M.fromList [("buildSTree", buildSTreeFun),
                                       ("sumSTree", sumSTreeFun)])
                   (Just (sumSTreeMainExp, IntTy))

--------------------------------------------------------------------------------

sumUpMainExp :: Exp2
sumUpMainExp = Ext $ LetRegionE (VarR "r530") Undefined Nothing $
                  Ext $ LetLocE "l531" (StartOfRegionLE (VarR "r530")) $
                  LetE ("x532",[], PackedTy "STree" "l531",
                           AppE "buildSTree" ["l531"] [LitE 2]) $
                  Ext $ LetRegionE (VarR "r536") Undefined Nothing $
                  Ext $ LetLocE "l537" (StartOfRegionLE (VarR "r536")) $
                  LetE ("z538",[],PackedTy "STree" "l537",
                           AppE "sumUp" ["l531","l537"] [VarE "x532"]) $
                  VarE "z538"

sumUpProg :: Prog2
sumUpProg = Prog stree (M.fromList [("sumUp", sumUpFun)
                                   ,("valueSTree", valueSTreeFun)
                                   ,("buildSTree", buildSTreeFun)
                                   ])
            (Just (sumUpMainExp, PackedTy "STree" "l537"))

--------------------------------------------------------------------------------

evenFun :: FunDef2
evenFun = FunDef "even" ["i560"] evenFunTy evenFunBod (FunMeta NotRec NoInline False)
  where
    evenFunTy :: ArrowTy2 Ty2
    evenFunTy = ArrowTy2
                 []
                 [IntTy]
                 (S.empty)
                 (IntTy)
                 []
                 False

    evenFunBod :: Exp2
    evenFunBod = LetE ("i561",[],IntTy, PrimAppE ModP [VarE "i560", LitE 2]) $
                 LetE ("b562",[],BoolTy,PrimAppE EqIntP [VarE "i561", LitE 0]) $
                 IfE (VarE "b562")
                    (LitE 1) -- True
                    (LitE 0) -- False
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
setEvenFun = FunDef "setEven" ["tr570"] setEvenFunTy setEvenFunBod (FunMeta Rec NoInline False)
  where
    setEvenFunTy :: ArrowTy2 Ty2
    setEvenFunTy = ArrowTy2
                    [LRM "lin571" (VarR "r570") Input, LRM "lout572" (VarR "r757") Output]
                    [PackedTy "STree" "lin571"]
                    (S.empty)
                    (PackedTy "STree" "lout572")
                    []
                    False


    setEvenFunBod :: Exp2
    setEvenFunBod = CaseE (VarE "tr570")
      [ ("Leaf", [("n573","l574")],
          LetE ("x575",[],PackedTy "STree" "lout572",
                   DataConE "lout572" "Leaf" [VarE "n573"]) $
          VarE "x575")

      , ("Inner", [("i576","l577"),("b578","l579"),("x580","l581"),("y582","l583")],
         Ext $ LetLocE "l584" (AfterConstantLE 1 "lout572") $
         Ext $ LetLocE "l585" (AfterVariableLE "i576" "l584" True) $
         Ext $ LetLocE "l586" (AfterVariableLE "b578" "l585" True) $
         LetE ("x587",[],PackedTy "STree" "l586",
                  AppE "setEven" ["l581","l586"] [VarE "x580"]) $
         Ext $ LetLocE "l588" (AfterVariableLE "x587" "l586" True) $
         LetE ("y589",[],PackedTy "STree" "l588",
                  AppE "setEven" ["l583","l588"] [VarE "y582"]) $
         LetE ("v590",[],IntTy, AppE "valueSTree" ["l586"] [VarE "x587"]) $
         LetE ("v591",[],IntTy, AppE "valueSTree" ["l588"] [VarE "y589"]) $
         LetE ("v592",[],IntTy, PrimAppE AddP [VarE "v590", VarE "v591"]) $
         LetE ("b593",[],IntTy, AppE "even" [] [VarE "v592"]) $
         LetE ("z594",[],PackedTy "STree" "lout572",
                  DataConE "lout572" "Inner" [VarE "i576", VarE "b593",
                                                 VarE "x587", VarE "y589"]) $
         VarE "z594"
        )]


setEvenMainExp :: Exp2
setEvenMainExp = Ext $ LetRegionE (VarR "r592") Undefined Nothing $
                 Ext $ LetLocE "l593" (StartOfRegionLE (VarR "r592")) $
                 LetE ("x594",[], PackedTy "STree" "l593",
                          AppE "buildSTree" ["l593"] [LitE 2]) $
                 Ext $ LetRegionE (VarR "r595") Undefined Nothing $
                 Ext $ LetLocE "l596" (StartOfRegionLE (VarR "r595")) $
                 LetE ("z597",[],PackedTy "STree" "l596",
                          AppE "setEven" ["l593","l596"] [VarE "x594"]) $
                 VarE "z597"


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
sumUpSetEvenFun = FunDef "sumUpSetEven" ["tr600"] sumUpSetEvenFunTy sumUpSetEvenFunBod (FunMeta Rec NoInline False)
  where
    sumUpSetEvenFunTy :: ArrowTy2 Ty2
    sumUpSetEvenFunTy = ArrowTy2
                         [LRM "lin601" (VarR "r600") Input, LRM "lout602" (VarR "r758") Output]
                         [PackedTy "STree" "lin601"]
                         (S.empty)
                         (ProdTy [PackedTy "STree" "lout602", IntTy])
                         []
                         False


    sumUpSetEvenFunBod :: Exp2
    sumUpSetEvenFunBod = CaseE (VarE "tr600")
      [ ("Leaf", [("n603","l604")],
          LetE ("x605",[],PackedTy "STree" "lout602",
                   DataConE "lout602" "Leaf" [VarE "n603"]) $
          LetE ("tx606",[], ProdTy [PackedTy "STree" "lout602", IntTy],
                   MkProdE [VarE "x605", VarE "n603"]) $
          VarE "tx606")

      , ("Inner", [("i607","l608"),("b609","l610"),("x611","l612"),("y613","l622")],
         Ext $ LetLocE "l614" (AfterConstantLE 1 "lout602") $
         Ext $ LetLocE "l615" (AfterVariableLE "i607" "l614" True) $
         Ext $ LetLocE "l616" (AfterVariableLE "b609" "l615" True) $
         LetE ("tx617",[], ProdTy [PackedTy "STree" "l616", IntTy],
                  AppE "sumUpSetEven" ["l612","l616"] [VarE "x611"]) $
         LetE ("x618",[],PackedTy "STree" "l616", ProjE 0 (VarE "tx617")) $
         LetE ("v619",[],IntTy, ProjE 1 (VarE "tx617")) $
         Ext $ LetLocE "l620" (AfterVariableLE "x618" "l616" True) $
         LetE ("tx621",[],ProdTy [PackedTy "STree" "l620", IntTy],
                  AppE "sumUpSetEven" ["l622","l620"] [VarE "y613"]) $
         LetE ("y623",[],PackedTy "STree" "l620", ProjE 0 (VarE "tx621")) $
         LetE ("v624",[],IntTy, ProjE 1 (VarE "tx621")) $
         LetE ("v625",[],IntTy, PrimAppE AddP [VarE "v619", VarE "v624"]) $
         LetE ("b626",[],IntTy, AppE "even" [] [VarE "v625"]) $
         LetE ("z627",[],PackedTy "STree" "lout602",
                  DataConE "lout602" "Inner" [VarE "v625", VarE "b626",
                                                 VarE "x618", VarE "y623"]) $
         LetE ("tx638",[], ProdTy [PackedTy "STree" "lout602", IntTy],
                  MkProdE [VarE "z627", VarE "v625"]) $
         VarE "tx638")
      ]


sumUpSetEvenExp :: Exp2
sumUpSetEvenExp = Ext $ LetRegionE (VarR "r628") Undefined Nothing $
                  Ext $ LetLocE "l629" (StartOfRegionLE (VarR "r628")) $
                  LetE ("z630",[], PackedTy "STree" "l629",
                           AppE "buildSTree" ["l629"] [LitE 3]) $
                  Ext $ LetRegionE (VarR "r631") Undefined Nothing $
                  Ext $ LetLocE "l632" (StartOfRegionLE (VarR "r631")) $
                  LetE ("z633",[],ProdTy [PackedTy "STree" "l632", IntTy],
                           AppE "sumUpSetEven" ["l629","l632"] [VarE "z630"]) $
                  VarE "z633"


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
ddexpr = fromListDD [DDef (toVar "Expr") []
                      [ ("VARREF", [(False,IntTy)])
                      , ("INTLIT", [(False,IntTy)])
                      , ("LETE"  , [(False,IntTy),
                                    (False,PackedTy "Expr" "l"),
                                    (False,PackedTy "Expr" "l")])
                      ]]

copyExprFun :: FunDef2
copyExprFun = FunDef "copyExpr" ["e700"] copyExprFunTy copyExprFunBod (FunMeta Rec NoInline False)
  where
    copyExprFunTy :: ArrowTy2 Ty2
    copyExprFunTy = ArrowTy2
                     [LRM "lin702" (VarR "r701") Input,
                      LRM "lout703" (VarR "r759") Output]
                     [PackedTy "Expr" "lin702"]
                     (S.empty)
                     (PackedTy "Expr" "lout703")
                     []
                     False

    copyExprFunBod :: Exp2
    copyExprFunBod = CaseE (VarE "e700")
                     [ ("VARREF", [("v704","l705")],
                        DataConE "lout703" "VARREF" [VarE "v704"]
                       )
                     , ("LETE", [("v706","l707"), ("rhs708", "l709"), ("bod710", "l711")],
                        Ext $ LetLocE "l712" (AfterConstantLE 1 "lout703") $
                        Ext $ LetLocE "l713" (AfterVariableLE "v706" "l712" True) $
                        LetE ("rhs714",[], PackedTy "Expr" "l713",
                                 AppE "copyExpr" ["l709","l713"] [VarE "rhs708"]) $
                        Ext $ LetLocE "l715" (AfterVariableLE "rhs714" "l713" True) $
                        LetE ("bod716",[],PackedTy "Expr" "l715",
                                 AppE "copyExpr" ["l711", "l715"] [VarE "bod710"]) $
                        LetE ("z717",[],PackedTy "Expr" "lout703",
                                 DataConE "lout703" "LETE" [VarE "v706", VarE "rhs714", VarE "bod716"]) $
                        VarE "z717")
                     ]


substFun :: FunDef2
substFun = FunDef "subst" ["tr653"] substFunTy substFunBod (FunMeta Rec NoInline False)
  where
    substFunTy :: ArrowTy2 Ty2
    substFunTy = ArrowTy2
                  [LRM "lin651" (VarR "r650") Input,
                   LRM "lin652" (VarR "r650") Input,
                   LRM "lout653" (VarR "r760") Output]
                  [ProdTy [IntTy,
                           PackedTy "Expr" "lin651",
                           PackedTy "Expr" "lin652"]]
                  (S.empty)
                  (PackedTy "Expr" "lout653")
                  []
                  False

    substFunBod :: Exp2
    substFunBod = LetE ("old654",[],IntTy, ProjE 0 (VarE "tr653")) $
                  LetE ("new655",[],PackedTy "Expr" "lin651",
                           ProjE 1 (VarE "tr653")) $
                  LetE ("expr656",[],PackedTy "Expr" "lin652",
                           ProjE 2 (VarE "tr653")) $
                  CaseE (VarE "expr656")
                  [ ("VARREF", [("v657","l658")],
                     LetE ("b659",[], BoolTy,
                              PrimAppE EqIntP [VarE "v657", VarE "old654"]) $
                     IfE (VarE "b659")
                     (AppE "copyExpr" ["lin651", "lout653"] [VarE "new655"])
                     (DataConE "lout653" "VARREF" [VarE "v657"]))
                  , ("LETE", [("v656","l657"), ("rhs658","l659"), ("bod660", "l661")],
                     LetE ("b662",[],BoolTy,
                              PrimAppE EqIntP [VarE "v656", VarE "old654"])
                     -- IfE (VarE "b662")
                     (Ext $ LetLocE "l663" (AfterConstantLE 1 "lout653") $
                      Ext $ LetLocE "l664" (AfterVariableLE "v656" "l663" True) $
                      LetE ("p668",[], ProdTy [IntTy, PackedTy "Expr" "lin651", PackedTy "Expr" "l659"],
                               MkProdE [VarE "old654", VarE "new655", VarE "rhs658"]) $
                      LetE ("rhs665",[],PackedTy "Expr" "l664",
                               AppE "subst" ["lin651", "l659", "l664"] [VarE "p668"]) $
                      Ext $ LetLocE "l669" (AfterVariableLE "rhs665" "l664" True) $
                      LetE ("bod670",[], PackedTy "Expr" "l669",
                               AppE "copyExpr" ["l661", "l669"] [VarE "bod660"]) $
                      LetE ("z671",[], PackedTy "Expr" "lout653",
                               DataConE "lout653" "LETE" [VarE "v656", VarE "rhs665", VarE "bod670"]) $
                      VarE "z671")
                    )
                  ]


substMainExp :: Exp2
substMainExp = Ext $ LetRegionE (VarR "r720") Undefined Nothing $
               Ext $ LetLocE "l721" (StartOfRegionLE (VarR "r720")) $
               Ext $ LetLocE "l722" (AfterConstantLE 1 "l721") $
               Ext $ LetLocE "l723" (AfterConstantLE 8 "l722") $
               LetE ("rhs724",[], PackedTy "Expr" "l723",
                        DataConE "l723" "VARREF" [LitE 1]) $
               Ext $ LetLocE "l724" (AfterVariableLE "rhs724" "l723" True) $
               LetE ("bod725",[], PackedTy "Expr" "l724",
                        DataConE "l724" "VARREF" [LitE 10]) $
               LetE ("old726",[],IntTy,LitE 1) $
               LetE ("z727",[], PackedTy "Expr" "l721",
                        DataConE "l721" "LETE" [VarE "old726", VarE "rhs724", VarE "bod725"]) $
               Ext $ LetRegionE (VarR "r728") Undefined Nothing $
               Ext $ LetLocE "l729" (StartOfRegionLE (VarR "r728")) $
               LetE ("new730",[],PackedTy "Expr" "l729",
                        DataConE "l729" "VARREF" [LitE 42]) $
               LetE ("p731",[],ProdTy [IntTy, PackedTy "Expr" "l729", PackedTy "Expr" "l721"],
                        MkProdE [VarE "old726", VarE "new730", VarE "z727"]) $
               Ext $ LetLocE "l730" (AfterVariableLE "new730" "l729" True) $
               LetE ("z732",[], PackedTy "Expr" "l730",
                        AppE "subst" ["l729", "l721", "l730"] [VarE "p731"]) $
               VarE "z732"


substProg :: Prog2
substProg = Prog ddexpr (M.fromList [("subst", substFun),
                                     ("copyExpr", copyExprFun)])
            (Just (substMainExp, PackedTy "Expr" "l730"))

--------------------------------------------------------------------------------

ddtree' :: DDefs Ty2
ddtree' = fromListDD [DDef (toVar "Tree") []
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
indrBuildTreeFun = FunDef "indrBuildTree" ["i270"] indrBuildTreeTy indrBuildTreeBod (FunMeta Rec NoInline False)
  where
    indrBuildTreeTy :: ArrowTy2 Ty2
    indrBuildTreeTy = ArrowTy2
                   [LRM "lout272" (VarR "r271") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" "lout272")
                   []
                   False

    indrBuildTreeBod :: Exp2
    indrBuildTreeBod = LetE ("b279",[], BoolTy, PrimAppE EqIntP [VarE "i270", LitE 0]) $
                       IfE (VarE "b279")
                       (DataConE "lout272" "Leaf" [LitE 1])
                       (LetE ("i273",[], IntTy, PrimAppE SubP [VarE "i270", LitE 1]) $
                        Ext $ LetLocE "loc_indr" (AfterConstantLE 1 "lout272") $
                        Ext $ LetLocE "l274" (AfterConstantLE 8 "loc_indr") $
                        LetE ("x275",[],PackedTy "Tree" "l274",
                                 AppE "indrBuildTree" ["l274"] [VarE "i273"]) $
                        Ext $ LetLocE "l276" (AfterVariableLE "x275" "l274" True) $
                        LetE ("y277",[],PackedTy "Tree" "l276",
                                 AppE "indrBuildTree" ["l276"] [VarE "i273"]) $
                        LetE ("indr_cur",[],CursorTy,Ext (StartOfPkdCursor "y277"))  $
                        -- LetE ("indr_node",[], PackedTy "Tree" "loc_indr",
                        --          DataConE "loc_indr" (indirectionTag++"1") [VarE "indr_cur"]) $
                        LetE ("a278",[],PackedTy "Tree" "lout272",
                                 DataConE "lout272" "Node^" [VarE "indr_cur",
                                                                VarE "x275",
                                                                VarE "y277"]) $
                        VarE "a278")

indrBuildTreeMainExp :: Exp2
indrBuildTreeMainExp = Ext $ LetRegionE (VarR "r800") Undefined Nothing $
                       Ext $ LetLocE "l801" (StartOfRegionLE (VarR "r800")) $
                       LetE ("tr802", [], PackedTy "Tree" "l801",
                                AppE "indrBuildTree" ["l801"] [LitE 3]) $
                       VarE "tr802"

indrBuildTreeProg :: Prog2
indrBuildTreeProg = Prog ddtree' (M.fromList [("indrBuildTree", indrBuildTreeFun)])
                         (Just (indrBuildTreeMainExp, PackedTy "Tree" "l801"))


indrRightmostFun :: FunDef2
indrRightmostFun = FunDef "indrRightmost" ["t742"] indrRightmostTy indrRightmostBod (FunMeta Rec NoInline False)
  where
    indrRightmostTy :: ArrowTy2 Ty2
    indrRightmostTy = ArrowTy2
                       [LRM "lin741" (VarR "r740") Input]
                       [PackedTy "Tree" "lin741"]
                       S.empty
                       IntTy
                       []
                       False

indrRightmostBod :: Exp2
indrRightmostBod = CaseE (VarE "t742")
               [("Leaf", [("n746","l747")],
                 VarE "n746"),
                ("Node^", [("indr_y750","lindr_y750"),("x748","l749"), ("y750","l751")],
                 LetE ("lm752",[],IntTy, AppE "indrRightmost" ["l751"] [VarE "y750"]) $
                 VarE "lm752")]

indrRightmostMainExp :: Exp2
indrRightmostMainExp = Ext $ LetRegionE (VarR "r753") Undefined Nothing $
                       Ext $ LetLocE "l754" (StartOfRegionLE (VarR "r753")) $
                       LetE ("tr1", [], PackedTy "Tree" "l754",
                                AppE "indrBuildTree" ["l754"] [LitE 3]) $
                       LetE ("a760",[], IntTy,
                                AppE "indrRightmost" ["l754"] [VarE "tr1"]) $
                       VarE "a760"

indrRightmostProg :: Prog2
indrRightmostProg = Prog ddtree' (M.fromList [("indrRightmost", indrRightmostFun)
                                             ,("indrBuildTree",indrBuildTreeFun)])
                    (Just (indrRightmostMainExp, IntTy))

--------------------------------------------------------------------------------

indrIDFun :: FunDef2
indrIDFun = FunDef "indrID" ["tr800"] indrIDTy indrIDBod (FunMeta NotRec NoInline False)
  where
    indrIDTy :: ArrowTy2 Ty2
    indrIDTy = ArrowTy2
                [LRM "lin802" (VarR "r801") Input, LRM "lout803" (VarR "r803") Output]
                [PackedTy "Tree" "lin802"]
                (S.empty)
                (PackedTy "Tree" "lout803")
                []
                False

    indrIDBod :: Exp2
    indrIDBod = LetE ("a804",[], PackedTy "Tree" "lout803",
                         Ext $ IndirectionE "Tree"
                                               (indirectionTag++"1")
                                               ("lout803","r803")
                                               ("lin802", "r801")
                                               (LitE 10)) $
                VarE "a804"


--------------------------------------------------------------------------------

indrIDMainExp :: Exp2
indrIDMainExp = Ext $ LetRegionE (VarR "r806") Undefined Nothing $
                Ext $ LetLocE "l807" (StartOfRegionLE (VarR "r806")) $
                LetE ("tr1",[], PackedTy "Tree" "l807",
                         AppE "indrBuildTree" ["l807"] [LitE 2]) $
                Ext $ LetRegionE (VarR "r808") Undefined Nothing $
                Ext $ LetLocE "l809" (StartOfRegionLE (VarR "r808")) $
                LetE ("tr2",[], PackedTy "Tree" "l809",
                         AppE "indrID" ["l807", "l809"] [VarE "tr1"]) $
                LetE ("rmost",[], IntTy,
                          AppE "indrRightmost" ["l809"] [VarE "tr2"]) $
                VarE "rmost"

indrIDProg :: Prog2
indrIDProg = Prog ddtree' (M.fromList [("indrBuildTree", indrBuildTreeFun)
                                      ,("indrID", indrIDFun)
                                      ,("indrRightmost",indrRightmostFun)])
             (Just (indrIDMainExp, IntTy))


--------------------------------------------------------------------------------

indrIDSumMainExp :: Exp2
indrIDSumMainExp = Ext $ LetRegionE (VarR "r806") Undefined Nothing $
                   Ext $ LetLocE "l807" (StartOfRegionLE (VarR "r806")) $
                   LetE ("tr1",[], PackedTy "Tree" "l807",
                         AppE "buildTree" ["l807"] [LitE 10]) $
                   Ext $ LetRegionE (VarR "r808") Undefined Nothing $
                   Ext $ LetLocE "l809" (StartOfRegionLE (VarR "r808")) $
                   LetE ("tr2",[], PackedTy "Tree" "l809",
                            AppE "indrID" ["l807", "l809"] [VarE "tr1"]) $
                   LetE ("total",[], IntTy,
                            AppE "sumTree" ["l809"] [VarE "tr2"]) $
                   VarE "total"

indrIDSumProg :: Prog2
indrIDSumProg = Prog ddtree' (M.fromList [("buildTree", buildTreeFun)
                                         ,("indrID", indrIDFun)
                                         ,("sumTree",sumTreeFun)])
                (Just (indrIDSumMainExp, IntTy))

--------------------------------------------------------------------------------

ddsnoclist :: DDefs Ty2
ddsnoclist = fromListDD [DDef (toVar "SnocList") []
                         [ ("Nil"  , [])
                         , ("Snoc" , [(False,PackedTy "SnocList" "l"),
                                      (False,IntTy)])
                         ]]
