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
                      , ("Node",[ (False,PackedTy "Tree" (Single "l"))
                                , (False,PackedTy "Tree" (Single "l"))])
                      ]]


tTypeable :: Exp2
tTypeable =  Ext $ LetRegionE (VarR "r500") Undefined Nothing $
             Ext $ LetLocE (Single "l501") (StartOfRegionLE (VarR "r500")) $
             LetE ("v502",[], IntTy, LitE 42) $
             (VarE "v502")

testTypeable :: UrTy LocVar
testTypeable = gRecoverType ddtree emptyEnv2 tTypeable

--------------------------------------------------------------------------------
-- Add1

add1TraversedFun :: FunDef2
add1TraversedFun = FunDef "add1" [ "tr1"] add1TraversedFunTy add1FunBod (FunMeta Rec NoInline False)
  where add1TraversedFunTy = add1FunTy { arrEffs = S.fromList [Traverse (Single "lin2")] }


add1Fun :: FunDef2
add1Fun = FunDef "add1" [ "tr1"] add1FunTy add1FunBod (FunMeta Rec NoInline False)


add1FunTy :: ArrowTy2 Ty2
add1FunTy = ArrowTy2
             [LRM (Single "lin2") (AoSR $ VarR "r3") Input, LRM (Single "lout4") (AoSR $ VarR "r750") Output]
             [PackedTy "Tree" (Single "lin2")]
             S.empty
             (PackedTy "Tree" (Single "lout4"))
             []
             False


add1FunBod :: Exp2
add1FunBod = CaseE (VarE "tr1")
  [ ("Leaf", [("n5",(Single "l6"))],
      LetE ("v7",[],IntTy,
               PrimAppE AddP [VarE "n5", LitE 1]) $
      LetE ("lf8",[],PackedTy "Tree" (Single "lout4"),
               DataConE (Single "lout4") "Leaf" [VarE "v7"]) $
      VarE "lf8")

  , ("Node", [("x9",(Single "l10")),("y11",(Single "l12"))],
     Ext $ LetLocE (Single "l13") (AfterConstantLE 1 (Single "lout4")) $
     LetE ("x14",[],PackedTy "Tree" (Single "l13"),
               AppE "add1" [(Single "l10"),(Single "l13")] [VarE "x9"]) $
     Ext $ LetLocE (Single "l15") (AfterVariableLE "x14" (Single "l13") True) $
     LetE ("y16",[],PackedTy "Tree" (Single "l15"), AppE "add1" [(Single "l12"),(Single "l15")] [VarE "y11"]) $
     LetE ("z17",[],PackedTy "Tree" (Single "lout4"),
              DataConE (Single "lout4") "Node" [ VarE "x14" , VarE "y16"]) $
     VarE "z17")
  ]

add1MainExp :: Exp2
add1MainExp = Ext $ LetRegionE (VarR "r99") Undefined Nothing $
              Ext $ LetLocE (Single "l100") (StartOfRegionLE (VarR "r99")) $
              Ext $ LetLocE (Single "l101") (AfterConstantLE 1 (Single "l100")) $
              LetE ("x102",[],PackedTy "Tree" (Single "l101"),
                      DataConE (Single "l101") "Leaf" [LitE 1]) $
              Ext $ LetLocE (Single "l103") (AfterVariableLE "x102" (Single "l101") True) $
              LetE ("y104",[],PackedTy "Tree" (Single "l103"),
                      DataConE (Single "l103") "Leaf" [LitE 2]) $
              LetE ("z105",[],PackedTy "Tree" (Single "l100"),
                      DataConE (Single "l100") "Node" [VarE "x102",
                                                 VarE "y104"]) $
              Ext $ LetRegionE (VarR "r106") Undefined Nothing $
              Ext $ LetLocE (Single "l107") (StartOfRegionLE (VarR "r106")) $
              LetE ("a108",[], PackedTy "Tree" (Single "l107"),
                      AppE "add1" [(Single "l100"), (Single "l107")] [VarE "z105"]) $
              VarE "a108"


add1Prog :: Prog2
add1Prog = Prog ddtree (M.fromList [( "add1", add1Fun)])
           (Just (add1MainExp, PackedTy "Tree" (Single "l107")))

--------------------------------------------------------------------------------

leafMainExp :: Exp2
leafMainExp = Ext $ LetRegionE (VarR "r150") Undefined Nothing $
              Ext $ LetLocE (Single "l151") (StartOfRegionLE (VarR "r150")) $
              LetE ("x152",[],PackedTy "Tree" (Single "l151"),
                       DataConE (Single "l151") "Leaf" [LitE 1]) $
              VarE "x152"

leafProg :: Prog2
leafProg = Prog ddtree M.empty (Just (leafMainExp, PackedTy "Tree" (Single "l151")))


--------------------------------------------------------------------------------

-- writes node
nodeMainExp :: Exp2
nodeMainExp = Ext $ LetRegionE (VarR "r155") Undefined Nothing $
               Ext $ LetLocE (Single "l156") (StartOfRegionLE (VarR "r155")) $
               Ext $ LetLocE (Single "l157") (AfterConstantLE 1 (Single "l156")) $
               LetE ("x158",[],PackedTy "Tree" (Single "l157"),
                       DataConE (Single "l157") "Leaf" [LitE 1]) $
               Ext $ LetLocE (Single "l159") (AfterVariableLE "x158" (Single "l157") True) $
               LetE ("y160",[],PackedTy "Tree" (Single "l159"),
                       DataConE (Single "l159") "Leaf" [LitE 2]) $
               LetE ("z161",[],PackedTy "Tree" (Single "l156"),
                       DataConE (Single "l156") "Node" [VarE "x158", VarE "y160"]) $
               VarE "z161"


nodeProg :: Prog2
nodeProg = Prog ddtree M.empty (Just (nodeMainExp, PackedTy "Tree" (Single "l156")))

--------------------------------------------------------------------------------

id1Fun :: FunDef2
id1Fun = FunDef "id1" [ "tr18"] idFunTy idFunBod (FunMeta NotRec NoInline False)
  where
    idFunBod = VarE "tr18"

    idFunTy :: ArrowTy2 Ty2
    idFunTy = ArrowTy2
               [LRM (Single "lin19") (AoSR $ VarR "r20") Input, LRM (Single "lout21") (AoSR $ VarR "r751") Output]
               [PackedTy "Tree" (Single "lin19")]
               (S.empty)
               (PackedTy "Tree" (Single "lout21"))
               []
               False


id1Prog :: Prog2
id1Prog = Prog ddtree (M.fromList [( "id1", id1Fun)]) Nothing

--------------------------------------------------------------------------------

copyTreeFun :: FunDef2
copyTreeFun = FunDef "copyTree" [ "tr22"] copyFunTy copyBod (FunMeta NotRec NoInline False)
  where
    copyFunTy = ArrowTy2
                 [LRM (Single "lin23") (AoSR $ VarR "r24") Input, LRM (Single "lout25") (AoSR$ VarR "r752") Output]
                 [PackedTy "Tree" (Single "lin23")]
                 S.empty
                 (PackedTy "Tree" (Single "lout25"))
                 []
                 False

    copyBod = CaseE (VarE "tr22")
                 [ ("Leaf", [("n27",(Single "lin26"))],
                     LetE ("n28",[],PackedTy "Tree" (Single "lout25"),
                               DataConE (Single "lout25") "Leaf" [VarE "n27"]) $
                     VarE "n28")

                 , ("Node", [("x29",(Single "lx30")),("y31",(Single "ly32"))],
                    Ext  $ LetLocE (Single "lx33") (AfterConstantLE 1 (Single "lout25")) $
                    LetE ("x34", [], PackedTy "Tree" (Single "lx33"),
                             AppE "copyTree" [(Single "lx30"),(Single "lx33")] [VarE "x29"]) $
                    Ext  $ LetLocE (Single "ly35") (AfterVariableLE "x34" (Single "lx33") True) $
                    LetE ("y36", [], PackedTy "Tree" (Single "ly35"),
                            AppE "copyTree" [(Single "ly32"),(Single "ly35")] [VarE "y31"]) $
                    DataConE (Single "lout25") "Node" [VarE "x34", VarE "y36"])
                 ]

copyTreeMainExp :: Exp2
copyTreeMainExp = Ext $ LetRegionE (VarR "r200") Undefined Nothing $
                  Ext $ LetLocE (Single "l201") (StartOfRegionLE (VarR "r200")) $
                  Ext $ LetLocE (Single "l202") (AfterConstantLE 1 (Single "l201")) $
                  LetE ("x203",[],PackedTy "Tree" (Single "l202"),
                          DataConE (Single "l202") "Leaf" [LitE 1]) $
                  Ext $ LetLocE (Single "r204") (AfterVariableLE "x203" (Single "l202") True) $
                  LetE ("y205",[],PackedTy "Tree" (Single "r204"),
                           DataConE (Single "r204") "Leaf" [LitE 2]) $
                  LetE ("z206",[],PackedTy "Tree" (Single "l201"),
                           DataConE (Single "l201") "Node" [VarE "x203", VarE "y205"]) $
                  Ext $ LetRegionE (VarR "r207") Undefined Nothing $
                  Ext $ LetLocE (Single "l208") (StartOfRegionLE (VarR "r207")) $
                  LetE ("a209",[], PackedTy "Tree" (Single "l208"),
                           AppE "copyTree" [(Single "l201"), (Single "l208")] [VarE "z206"]) $
                  VarE "a209"

copyTreeProg :: Prog2
copyTreeProg = Prog ddtree (M.fromList [( "copyTree", copyTreeFun)]) $
               Just (copyTreeMainExp, PackedTy "Tree" (Single "l208"))

--------------------------------------------------------------------------------

id2Fun :: FunDef2
id2Fun = FunDef "id2" [ "tr41"] id2Ty id2Bod (FunMeta NotRec NoInline False)
  where
    id2Ty :: ArrowTy2 Ty2
    id2Ty = ArrowTy2
             [LRM (Single "lin37") (AoSR $ VarR "r38") Input, LRM (Single "lout39") (AoSR $ VarR "r753") Output]
             [PackedTy "Tree" (Single "lin37")]
             (S.empty)
             (PackedTy "Tree" (Single "lout39"))
             []
             False

    id2Bod = IfE (PrimAppE EqIntP [LitE 20, LitE 20])
             (VarE "tr41")
             (VarE "tr41")

id2Prog :: Prog2
id2Prog = Prog ddtree (M.fromList [( "id2", id2Fun)]) Nothing

--------------------------------------------------------------------------------

copyOnId1Prog :: Prog2
copyOnId1Prog = Prog ddtree funs $ Just (copyOnId1MainExp, PackedTy "Tree" (Single "l228"))
  where
    funs  = M.fromList [( "copyTree" , copyTreeFun),
                         ( "id1WithCopy", id1WithCopyFun)]

copyOnId1MainExp :: Exp2
copyOnId1MainExp = Ext $ LetRegionE (VarR "r220") Undefined Nothing $
                   Ext $ LetLocE (Single "l221") (StartOfRegionLE (VarR "r220")) $
                   Ext $ LetLocE (Single "l222") (AfterConstantLE 1 (Single "l221")) $
                   LetE ("l223",[],PackedTy "Tree" (Single "l222"),
                           DataConE (Single "l222") "Leaf" [LitE 1]) $
                   Ext $ LetLocE (Single "l224") (AfterVariableLE "l223" (Single "l222") True) $
                   LetE ("l225",[],PackedTy "Tree" (Single "l224"),
                            DataConE (Single "l224") "Leaf" [LitE 2]) $
                   LetE ("z226",[],PackedTy "Tree" (Single "l221"),
                            DataConE (Single "l221") "Node" [VarE "l223", VarE "l225"]) $
                   Ext $ LetRegionE (VarR "r227") Undefined Nothing $
                   Ext $ LetLocE (Single "l228") (StartOfRegionLE (VarR "r227")) $
                   LetE ("a229",[], PackedTy "Tree" (Single "l228"),
                            AppE "id1WithCopy" [(Single "l221"), (Single "l228")] [VarE "z226"]) $
                   VarE "a229"

id1WithCopyFun :: FunDef2
id1WithCopyFun = id1Fun { funBody = AppE "copyTree" [(Single "lin19"),(Single "lout21")]
                                    [VarE "tr18"]
                        , funName = "id1WithCopy"
                        }

--------------------------------------------------------------------------------

id3Fun :: FunDef2
id3Fun = FunDef "id3" [ "i42"] id3Ty id3Bod (FunMeta NotRec NoInline False)
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
id3Prog = Prog ddtree (M.fromList [( "id3", id3Fun)]) $ Just (id3MainExp, IntTy)


--------------------------------------------------------------------------------

intAddFun :: FunDef2
intAddFun = FunDef "intAdd" [ "i109"] intAddTy id3Bod (FunMeta NotRec NoInline False)
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
intAddProg = Prog M.empty (M.fromList [( "intAdd", intAddFun)]) (Just (intAddMainExp, IntTy))

--------------------------------------------------------------------------------

leftmostFun :: FunDef2
leftmostFun = FunDef "leftmost" [ "t111"] leftmostTy leftmostBod (FunMeta Rec NoInline False)
  where
    leftmostTy :: ArrowTy2 Ty2
    leftmostTy = ArrowTy2
                 [LRM (Single "lin112") (AoSR $ VarR "r113") Input]
                 [PackedTy "Tree" (Single "lin112")]
                 (S.empty)
                 (IntTy)
                 []
                 False

leftmostBod :: Exp2
leftmostBod = CaseE (VarE "t111")
              [("Leaf", [("n114",(Single "l115"))],
                VarE "n114"),
               ("Node", [("x117",(Single "l118")), ("y119",(Single "l120"))],
                LetE ("lm121",[],IntTy, AppE "leftmost" [(Single "l118")] [VarE "x117"]) $
                VarE "lm121")]

leftmostMainExp :: Exp2
leftmostMainExp = Ext $ LetRegionE (VarR "r122") Undefined Nothing $
                  Ext $ LetLocE (Single "l123") (StartOfRegionLE (VarR "r122")) $
                  Ext $ LetLocE (Single "l124") (AfterConstantLE 1 (Single "l123")) $
                  LetE ("x125",[],PackedTy "Tree" (Single "l124"),
                          DataConE (Single "l124") "Leaf" [LitE 1]) $
                  Ext $ LetLocE (Single "l126") (AfterVariableLE "x125" (Single "l124") True) $
                  LetE ("y128",[],PackedTy "Tree" (Single "l126"),
                          DataConE (Single "l126") "Leaf" [LitE 2]) $
                  LetE ("z127",[],PackedTy "Tree" (Single "l123"),
                          DataConE (Single "l123") "Node" [VarE "x125", VarE "y128"]) $
                  LetE ("a131",[], IntTy,
                          AppE "leftmost" [(Single "l123")] [VarE "z127"]) $
                  VarE "a131"

leftmostProg :: Prog2
leftmostProg = Prog ddtree (M.fromList [( "leftmost", leftmostFun)]) (Just (leftmostMainExp, IntTy))


--------------------------------------------------------------------------------

rightmostFun :: FunDef2
rightmostFun = FunDef "rightmost" [ "t242"] rightmostTy rightmostBod (FunMeta Rec NoInline False)
  where
    rightmostTy :: ArrowTy2 Ty2
    rightmostTy = ArrowTy2
                   [LRM (Single "lin241") (AoSR $ VarR "r240") Input]
                   [PackedTy "Tree" (Single "lin241")]
                   (S.empty)
                   (IntTy)
                   []
                   False

rightmostBod :: Exp2
rightmostBod = CaseE (VarE "t242")
               [("Leaf", [("n246",(Single "l247"))],
                 VarE "n246"),
                ("Node", [("x248",(Single "l249")), ("y250",(Single "l251"))],
                 -- Ext $ LetRegionE (VarR "r252") Undefined Nothing $
                 -- Ext $ LetLocE "l253" (StartOfRegionLE (VarR "r252")) $
                 -- LetE ("x254",[],PackedTy "Tree" "l253",
                 --          AppE "copyTree" ["l249", "l253"] (VarE "x248")) $
                 AppE "rightmost" [(Single "l251")] [VarE "y250"]
                )]

rightmostMainExp :: Exp2
rightmostMainExp = Ext $ LetRegionE (VarR "r253") Undefined Nothing $
                   Ext $ LetLocE (Single "l254") (StartOfRegionLE (VarR "r253")) $
                   Ext $ LetLocE (Single "l255") (AfterConstantLE 1 (Single "l254")) $
                   LetE ("x256",[],PackedTy "Tree" (Single "l255"),
                            DataConE (Single "l255") "Leaf" [LitE 1]) $
                   Ext $ LetLocE (Single "l257") (AfterVariableLE "x256" (Single "l255") True) $
                   LetE ("y258",[],PackedTy "Tree" (Single "l257"),
                            DataConE (Single "l257") "Leaf" [LitE 2]) $
                   LetE ("z259",[],PackedTy "Tree" (Single "l254"),
                            DataConE (Single "l254") "Node" [VarE "x256", VarE "y258"]) $
                   LetE ("a260",[], IntTy,
                            AppE "rightmost" [(Single "l254")] [VarE "z259"]) $
                   VarE "a260"

rightmostProg :: Prog2
rightmostProg = Prog ddtree (M.fromList [( "rightmost", rightmostFun)])
                (Just (rightmostMainExp, IntTy))


--------------------------------------------------------------------------------

buildLeafFun :: FunDef2
buildLeafFun = FunDef "buildLeaf" [ "i125"] buildLeafTy buildLeafBod (FunMeta Rec NoInline False)
  where
    buildLeafTy :: ArrowTy2 Ty2
    buildLeafTy = ArrowTy2
                   [LRM (Single "lout126") (AoSR $ VarR "r127") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" (Single "lout126"))
                   []
                   False

    buildLeafBod :: Exp2
    buildLeafBod = DataConE (Single "lout126") "Leaf" [VarE "i125"]


buildLeafMainExp :: Exp2
buildLeafMainExp = Ext $ LetRegionE (VarR "r128") Undefined Nothing $
                   Ext $ LetLocE (Single "l129") (StartOfRegionLE (VarR "r128")) $
                   AppE "buildLeaf" [(Single "l129")] [LitE 42]

buildLeafProg :: Prog2
buildLeafProg = Prog ddtree (M.fromList [( "buildLeaf", buildLeafFun)]) (Just (buildLeafMainExp, PackedTy "Tree" (Single "l129")))


--------------------------------------------------------------------------------

buildTreeFun :: FunDef2
buildTreeFun = FunDef "buildTree" [ "i270"] buildTreeTy buildTreeBod (FunMeta Rec NoInline False)
  where
    buildTreeTy :: ArrowTy2 Ty2
    buildTreeTy = ArrowTy2
                   [LRM (Single "lout272") (AoSR $ VarR "r271") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" (Single "lout272"))
                   []
                   False

    buildTreeBod :: Exp2
    buildTreeBod = LetE ("b279",[], BoolTy, PrimAppE EqIntP [VarE "i270", LitE 0]) $
                   IfE (VarE "b279")
                   (DataConE (Single "lout272") "Leaf" [LitE 1])
                   (LetE ("i273",[], IntTy, PrimAppE SubP [VarE "i270", LitE 1]) $
                    Ext $ LetLocE (Single "l274") (AfterConstantLE 1 (Single "lout272")) $
                    LetE ("x275",[],PackedTy "Tree" (Single "l274"),
                             AppE "buildTree" [(Single "l274")] [VarE "i273"]) $
                    Ext $ LetLocE (Single "l276") (AfterVariableLE "x275" (Single "l274") True) $
                    LetE ("y277",[],PackedTy "Tree" (Single "l276"),
                             AppE "buildTree" [(Single "l276")] [VarE "i273"]) $
                    LetE ("a278",[],PackedTy "Tree" (Single "lout272"),
                             DataConE (Single "lout272") "Node" [VarE "x275", VarE "y277"]) $
                    VarE "a278")


buildTreeMainExp :: Exp2
buildTreeMainExp = Ext $ LetRegionE (VarR "r279") Undefined Nothing $
                   Ext $ LetLocE (Single "l280") (StartOfRegionLE (VarR "r279")) $
                   AppE "buildTree" [(Single "l280")] [LitE 3]

buildTreeProg :: Prog2
buildTreeProg = Prog ddtree (M.fromList [( "buildTree", buildTreeFun)]) (Just (buildTreeMainExp, PackedTy "Tree" (Single "l280")))


--------------------------------------------------------------------------------


buildTwoTreesFun :: FunDef2
buildTwoTreesFun = FunDef "buildTwoTrees" [ "i750"] buildTreeTy buildTreeBod (FunMeta Rec NoInline False)
  where
    buildTreeTy :: ArrowTy2 Ty2
    buildTreeTy = ArrowTy2
                   [LRM (Single "lout752") (AoSR $ VarR "r751") Output, LRM (Single "lout754") (AoSR $ VarR "r753") Output]
                   [IntTy]
                   (S.empty)
                   (ProdTy [PackedTy "Tree" (Single "lout752"), PackedTy "Tree" (Single "lout754")])
                   []
                   False

    buildTreeBod :: Exp2
    buildTreeBod = LetE ("tree1",[],PackedTy "Tree" (Single "lout752"),
                            AppE "buildTree" [(Single "lout752")] [VarE "i750"]) $
                   LetE ("tree2",[],PackedTy "Tree" (Single "lout754"),
                            AppE "buildTree" [(Single "lout754")] [VarE "i750"]) $
                   LetE ("a755",[], ProdTy [PackedTy "Tree" (Single "lout752"), PackedTy "Tree" (Single "lout754")],
                            MkProdE [VarE "tree1", VarE "tree2"]) $
                   VarE "a755"

buildTwoTreesMainExp :: Exp2
buildTwoTreesMainExp = Ext $ LetRegionE (VarR "r756") Undefined Nothing $
                       Ext $ LetLocE (Single "l757") (StartOfRegionLE (VarR "r756")) $
                       Ext $ LetRegionE (VarR "r758") Undefined Nothing $
                       Ext $ LetLocE (Single "l759") (StartOfRegionLE (VarR "r758")) $
                       LetE ("treeprod", [], ProdTy [PackedTy "Tree" (Single "lout757"), PackedTy "Tree" (Single "lout759")],
                                AppE "buildTwoTrees" [(Single "l757"), (Single "l759")] [LitE 2]) $
                       VarE "treeprod"

buildTwoTreesProg :: Prog2
buildTwoTreesProg = Prog ddtree (M.fromList [( "buildTree", buildTreeFun),
                                             ( "buildTwoTrees", buildTwoTreesFun)])
                         (Just (buildTwoTreesMainExp, ProdTy [PackedTy "Tree" (Single "lout757"), PackedTy "Tree" (Single "lout759")]))

--------------------------------------------------------------------------------

buildTreeSumFun :: FunDef2
buildTreeSumFun = FunDef "buildTreeSum" [ "i302"] buildTreeSumTy buildTreeSumBod (FunMeta Rec NoInline False)
  where
    buildTreeSumTy :: ArrowTy2 Ty2
    buildTreeSumTy = ArrowTy2
                      [LRM (Single "lout301") (AoSR $ VarR "r300") Output]
                      [IntTy]
                      (S.empty)
                      (ProdTy [IntTy, PackedTy "Tree" (Single "lout301")])
                      []
                      False

    buildTreeSumBod :: Exp2
    buildTreeSumBod = LetE ("b303",[], BoolTy, PrimAppE EqIntP [VarE "i302", LitE 0]) $
                      IfE (VarE "b303")
                      (LetE ("c316",[],PackedTy "Tree" (Single "lout301"),
                                DataConE (Single "lout301") "Leaf" [LitE 1]) $
                       LetE ("t317",[],ProdTy [IntTy, PackedTy "Tree" (Single "lout301")],
                               MkProdE [LitE 1, VarE "c316"]) $
                       VarE "t317")
                      (LetE ("i303",[], IntTy, PrimAppE SubP [VarE "i302", LitE 1]) $
                       Ext $ LetLocE (Single "l304") (AfterConstantLE 1 (Single "lout301")) $
                       LetE ("t318",[],ProdTy [IntTy, PackedTy "Tree" (Single "l304")],
                                AppE "buildTreeSum" [(Single "l304")] [VarE "i303"]) $
                       LetE ("i309",[],IntTy, ProjE 0 (VarE "t318")) $
                       LetE ("x305",[],PackedTy "Tree" (Single "l304"), ProjE 1 (VarE "t318")) $
                       Ext $ LetLocE (Single "l306") (AfterVariableLE "x305" (Single "l304") True) $
                       LetE ("t319",[],ProdTy [IntTy, PackedTy "Tree" (Single "l306")],
                                AppE "buildTreeSum" [(Single "l306")] [VarE "i303"]) $
                       LetE ("i310",[],IntTy, ProjE 0 (VarE "t319")) $
                       LetE ("y307",[],PackedTy "Tree" (Single "l306"), ProjE 1 (VarE "t319")) $
                       LetE ("j311",[],IntTy, PrimAppE AddP [VarE "i309", VarE "i310"]) $
                       LetE ("a308",[],PackedTy "Tree" (Single "lout301"),
                                DataConE (Single "lout301") "Node" [VarE "x305", VarE "y307"]) $
                       LetE ("b312",[], ProdTy [IntTy, PackedTy "Tree" (Single "lout301")],
                                MkProdE [VarE "j311", VarE "a308"]) $
                       VarE "b312")


buildTreeSumMainExp :: Exp2
buildTreeSumMainExp = Ext $ LetRegionE (VarR "r313") Undefined Nothing $
                      Ext $ LetLocE (Single "l314") (StartOfRegionLE (VarR "r313")) $
                      LetE ("z315",[],ProdTy [IntTy, PackedTy "Tree" (Single "l314")],
                               AppE "buildTreeSum" [(Single "l314")] [LitE 3]) $
                      VarE "z315"


buildTreeSumProg :: Prog2
buildTreeSumProg = Prog ddtree (M.fromList [( "buildTreeSum", buildTreeSumFun)]) (Just (buildTreeSumMainExp, ProdTy [IntTy, PackedTy "Tree" (Single "l314")]))

--------------------------------------------------------------------------------

sumTreeFun :: FunDef2
sumTreeFun = FunDef "sumTree" [ "tr762"] sumTreeTy sumTreeBod (FunMeta Rec NoInline False)
  where
    sumTreeTy :: ArrowTy2 Ty2
    sumTreeTy = ArrowTy2
                      [LRM (Single "lin761") (AoSR $ VarR "r760") Input]
                      [PackedTy "Tree" (Single "lin761")]
                      (S.empty)
                      (IntTy)
                      []
                      False

    sumTreeBod :: Exp2
    sumTreeBod = CaseE (VarE "tr762")
                 [ ("Leaf", [("n763", (Single "l764"))],
                   VarE "n763")
                 , ("Node", [("x764",(Single "l765")), ("y766", (Single "l767"))],
                   LetE ("sx768", [], IntTy,
                            AppE "sumTree" [(Single "l765")] [VarE "x764"]) $
                   LetE ("sy769", [], IntTy,
                            AppE "sumTree" [(Single "l767")] [VarE "y766"]) $
                   LetE ("total770", [], IntTy ,
                            PrimAppE AddP [VarE "sx768", VarE "sy769"]) $
                   VarE "total770"
                   )]

sumTreeMainExp :: Exp2
sumTreeMainExp = Ext $ LetRegionE (VarR "r771") Undefined Nothing $
                 Ext $ LetLocE (Single "l772") (StartOfRegionLE (VarR "r771")) $
                 LetE ("tr773", [], PackedTy "Tree" (Single "l772"),
                          AppE "buildTree" [(Single "l772")] [LitE 3]) $
                 LetE ("sum774", [], IntTy,
                          AppE "sumTree" [(Single "l772")] [VarE "tr773"]) $
                 VarE "sum774"

sumTreeProg :: Prog2
sumTreeProg = Prog ddtree (M.fromList [( "buildTree", buildTreeFun),
                                       ( "sumTree", sumTreeFun)
                                      ])
                   (Just (sumTreeMainExp, IntTy))

--------------------------------------------------------------------------------

printTupMainExp :: Exp2
printTupMainExp = Ext $ LetRegionE (VarR "r325") Undefined Nothing $
                  Ext $ LetLocE (Single "l326") (StartOfRegionLE (VarR "r325")) $
                  LetE ("i327",[], IntTy, LitE 42) $
                  LetE ("x328",[], PackedTy "Tree" (Single "l326"),
                           DataConE (Single "l326") "Leaf" [LitE 1]) $
                  LetE ("t329",[], ProdTy [IntTy, PackedTy "Tree" (Single "l326")],
                           MkProdE [VarE "i327", VarE "x328"]) $
                  VarE "t329"

printTupProg :: Prog2
printTupProg = Prog ddtree M.empty (Just (printTupMainExp, ProdTy [IntTy, PackedTy "Tree" (Single "l326")]))

--------------------------------------------------------------------------------

printTupMainExp2 :: Exp2
printTupMainExp2 = Ext $ LetRegionE (VarR "r400") Undefined Nothing $
                  Ext $ LetLocE (Single "l401") (StartOfRegionLE (VarR "r400")) $
                  LetE ("x402",[], PackedTy "Tree" (Single "l401"),
                           AppE "buildTree" [(Single "l401")] [LitE 2]) $
                  Ext $ LetLocE (Single "l403") (AfterVariableLE "x402" (Single "l401") True) $
                  LetE ("y404",[], PackedTy "Tree" (Single "l403"),
                           AppE "buildTree" [(Single "l403")] [LitE 1]) $
                  LetE ("z405",[], ProdTy [PackedTy "Tree" (Single "l401"), PackedTy "Tree" (Single "l403")],
                           MkProdE [VarE "x402", VarE "y404"]) $
                  VarE "z405"

printTupProg2 :: Prog2
printTupProg2 = Prog ddtree (M.fromList [( "buildTree", buildTreeFun)])
                (Just (printTupMainExp2,
                       ProdTy [PackedTy "Tree" (Single "l401"), PackedTy "Tree" (Single "l403")]))

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
addTreesFun = FunDef "addTrees" [ "trees354"] addTreesTy addTreesBod (FunMeta Rec NoInline False)
  where
    addTreesTy :: ArrowTy2 Ty2
    addTreesTy = ArrowTy2
                  [LRM (Single "lin351") (AoSR $ VarR "r350") Input,
                   LRM (Single "lin352") (AoSR $ VarR "r351") Input,
                   LRM (Single "lout353") (AoSR $ VarR "r754") Output]
                  [ProdTy [PackedTy "Tree" (Single "lin351"), PackedTy "Tree" (Single "lin352")]]
                  (S.empty)
                  (PackedTy "Tree" (Single "lout353"))
                  []
                  False

    addTreesBod :: Exp2
    addTreesBod = LetE ("tree1",[],PackedTy "Tree" (Single "lin351"),
                           ProjE 0 (VarE "trees354")) $
                  LetE ("tree2",[],PackedTy "Tree" (Single "lin352"),
                           ProjE 1 (VarE "trees354")) $
                  CaseE (VarE "tree1")
                  [("Leaf", [("n355",(Single "l356"))],
                    CaseE (VarE "tree2")
                       [("Leaf",[("n357",(Single "l358"))],
                         LetE ("n358",[],IntTy,PrimAppE AddP [VarE "n355",VarE "n357"]) $
                         LetE ("x359",[],PackedTy "Tree" (Single "lout353"),
                                  DataConE (Single "lout353") "Leaf" [VarE "n358"]) $
                         VarE "x359"
                        )]
                   ),
                    ("Node", [("x360",(Single "l361")), ("y362",(Single "l363"))],
                     CaseE (VarE "tree2")
                        [("Node", [("x364",(Single "l365")), ("y366", (Single "l367"))],
                          Ext $ LetLocE (Single "l368") (AfterConstantLE 1 (Single "lout353")) $
                          LetE ("tree3",[],ProdTy [PackedTy "Tree" (Single "l361"),
                                                      PackedTy "Tree" (Single "l365")],
                                   MkProdE [VarE "x360", VarE "x364"]) $
                          LetE ("x369",[],PackedTy "Tree" (Single "l368"),
                                   AppE "addTrees" [(Single "l361"),(Single "l365"),(Single "l368")] [VarE "tree3"]) $
                          Ext $ LetLocE (Single "l370") (AfterVariableLE "x369" (Single "l368") True) $
                          LetE ("tree4",[],ProdTy [PackedTy "Tree" (Single "l363"),
                                                      PackedTy "Tree" (Single "l367")],
                                   MkProdE [VarE "y362", VarE "y366"]) $
                          LetE ("y371",[],PackedTy "Tree" (Single "l370"),
                                   AppE "addTrees" [(Single "l363"),(Single "l367"),(Single "l370")] [VarE "tree4"]) $
                          LetE ("z372",[],PackedTy "Tree" (Single "lout353"),
                                    DataConE (Single "lout353") "Node" [VarE "x369", VarE "y371"]) $
                          VarE "z372"
                         )]
                    )]

addTreesMainExp :: Exp2
addTreesMainExp = Ext $ LetRegionE (VarR "r400") Undefined Nothing $
                  Ext $ LetLocE (Single "l401") (StartOfRegionLE (VarR "r400")) $
                  LetE ("x402",[], PackedTy "Tree" (Single "l401"),
                           AppE "buildTree" [(Single "l401")] [LitE 2]) $
                  -- Ext $ LetLocE "l403" (AfterVariableLE "x402" "l401" True) $
                  Ext $ LetRegionE (VarR "r403") Undefined Nothing $
                  Ext $ LetLocE (Single "l403") (StartOfRegionLE (VarR "r403")) $
                  LetE ("y404",[], PackedTy "Tree" (Single "l403"),
                           AppE "buildTree" [(Single "l403")] [LitE 2]) $
                  LetE ("z405",[], ProdTy [PackedTy "Tree" (Single "l401"), PackedTy "Tree" (Single "l403")],
                           MkProdE [VarE "x402", VarE "y404"]) $
                  Ext $ LetRegionE (VarR "r405") Undefined Nothing $
                  Ext $ LetLocE (Single "l406") (StartOfRegionLE (VarR "r405")) $
                  LetE ("a407",[],PackedTy "Tree" (Single "l406"),
                           AppE "addTrees" [(Single "l401"),(Single "l403"),(Single "l406")] [VarE "z405"]) $
                  VarE "a407"

addTreesProg :: Prog2
addTreesProg = Prog ddtree (M.fromList [( "addTrees", addTreesFun)
                                       ,( "buildTree", buildTreeFun)])
                    (Just (addTreesMainExp, PackedTy "Tree" (Single "l406")))

--------------------------------------------------------------------------------

testProdFun :: FunDef2
testProdFun = FunDef "testprod" [ "tup130"] testprodTy testprodBod (FunMeta Rec NoInline False)
  where
    testprodTy = ArrowTy2
                  [LRM (Single "lin131") (AoSR $ VarR "r132") Input, LRM (Single "lout133") (AoSR $ VarR "r755") Output]
                  [ProdTy [(PackedTy "Tree" (Single "lin131")), IntTy]]
                  (S.empty)
                  (ProdTy [(PackedTy "Tree" (Single "lout133")), IntTy])
                  []
                  False
    testprodBod = LetE ("t134",[], PackedTy "Tree" (Single "lin131"), ProjE 0 (VarE "tup130")) $
                  LetE ("i135",[], IntTy, ProjE 1 (VarE "tup130")) $
                  CaseE (VarE "t134")
                  [("Leaf",[("n136",(Single "l137"))],
                    LetE ("v138",[],IntTy, PrimAppE AddP [VarE "n136", LitE 1]) $
                    LetE ("lf139",[],PackedTy "Tree" (Single "lout133"),
                            DataConE (Single "lout133") "Leaf" [VarE "v138"]) $
                    LetE ("tup148",[], ProdTy [PackedTy "Tree" (Single "lout133"), IntTy],
                       MkProdE [VarE "lf139", VarE "i135"]) $
                    VarE "tup148"
                   ),
                   ("Node",[("x140",(Single "l141")), ("y142",(Single "l143"))],
                    Ext $ LetLocE (Single "l144") (AfterConstantLE 1 (Single "lout133")) $
                    LetE ("tup145",[], ProdTy [PackedTy "Tree" (Single "l144"), IntTy],
                             AppE "testprod" [(Single "l141"),(Single "l144")]
                             [MkProdE [VarE "x140", VarE "i135"]]) $

                    LetE ("x149",[], PackedTy "Tree" (Single "l144"), ProjE 0 (VarE "tup145")) $
                    Ext $ LetLocE (Single "l146") (AfterVariableLE "x149" (Single "l144") True) $
                    LetE ("tup147",[], ProdTy [PackedTy "Tree" (Single "l146"), IntTy],
                            AppE "testprod" [(Single "l143"),(Single "l146")]
                            [MkProdE [VarE "y142", VarE "i135"]]) $
                    LetE ("y150",[], PackedTy "Tree" (Single "l146"), ProjE 0 (VarE "tup147")) $
                    LetE ("node151",[], PackedTy "Tree" (Single "lout133"),
                            DataConE (Single "lout133") "Node" [VarE "x149", VarE "y150"]) $
                    LetE ("tup152",[],ProdTy [PackedTy "Tree" (Single "lout133"), IntTy],
                            MkProdE [VarE "node151", VarE "i135"]) $
                    VarE "tup152")
                  ]

testProdProg :: Prog2
testProdProg = Prog ddtree (M.fromList [( "testprod", testProdFun)]) Nothing

--------------------------------------------------------------------------------

-- Meaningless program, just to test flattenL2
testFlattenProg :: Prog2
testFlattenProg = Prog M.empty (M.fromList [( "intAdd",intAddFun)]) $ Just (testFlattenBod, IntTy)
  where
    testFlattenBod :: Exp2
    testFlattenBod =
      Ext $ LetRegionE (VarR "_") Undefined Nothing $
      Ext $ LetLocE (Single "_") (StartOfRegionLE (VarR "_")) $
      Ext $ LetLocE (Single "_") (AfterConstantLE 1 (Single "_")) $
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
                               , (False, PackedTy "STree" (Single "l"))
                               , (False, PackedTy "STree" (Single "l"))])
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
sumUpFun = FunDef "sumUp" [ "tr1"] sumUpFunTy sumUpFunBod (FunMeta Rec NoInline False)
  where
    sumUpFunTy :: ArrowTy2 Ty2
    sumUpFunTy = ArrowTy2
                  [LRM (Single "lin501") (AoSR $ VarR "r500") Input, LRM (Single "lout502") (AoSR $ VarR "r756") Output]
                  [PackedTy "STree" (Single "lin501")]
                  (S.empty)
                  (PackedTy "STree" (Single "lout502"))
                  []
                  False


    sumUpFunBod :: Exp2
    sumUpFunBod = CaseE (VarE "tr1")
      [ ("Leaf", [("n503",(Single "l504"))],
          LetE ("x505",[],PackedTy "STree" (Single "lout502"),
                   DataConE (Single "lout502") "Leaf" [VarE "n503"]) $
          VarE "x505")

      , ("Inner", [("i506",(Single "l507")),("b508", (Single "l509")),("x510", (Single "l511")),("y512", (Single "l513"))],
         Ext $ LetLocE (Single "l514") (AfterConstantLE 1 (Single "lout502")) $
         Ext $ LetLocE (Single "l550") (AfterVariableLE "i506" (Single "l514") True) $
         Ext $ LetLocE (Single "l551") (AfterVariableLE "b508" (Single "l550") True) $
         LetE ("x515",[],PackedTy "STree" (Single "l551"),
                   AppE "sumUp" [(Single "l511"),(Single "l551")] [VarE "x510"]) $
         Ext $ LetLocE (Single "l516") (AfterVariableLE "x515" (Single "l551") True) $
         LetE ("y517",[],PackedTy "STree" (Single "l516"),
                  AppE "sumUp" [(Single "l513"),(Single "l516")] [VarE "y512"]) $
         LetE ("v518",[],IntTy, AppE "valueSTree" [(Single "l551")] [VarE "x515"]) $
         LetE ("v519",[],IntTy, AppE "valueSTree" [(Single "l516")] [VarE "y517"]) $
         LetE ("v520",[],IntTy, PrimAppE AddP [VarE "v518", VarE "v519"]) $
         LetE ("z521",[],PackedTy "STree" (Single "lout502"),
                  DataConE (Single "lout502") "Inner" [VarE "v520", VarE "b508",
                                                 VarE "x515", VarE "y517"]) $
         VarE "z521"
        )]


valueSTreeFun :: FunDef2
valueSTreeFun = FunDef "valueSTree" [ "tr522"] valueSTreeFunTy valueSTreeFunBod (FunMeta Rec NoInline False)
  where
    valueSTreeFunTy :: ArrowTy2 Ty2
    valueSTreeFunTy = ArrowTy2
                       [LRM (Single "lin524") (AoSR $ VarR "r523") Input]
                       [PackedTy "STree" (Single "lin524")]
                       (S.empty)
                       (IntTy)
                       []
                       False

    valueSTreeFunBod :: Exp2
    valueSTreeFunBod = CaseE (VarE "tr522")
      [ ("Leaf", [("n523",(Single "l524"))],
          VarE "n523")

      , ("Inner", [("i525",(Single "l526")),("b527",(Single "l528")),("x529",(Single "l530")),("y531",(Single "l532"))],
         VarE "i525"
      )]


buildSTreeFun :: FunDef2
buildSTreeFun = FunDef "buildSTree" [ "i543"] buildSTreeTy buildSTreeBod (FunMeta Rec NoInline False)
  where
    buildSTreeTy :: ArrowTy2 Ty2
    buildSTreeTy = ArrowTy2
                    [LRM (Single "lout541") (AoSR $ VarR "r540") Output]
                    [IntTy]
                    (S.empty)
                    (PackedTy "STree" (Single "lout541"))
                    []
                    False

    buildSTreeBod :: Exp2
    buildSTreeBod = LetE ("b542",[], BoolTy, PrimAppE EqIntP [VarE "i543", LitE 0]) $
                   IfE (VarE "b542")
                   (DataConE (Single "lout541") "Leaf" [LitE 1])
                   (LetE ("i548",[], IntTy, PrimAppE SubP [VarE "i543", LitE 1]) $
                    LetE ("i554",[], IntTy, LitE 0) $
                    LetE ("b555",[], IntTy, LitE 0) $
                    Ext $ LetLocE (Single "l544") (AfterConstantLE 1 (Single "lout541")) $
                    Ext $ LetLocE (Single "l552") (AfterVariableLE "i554" (Single "l544") True) $
                    Ext $ LetLocE (Single "l553") (AfterVariableLE "b555" (Single "l552") True) $
                    LetE ("x545",[],PackedTy "STree" (Single "l553"),
                             AppE "buildSTree" [(Single "l553")] [VarE "i548"]) $
                    Ext $ LetLocE (Single "l545") (AfterVariableLE "x545" (Single "l553") True) $
                    LetE ("y546",[],PackedTy "STree" (Single "l545"),
                             AppE "buildSTree" [(Single "l545")] [VarE "i548"]) $
                    LetE ("a547",[],PackedTy "STree" (Single "lout541"),
                             DataConE (Single "lout541") "Inner" [VarE "i554", VarE "b555",
                                                            VarE "x545", VarE "y546"]) $
                    VarE "a547")


buildSTreeMainExp :: Exp2
buildSTreeMainExp = Ext $ LetRegionE (VarR "r530") Undefined Nothing $
                    Ext $ LetLocE (Single "l531") (StartOfRegionLE (VarR "r530")) $
                    LetE ("x532",[], PackedTy "STree" (Single "l531"),
                             AppE "buildSTree" [(Single "l531")] [LitE 3]) $
                    VarE "x532"


buildSTreeProg :: Prog2
buildSTreeProg = Prog stree (M.fromList [( "buildSTree", buildSTreeFun)])
                      (Just (buildSTreeMainExp, PackedTy "STree" (Single "l531")))


--------------------------------------------------------------------------------

sumSTreeFun :: FunDef2
sumSTreeFun = FunDef "sumSTree" [ "tr762"] sumSTreeTy sumSTreeBod (FunMeta Rec NoInline False)
  where
    sumSTreeTy :: ArrowTy2 Ty2
    sumSTreeTy = ArrowTy2
                      [LRM (Single "lin761") (AoSR $ VarR "r760") Input]
                      [PackedTy "STree" (Single "lin761")]
                      (S.empty)
                      (IntTy)
                      []
                      False

    sumSTreeBod :: Exp2
    sumSTreeBod = CaseE (VarE "tr762")
                 [ ("Leaf", [("n763", (Single "l764"))],
                   VarE "n763")
                 , ("Inner", [("i775", (Single "l776")),("b777", (Single "l778")),
                              ("x764", (Single "l765")), ("y766", (Single "l767"))],
                   LetE ("sx768", [], IntTy,
                            AppE "sumSTree" [(Single "l765")] [VarE "x764"]) $
                   LetE ("sy769", [], IntTy,
                            AppE "sumSTree" [(Single "l767")] [VarE "y766"]) $
                   LetE ("total770", [], IntTy ,
                            PrimAppE AddP [VarE "sx768", VarE "sy769"]) $
                   VarE "total770"
                   )]

sumSTreeMainExp :: Exp2
sumSTreeMainExp = Ext $ LetRegionE (VarR "r771") Undefined Nothing $
                 Ext $ LetLocE (Single "l772") (StartOfRegionLE (VarR "r771")) $
                 LetE ("tr773", [], PackedTy "STree" (Single "l772"),
                          AppE "buildSTree" [(Single "l772")] [LitE 3]) $
                 LetE ("sum774", [], IntTy,
                          AppE "sumSTree" [(Single "l772")] [VarE "tr773"]) $
                 VarE "sum774"

sumSTreeProg :: Prog2
sumSTreeProg = Prog stree (M.fromList [( "buildSTree", buildSTreeFun),
                                       ( "sumSTree", sumSTreeFun)])
                   (Just (sumSTreeMainExp, IntTy))

--------------------------------------------------------------------------------

sumUpMainExp :: Exp2
sumUpMainExp = Ext $ LetRegionE (VarR "r530") Undefined Nothing $
                  Ext $ LetLocE (Single "l531") (StartOfRegionLE (VarR "r530")) $
                  LetE ("x532",[], PackedTy "STree" (Single "l531"),
                           AppE "buildSTree" [(Single "l531")] [LitE 2]) $
                  Ext $ LetRegionE (VarR "r536") Undefined Nothing $
                  Ext $ LetLocE (Single "l537") (StartOfRegionLE (VarR "r536")) $
                  LetE ("z538",[],PackedTy "STree" (Single "l537"),
                           AppE "sumUp" [(Single "l531"),(Single "l537")] [VarE "x532"]) $
                  VarE "z538"

sumUpProg :: Prog2
sumUpProg = Prog stree (M.fromList [( "sumUp", sumUpFun)
                                   ,( "valueSTree", valueSTreeFun)
                                   ,( "buildSTree", buildSTreeFun)
                                   ])
            (Just (sumUpMainExp, PackedTy "STree" (Single "l537")))

--------------------------------------------------------------------------------

evenFun :: FunDef2
evenFun = FunDef "even" [ "i560"] evenFunTy evenFunBod (FunMeta NotRec NoInline False)
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
setEvenFun = FunDef "setEven" [ "tr570"] setEvenFunTy setEvenFunBod (FunMeta Rec NoInline False)
  where
    setEvenFunTy :: ArrowTy2 Ty2
    setEvenFunTy = ArrowTy2
                    [LRM (Single "lin571") (AoSR $ VarR "r570") Input, LRM (Single "lout572") (AoSR $ VarR "r757") Output]
                    [PackedTy "STree" (Single "lin571")]
                    (S.empty)
                    (PackedTy "STree" (Single "lout572"))
                    []
                    False


    setEvenFunBod :: Exp2
    setEvenFunBod = CaseE (VarE "tr570")
      [ ("Leaf", [("n573",(Single "l574"))],
          LetE ("x575",[],PackedTy "STree" (Single "lout572"),
                   DataConE (Single "lout572") "Leaf" [VarE "n573"]) $
          VarE "x575")

      , ("Inner", [("i576",(Single "l577")),("b578",(Single "l579")),("x580",(Single "l581")),("y582",(Single "l583"))],
         Ext $ LetLocE (Single "l584") (AfterConstantLE 1 (Single "lout572")) $
         Ext $ LetLocE (Single "l585") (AfterVariableLE "i576" (Single "l584") True) $
         Ext $ LetLocE (Single "l586") (AfterVariableLE "b578" (Single "l585") True) $
         LetE ("x587",[],PackedTy "STree" (Single "l586"),
                  AppE "setEven" [(Single "l581"),(Single "l586")] [VarE "x580"]) $
         Ext $ LetLocE (Single "l588") (AfterVariableLE "x587" (Single "l586") True) $
         LetE ("y589",[],PackedTy "STree" (Single "l588"),
                  AppE "setEven" [(Single "l583"),(Single "l588")] [VarE "y582"]) $
         LetE ("v590",[],IntTy, AppE "valueSTree" [(Single "l586")] [VarE "x587"]) $
         LetE ("v591",[],IntTy, AppE "valueSTree" [(Single "l588")] [VarE "y589"]) $
         LetE ("v592",[],IntTy, PrimAppE AddP [VarE "v590", VarE "v591"]) $
         LetE ("b593",[],IntTy, AppE "even" [] [VarE "v592"]) $
         LetE ("z594",[],PackedTy "STree" (Single "lout572"),
                  DataConE (Single "lout572") "Inner" [VarE "i576", VarE "b593",
                                                 VarE "x587", VarE "y589"]) $
         VarE "z594"
        )]


setEvenMainExp :: Exp2
setEvenMainExp = Ext $ LetRegionE (VarR "r592") Undefined Nothing $
                 Ext $ LetLocE (Single "l593") (StartOfRegionLE (VarR "r592")) $
                 LetE ("x594",[], PackedTy "STree" (Single "l593"),
                          AppE "buildSTree" [(Single "l593")] [LitE 2]) $
                 Ext $ LetRegionE (VarR "r595") Undefined Nothing $
                 Ext $ LetLocE (Single "l596") (StartOfRegionLE (VarR "r595")) $
                 LetE ("z597",[],PackedTy "STree" (Single "l596"),
                          AppE "setEven" [(Single "l593"),(Single "l596")] [VarE "x594"]) $
                 VarE "z597"


setEvenProg :: Prog2
setEvenProg = Prog stree (M.fromList [( "setEven"   , setEvenFun)
                                     ,( "even"      , evenFun )
                                     ,( "buildSTree", buildSTreeFun)
                                     ,( "valueSTree", valueSTreeFun)
                                     ])
            (Just (setEvenMainExp, PackedTy "STree" (Single "l596")))

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
sumUpSetEvenFun = FunDef "sumUpSetEven" [ "tr600"] sumUpSetEvenFunTy sumUpSetEvenFunBod (FunMeta Rec NoInline False)
  where
    sumUpSetEvenFunTy :: ArrowTy2 Ty2
    sumUpSetEvenFunTy = ArrowTy2
                         [LRM (Single "lin601") (AoSR $ VarR "r600") Input, LRM (Single "lout602") (AoSR $ VarR "r758") Output]
                         [PackedTy "STree" (Single "lin601")]
                         (S.empty)
                         (ProdTy [PackedTy "STree" (Single "lout602"), IntTy])
                         []
                         False


    sumUpSetEvenFunBod :: Exp2
    sumUpSetEvenFunBod = CaseE (VarE "tr600")
      [ ("Leaf", [("n603",(Single "l604"))],
          LetE ("x605",[],PackedTy "STree" (Single "lout602"),
                   DataConE (Single "lout602") "Leaf" [VarE "n603"]) $
          LetE ("tx606",[], ProdTy [PackedTy "STree" (Single "lout602"), IntTy],
                   MkProdE [VarE "x605", VarE "n603"]) $
          VarE "tx606")

      , ("Inner", [("i607",(Single "l608")),("b609", (Single "l610")),("x611", (Single "l612")),("y613", (Single "l622"))],
         Ext $ LetLocE (Single "l614") (AfterConstantLE 1 (Single "lout602")) $
         Ext $ LetLocE (Single "l615") (AfterVariableLE "i607" (Single "l614") True) $
         Ext $ LetLocE (Single "l616") (AfterVariableLE "b609" (Single "l615") True) $
         LetE ("tx617",[], ProdTy [PackedTy "STree" (Single "l616"), IntTy],
                  AppE "sumUpSetEven" [(Single "l612"),(Single "l616")] [VarE "x611"]) $
         LetE ("x618",[],PackedTy "STree" (Single "l616"), ProjE 0 (VarE "tx617")) $
         LetE ("v619",[],IntTy, ProjE 1 (VarE "tx617")) $
         Ext $ LetLocE (Single "l620") (AfterVariableLE "x618" (Single "l616") True) $
         LetE ("tx621",[],ProdTy [PackedTy "STree" (Single "l620"), IntTy],
                  AppE "sumUpSetEven" [(Single "l622"),(Single "l620")] [VarE "y613"]) $
         LetE ("y623",[],PackedTy "STree" (Single "l620"), ProjE 0 (VarE "tx621")) $
         LetE ("v624",[],IntTy, ProjE 1 (VarE "tx621")) $
         LetE ("v625",[],IntTy, PrimAppE AddP [VarE "v619", VarE "v624"]) $
         LetE ("b626",[],IntTy, AppE "even" [] [VarE "v625"]) $
         LetE ("z627",[],PackedTy "STree" (Single "lout602"),
                  DataConE (Single "lout602") "Inner" [VarE "v625", VarE "b626",
                                                 VarE "x618", VarE "y623"]) $
         LetE ("tx638",[], ProdTy [PackedTy "STree" (Single "lout602"), IntTy],
                  MkProdE [VarE "z627", VarE "v625"]) $
         VarE "tx638")
      ]


sumUpSetEvenExp :: Exp2
sumUpSetEvenExp = Ext $ LetRegionE (VarR "r628") Undefined Nothing $
                  Ext $ LetLocE (Single "l629") (StartOfRegionLE (VarR "r628")) $
                  LetE ("z630",[], PackedTy "STree" (Single "l629"),
                           AppE "buildSTree" [(Single "l629")] [LitE 3]) $
                  Ext $ LetRegionE (VarR "r631") Undefined Nothing $
                  Ext $ LetLocE (Single "l632") (StartOfRegionLE (VarR "r631")) $
                  LetE ("z633",[],ProdTy [PackedTy "STree" (Single "l632"), IntTy],
                           AppE "sumUpSetEven" [(Single "l629"),(Single "l632")] [VarE "z630"]) $
                  VarE "z633"


sumUpSetEvenProg :: Prog2
sumUpSetEvenProg = Prog stree (M.fromList [( "sumUpSetEven", sumUpSetEvenFun)
                                          ,( "even"        , evenFun )
                                          ,( "buildSTree"  , buildSTreeFun)
                                          ])
            (Just (sumUpSetEvenExp, ProdTy [PackedTy "STree" (Single "l632"), IntTy]))

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
                                    (False,PackedTy "Expr" (Single "l")),
                                    (False,PackedTy "Expr" (Single "l"))])
                      ]]

copyExprFun :: FunDef2
copyExprFun = FunDef "copyExpr" [ "e700"] copyExprFunTy copyExprFunBod (FunMeta Rec NoInline False)
  where
    copyExprFunTy :: ArrowTy2 Ty2
    copyExprFunTy = ArrowTy2
                     [LRM (Single "lin702") (AoSR $ VarR "r701") Input,
                      LRM (Single "lout703") (AoSR $ VarR "r759") Output]
                     [PackedTy "Expr" (Single "lin702")]
                     (S.empty)
                     (PackedTy "Expr" (Single "lout703"))
                     []
                     False

    copyExprFunBod :: Exp2
    copyExprFunBod = CaseE (VarE "e700")
                     [ ("VARREF", [("v704",(Single "l705"))],
                        DataConE (Single "lout703") "VARREF" [VarE "v704"]
                       )
                     , ("LETE", [("v706",(Single "l707")), ("rhs708", (Single "l709")), ("bod710", (Single "l711"))],
                        Ext $ LetLocE (Single "l712") (AfterConstantLE 1 (Single "lout703")) $
                        Ext $ LetLocE (Single "l713") (AfterVariableLE "v706" (Single "l712") True) $
                        LetE ("rhs714",[], PackedTy "Expr" (Single "l713"),
                                 AppE "copyExpr" [(Single "l709"),(Single "l713")] [VarE "rhs708"]) $
                        Ext $ LetLocE (Single "l715") (AfterVariableLE "rhs714" (Single "l713") True) $
                        LetE ("bod716",[],PackedTy "Expr" (Single "l715"),
                                 AppE "copyExpr" [(Single "l711"), (Single "l715")] [VarE "bod710"]) $
                        LetE ("z717",[],PackedTy "Expr" (Single "lout703"),
                                 DataConE (Single "lout703") "LETE" [VarE "v706", VarE "rhs714", VarE "bod716"]) $
                        VarE "z717")
                     ]


substFun :: FunDef2
substFun = FunDef "subst" [ "tr653"] substFunTy substFunBod (FunMeta Rec NoInline False)
  where
    substFunTy :: ArrowTy2 Ty2
    substFunTy = ArrowTy2
                  [LRM (Single "lin651") (AoSR $ VarR "r650") Input,
                   LRM (Single "lin652") (AoSR $ VarR "r650") Input,
                   LRM (Single "lout653") (AoSR $ VarR "r760") Output]
                  [ProdTy [IntTy,
                           PackedTy "Expr" (Single "lin651"),
                           PackedTy "Expr" (Single "lin652")]]
                  (S.empty)
                  (PackedTy "Expr" (Single "lout653"))
                  []
                  False

    substFunBod :: Exp2
    substFunBod = LetE ("old654",[],IntTy, ProjE 0 (VarE "tr653")) $
                  LetE ("new655",[],PackedTy "Expr" (Single "lin651"),
                           ProjE 1 (VarE "tr653")) $
                  LetE ("expr656",[],PackedTy "Expr" (Single "lin652"),
                           ProjE 2 (VarE "tr653")) $
                  CaseE (VarE "expr656")
                  [ ("VARREF", [("v657",(Single "l658"))],
                     LetE ("b659",[], BoolTy,
                              PrimAppE EqIntP [VarE "v657", VarE "old654"]) $
                     IfE (VarE "b659")
                     (AppE "copyExpr" [(Single "lin651"), (Single "lout653")] [VarE "new655"])
                     (DataConE (Single "lout653") "VARREF" [VarE "v657"]))
                  , ("LETE", [("v656",(Single "l657")), ("rhs658",(Single "l659")), ("bod660", (Single "l661"))],
                     LetE ("b662",[],BoolTy,
                              PrimAppE EqIntP [VarE "v656", VarE "old654"])
                     -- IfE (VarE "b662")
                     (Ext $ LetLocE (Single "l663") (AfterConstantLE 1 (Single "lout653")) $
                      Ext $ LetLocE (Single "l664") (AfterVariableLE "v656" (Single "l663") True) $
                      LetE ("p668",[], ProdTy [IntTy, PackedTy "Expr" (Single "lin651"), PackedTy "Expr" (Single "l659")],
                               MkProdE [VarE "old654", VarE "new655", VarE "rhs658"]) $
                      LetE ("rhs665",[],PackedTy "Expr" (Single "l664"),
                               AppE "subst" [(Single "lin651"), (Single "l659"), (Single "l664")] [VarE "p668"]) $
                      Ext $ LetLocE (Single "l669") (AfterVariableLE "rhs665" (Single "l664") True) $
                      LetE ("bod670",[], PackedTy "Expr" (Single "l669"),
                               AppE "copyExpr" [(Single "l661"), (Single "l669")] [VarE "bod660"]) $
                      LetE ("z671",[], PackedTy "Expr" (Single "lout653"),
                               DataConE (Single "lout653") "LETE" [VarE "v656", VarE "rhs665", VarE "bod670"]) $
                      VarE "z671")
                    )
                  ]


substMainExp :: Exp2
substMainExp = Ext $ LetRegionE (VarR "r720") Undefined Nothing $
               Ext $ LetLocE (Single "l721") (StartOfRegionLE (VarR "r720")) $
               Ext $ LetLocE (Single "l722") (AfterConstantLE 1 (Single "l721")) $
               Ext $ LetLocE (Single "l723") (AfterConstantLE 8 (Single "l722")) $
               LetE ("rhs724",[], PackedTy "Expr" (Single "l723"),
                        DataConE (Single "l723") "VARREF" [LitE 1]) $
               Ext $ LetLocE (Single "l724") (AfterVariableLE "rhs724" (Single "l723") True) $
               LetE ("bod725",[], PackedTy "Expr" (Single "l724"),
                        DataConE (Single "l724") "VARREF" [LitE 10]) $
               LetE ("old726",[],IntTy,LitE 1) $
               LetE ("z727",[], PackedTy "Expr" (Single "l721"),
                        DataConE (Single "l721") "LETE" [VarE "old726", VarE "rhs724", VarE "bod725"]) $
               Ext $ LetRegionE (VarR "r728") Undefined Nothing $
               Ext $ LetLocE (Single "l729") (StartOfRegionLE (VarR "r728")) $
               LetE ("new730",[],PackedTy "Expr" (Single "l729"),
                        DataConE (Single "l729") "VARREF" [LitE 42]) $
               LetE ("p731",[],ProdTy [IntTy, PackedTy "Expr" (Single "l729"), PackedTy "Expr" (Single "l721")],
                        MkProdE [VarE "old726", VarE "new730", VarE "z727"]) $
               Ext $ LetLocE (Single "l730") (AfterVariableLE "new730" (Single "l729") True) $
               LetE ("z732",[], PackedTy "Expr" (Single "l730"),
                        AppE "subst" [(Single "l729"), (Single "l721"), (Single "l730")] [VarE "p731"]) $
               VarE "z732"


substProg :: Prog2
substProg = Prog ddexpr (M.fromList [( "subst", substFun),
                                     ( "copyExpr", copyExprFun)])
            (Just (substMainExp, PackedTy "Expr" (Single "l730")))

--------------------------------------------------------------------------------

ddtree' :: DDefs Ty2
ddtree' = fromListDD [DDef (toVar "Tree") []
                       [ ("Leaf",[(False,IntTy)])
                       , ("Node",[ (False,PackedTy "Tree" (Single "l"))
                                 , (False,PackedTy "Tree" (Single "l"))])
                       , ("Node^", [ (False,CursorTy)
                                   , (False,PackedTy "Tree" (Single "l"))
                                   , (False,PackedTy "Tree" (Single "l"))])
                       , (indirectionTag++"1", [(False,CursorTy)])
                       ]]

-- The rightmost function *without* copy-insertion. Gibbon should add and use
-- indirection pointers to get to the rightmost node of the tree.

indrBuildTreeFun :: FunDef2
indrBuildTreeFun = FunDef "indrBuildTree" [ "i270"] indrBuildTreeTy indrBuildTreeBod (FunMeta Rec NoInline False)
  where
    indrBuildTreeTy :: ArrowTy2 Ty2
    indrBuildTreeTy = ArrowTy2
                   [LRM (Single "lout272") (AoSR $ VarR "r271") Output]
                   [IntTy]
                   (S.empty)
                   (PackedTy "Tree" (Single "lout272"))
                   []
                   False

    indrBuildTreeBod :: Exp2
    indrBuildTreeBod = LetE ("b279",[], BoolTy, PrimAppE EqIntP [VarE "i270", LitE 0]) $
                       IfE (VarE "b279")
                       (DataConE (Single "lout272") "Leaf" [LitE 1])
                       (LetE ("i273",[], IntTy, PrimAppE SubP [VarE "i270", LitE 1]) $
                        Ext $ LetLocE (Single "loc_indr") (AfterConstantLE 1 (Single "lout272")) $
                        Ext $ LetLocE (Single "l274") (AfterConstantLE 8 (Single "loc_indr")) $
                        LetE ("x275",[],PackedTy "Tree" (Single "l274"),
                                 AppE "indrBuildTree" [(Single "l274")] [VarE "i273"]) $
                        Ext $ LetLocE (Single "l276") (AfterVariableLE "x275" (Single "l274") True) $
                        LetE ("y277",[],PackedTy "Tree" (Single "l276"),
                                 AppE "indrBuildTree" [(Single "l276")] [VarE "i273"]) $
                        LetE ("indr_cur",[],CursorTy,Ext (StartOfPkdCursor "y277"))  $
                        -- LetE ("indr_node",[], PackedTy "Tree" "loc_indr",
                        --          DataConE "loc_indr" (indirectionTag++"1") [VarE "indr_cur"]) $
                        LetE ("a278",[],PackedTy "Tree" (Single "lout272"),
                                 DataConE (Single "lout272") "Node^" [VarE "indr_cur",
                                                                VarE "x275",
                                                                VarE "y277"]) $
                        VarE "a278")

indrBuildTreeMainExp :: Exp2
indrBuildTreeMainExp = Ext $ LetRegionE (VarR "r800") Undefined Nothing $
                       Ext $ LetLocE (Single "l801") (StartOfRegionLE (VarR "r800")) $
                       LetE ("tr802", [], PackedTy "Tree" (Single "l801"),
                                AppE "indrBuildTree" [(Single "l801")] [LitE 3]) $
                       VarE "tr802"

indrBuildTreeProg :: Prog2
indrBuildTreeProg = Prog ddtree' (M.fromList [( "indrBuildTree", indrBuildTreeFun)])
                         (Just (indrBuildTreeMainExp, PackedTy "Tree" (Single "l801")))


indrRightmostFun :: FunDef2
indrRightmostFun = FunDef "indrRightmost" [ "t742"] indrRightmostTy indrRightmostBod (FunMeta Rec NoInline False)
  where
    indrRightmostTy :: ArrowTy2 Ty2
    indrRightmostTy = ArrowTy2
                       [LRM (Single "lin741") (AoSR $ VarR "r740") Input]
                       [PackedTy "Tree" (Single "lin741")]
                       S.empty
                       IntTy
                       []
                       False

indrRightmostBod :: Exp2
indrRightmostBod = CaseE (VarE "t742")
               [("Leaf", [("n746",(Single "l747"))],
                 VarE "n746"),
                ("Node^", [("indr_y750",(Single "lindr_y750")),("x748",(Single "l749")), ("y750",(Single "l751"))],
                 LetE ("lm752",[],IntTy, AppE "indrRightmost" [(Single "l751")] [VarE "y750"]) $
                 VarE "lm752")]

indrRightmostMainExp :: Exp2
indrRightmostMainExp = Ext $ LetRegionE (VarR "r753") Undefined Nothing $
                       Ext $ LetLocE (Single "l754") (StartOfRegionLE (VarR "r753")) $
                       LetE ("tr1", [], PackedTy "Tree" (Single "l754"),
                                AppE "indrBuildTree" [(Single "l754")] [LitE 3]) $
                       LetE ("a760",[], IntTy,
                                AppE "indrRightmost" [(Single "l754")] [VarE "tr1"]) $
                       VarE "a760"

indrRightmostProg :: Prog2
indrRightmostProg = Prog ddtree' (M.fromList [( "indrRightmost", indrRightmostFun)
                                             ,( "indrBuildTree",indrBuildTreeFun)])
                    (Just (indrRightmostMainExp, IntTy))

--------------------------------------------------------------------------------

indrIDFun :: FunDef2
indrIDFun = FunDef "indrID" [ "tr800"] indrIDTy indrIDBod (FunMeta NotRec NoInline False)
  where
    indrIDTy :: ArrowTy2 Ty2
    indrIDTy = ArrowTy2
                [LRM (Single "lin802") (AoSR $ VarR "r801") Input, LRM (Single "lout803") (AoSR $ VarR "r803") Output]
                [PackedTy "Tree" (Single "lin802")]
                (S.empty)
                (PackedTy "Tree" (Single "lout803"))
                []
                False

    indrIDBod :: Exp2
    indrIDBod = LetE ("a804",[], PackedTy "Tree" (Single "lout803"),
                         Ext $ IndirectionE "Tree"
                                               (indirectionTag++"1")
                                               ((Single "lout803"),(Single "r803"))
                                               ((Single "lin802"), (Single "r801"))
                                               (LitE 10)) $
                VarE "a804"


--------------------------------------------------------------------------------

indrIDMainExp :: Exp2
indrIDMainExp = Ext $ LetRegionE (VarR "r806") Undefined Nothing $
                Ext $ LetLocE (Single "l807") (StartOfRegionLE (VarR "r806")) $
                LetE ("tr1",[], PackedTy "Tree" (Single "l807"),
                         AppE "indrBuildTree" [(Single "l807")] [LitE 2]) $
                Ext $ LetRegionE (VarR "r808") Undefined Nothing $
                Ext $ LetLocE (Single "l809") (StartOfRegionLE (VarR "r808")) $
                LetE ("tr2",[], PackedTy "Tree" (Single "l809"),
                         AppE "indrID" [(Single "l807"), (Single "l809")] [VarE "tr1"]) $
                LetE ("rmost",[], IntTy,
                          AppE "indrRightmost" [(Single "l809")] [VarE "tr2"]) $
                VarE "rmost"

indrIDProg :: Prog2
indrIDProg = Prog ddtree' (M.fromList [( "indrBuildTree", indrBuildTreeFun)
                                      ,( "indrID", indrIDFun)
                                      ,( "indrRightmost",indrRightmostFun)])
             (Just (indrIDMainExp, IntTy))


--------------------------------------------------------------------------------

indrIDSumMainExp :: Exp2
indrIDSumMainExp = Ext $ LetRegionE (VarR "r806") Undefined Nothing $
                   Ext $ LetLocE (Single "l807") (StartOfRegionLE (VarR "r806")) $
                   LetE ("tr1",[], PackedTy "Tree" (Single "l807"),
                         AppE "buildTree" [(Single "l807")] [LitE 10]) $
                   Ext $ LetRegionE (VarR "r808") Undefined Nothing $
                   Ext $ LetLocE (Single "l809") (StartOfRegionLE (VarR "r808")) $
                   LetE ("tr2",[], PackedTy "Tree" (Single "l809"),
                            AppE "indrID" [(Single "l807"), (Single "l809")] [VarE "tr1"]) $
                   LetE ("total",[], IntTy,
                            AppE "sumTree" [(Single "l809")] [VarE "tr2"]) $
                   VarE "total"

indrIDSumProg :: Prog2
indrIDSumProg = Prog ddtree' (M.fromList [( "buildTree", buildTreeFun)
                                         ,( "indrID", indrIDFun)
                                         ,( "sumTree",sumTreeFun)])
                (Just (indrIDSumMainExp, IntTy))

--------------------------------------------------------------------------------

ddsnoclist :: DDefs Ty2
ddsnoclist = fromListDD [DDef (toVar "SnocList") []
                         [ ("Nil", [])
                         , ("Snoc" , [(False,PackedTy "SnocList" (Single "l")),
                                      (False,IntTy)])
                         ]]
