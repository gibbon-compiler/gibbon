module Gibbon.L1.Examples where

import           Data.Map         as M

import           Gibbon.L1.Syntax


--------------------------------------------------------------------------------
treeTy :: Ty1
treeTy = PackedTy "Tree" ()

treeDD :: DDefs (UrTy ())
treeDD =
  (fromListDD
     [ DDef
         "Tree"
         []
         [ ("Leaf", [(False, IntTy)])
         , ("Node", [(False, treeTy), (False, treeTy)])
         ]
     ])

mkAdd1Prog :: Exp1 -> Maybe (Exp1, Ty1) -> Prog1
mkAdd1Prog bod mainExp =
  Prog treeDD (M.fromList [("add1", mkAdd1Fun bod)]) mainExp

mkAdd1Fun :: Exp1 -> FunDef1
mkAdd1Fun bod =
  FunDef
    "add1"
    ["tr"]
    ([treeTy], treeTy)
    bod
    (FunMeta Rec NoInline False NoLayoutOpt Nothing)


----------------

-- | The basic form of the add1 program where recursions happen
-- immediately as arguments to the data-constructor.
add1Prog :: Prog1
add1Prog = mkAdd1Prog exadd1Bod Nothing

exadd1Bod :: Exp1
exadd1Bod =
  CaseE (VarE "tr") $
  [ ("Leaf", [("n", ())], PrimAppE AddP [VarE "n", LitE 1])
  , ( "Node"
    , [("x", ()), ("y", ())]
    , DataConE () "Node" [AppE "add1" [] [VarE "x"], AppE "add1" [] [VarE "y"]])
  ]

exadd1BodLetLeft :: Exp1
exadd1BodLetLeft =
  CaseE (VarE "tr") $
  [ ("Leaf", [("n", ())], PrimAppE AddP [VarE "n", LitE 1])
  , ( "Node"
    , [("x", ()), ("y", ())]
    , LetE ("x2", [], treeTy, AppE "add1" [] [VarE "x"]) $
      LetE ("y2", [], treeTy, AppE "add1" [] [VarE "y"]) $
      DataConE () "Node" [VarE "x2", VarE "y2"])
  ]


-- | A more challenging case where recursions are performed right-to-left
exadd1BodLetRight :: Exp1
exadd1BodLetRight =
  CaseE (VarE "tr") $
  [ ("Leaf", [("n", ())], PrimAppE AddP [VarE "n", LitE 1])
  , ( "Node"
    , [("x", ()), ("y", ())]
    , LetE ("y2", [], treeTy, AppE "add1" [] [VarE "y"]) $
      LetE ("x2", [], treeTy, AppE "add1" [] [VarE "x"]) $
      DataConE () "Node" [VarE "x2", VarE "y2"])
  ]


-- | Add1 program with let bindings, recurring in left-to-right order.
add1ProgLetLeft :: Prog1
add1ProgLetLeft = mkAdd1Prog exadd1BodLetLeft Nothing


-- | Add1 program with let bindings, recurring in right-to-left order.
add1ProgLetRight :: Prog1
add1ProgLetRight = mkAdd1Prog exadd1BodLetRight Nothing


-- | An even more challenging case where there is an (apparent) data
-- dependency where x2 depends on y2.
add1ProgChallenge :: Prog1
add1ProgChallenge =
  Prog
    treeDD
    (M.fromList
       [ ("add1", mkAdd1Fun bod)
       , ( "pred"
         , FunDef
             "pred"
             ["tr"]
             ([treeTy], BoolTy)
             (CaseE (VarE "tr") $
              [ ("Leaf", [("n", ())], PrimAppE MkTrue [])
              , ("Node", [("x", ()), ("y", ())], PrimAppE MkFalse [])
              ])
             (FunMeta Rec NoInline False NoLayoutOpt Nothing))
       ])
    Nothing
  where
    bod =
      CaseE (VarE "tr") $
      [ ("Leaf", [("n", ())], PrimAppE AddP [VarE "n", LitE 1])
      , ( "Node"
        , [("x", ()), ("y", ())]
        , LetE ("y2", [], treeTy, AppE "add1" [] [VarE "y"]) $
          LetE
            ( "x2"
            , []
            , treeTy
            , (IfE
                 (AppE "pred" [] [VarE "y2"])
                 (AppE "add1" [] [VarE "x"])
                 (AppE "add1" [] [VarE "x"]))) $
          DataConE () "Node" [VarE "x2", VarE "y2"])
      ]


-- | This program is a challenge because a packed value flows to two destinations.
add1ProgSharing :: Prog1
add1ProgSharing = Prog treeDD (M.fromList [("add1", mkAdd1Fun bod)]) Nothing
  where
    bod =
      CaseE (VarE "tr") $
      [ ("Leaf", [("n", ())], PrimAppE AddP [VarE "n", LitE 1])
      , ( "Node"
        , [("x", ()), ("y", ())]
        , LetE ("x2", [], treeTy, AppE "add1" [] [VarE "x"]) $
          DataConE () "Node" [VarE "x2", VarE "x2"])
      ]
