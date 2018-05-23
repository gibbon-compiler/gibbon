{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Gibbon.Pretty ( Pretty(..) ) where

import Gibbon.L1.Syntax
import qualified Gibbon.L2.Syntax as L2
import Gibbon.Common
import Gibbon.GenericOps
import Data.Loc    
import Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.GenericPretty

class Expression e => Pretty e where
    pprint :: e -> Doc

instance Pretty (NoExt l d) where
    pprint _ = empty

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprint (L _ e) = pprint e

instance (Show l, Out l, Pretty (e l (UrTy l)), Expression (e l (UrTy l)), TyOf (e l (UrTy l)) ~ TyOf (PreExp e l (UrTy l)), Pretty (UrTy l)) => Pretty (PreExp e l (UrTy l)) where
    pprint ex0 =
        case ex0 of
          VarE v -> doc v
          LitE i -> int i
          LitSymE v -> doc v
          AppE v ls e -> doc v <+>
                         lbrack <> hcat (punctuate "," (map doc ls)) <> rbrack <+>
                         lparen <> pprint e <> rparen
          PrimAppE pr es -> text (show pr) <> lparen <> hcat (map pprint es) <> rparen
          LetE (v,ls,ty,e1) e2 -> text "let" <+>
                                  doc v <+> colon <+>
                                  hcat (map doc ls) <+>
                                  pprint ty <+>
                                  equals <+>
                                  pprint e1 <+>
                                  text "in" $+$
                                  pprint e2
          IfE e1 e2 e3 -> text "if" <+>
                          pprint e1 $+$
                          text "then" <+>
                          pprint e2 $+$
                          text "else" <+>
                          pprint e3
          MkProdE es -> lparen <> hcat (punctuate (text ",") (map pprint es)) <> rparen
          ProjE i e -> text "#" <> int i <+> pprint e 
          CaseE e bnds -> text "case" <+> pprint e <+> text "of" $+$
                          nest 4 (vcat $ map (\(dc,vls,e) -> text dc <+> hcat (punctuate (text " ") (map (\(v,l) -> vdoc v <> colon <> doc l) vls)) <+> text "->" <+> pprint e) bnds)
          DataConE l dc es -> text dc <+> lbrack <> doc l <> rbrack <+>
                              lparen <> hcat (punctuate (text ",") (map pprint es)) <> rparen
          TimeIt e _ty _b -> pprint e
          Ext ext -> pprint ext -- do we want to print this?
          MapE{} -> error $ "Unexpected form in program: " ++ show ex0
          FoldE{} -> error $ "Unexpected form in program: " ++ show ex0

instance (Show l, Out l, Pretty (L (L2.E2 l (UrTy l)))) => Pretty (L2.E2Ext l (UrTy l)) where
    pprint ex0 =
        case ex0 of
          L2.LetRegionE r e -> text "letregion" <+>
                               doc r <+> text "in" $+$ pprint e
          L2.LetLocE l le e -> text "letloc" <+>
                               doc l <+> equals <+> pprint le <+> text "in" $+$ pprint e
          L2.RetE ls v -> text "return" <+>
                          lbrack <> hcat (punctuate (text ",") (map doc ls)) <> rbrack <+>
                          doc v
          L2.FromEndE l -> text "fromend" <+> doc l
          L2.BoundsCheck i l1 l2 -> text "boundscheck" <+> int i <+> doc l1 <+> text (show l2)
          L2.IndirectionE tc dc (l1,v1) (l2,v2) e -> text "indirection" <+>
                                                     doc tc <+>
                                                     doc dc <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [doc l1,text (fromVar v1)]) <>
                                                     rparen <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [doc l2,text (fromVar v2)]) <>
                                                     rparen <+>
                                                     pprint e

instance (Show l, Out l) => Pretty (L2.PreLocExp l) where
    pprint le =
        case le of
          L2.StartOfLE r -> lparen <> text "startof" <+> text (show r) <> rparen
          L2.AfterConstantLE i l -> lparen <> doc l <+> text "+" <+> int i <> rparen
          L2.AfterVariableLE v l -> lparen <> doc l <+> text "+" <+> doc v <> rparen
          L2.InRegionLE r -> lparen <> text "inregion" <+> text (show r) <> rparen
          L2.FromEndLE l -> lparen <> text "fromend" <+> doc l <> rparen

instance (Show l, Out l) => Pretty (UrTy l) where
    pprint ty =
        case ty of
          IntTy -> text "int"
          BoolTy -> text "bool"
          ProdTy tys -> hcat $ punctuate "," $ map pprint tys
          SymDictTy ty -> text "dict" <+> pprint ty
          PackedTy tc l -> text "packed" <+> text tc <+> doc l
          ListTy ty -> text "list" <+> pprint ty
          PtrTy -> text "ptr"
          CursorTy -> text "cursor"

vdoc :: Var -> Doc
vdoc = text . fromVar


add1FunBod :: L L2.Exp2
add1FunBod = l$ CaseE (l$ VarE "tr1") $
  [ ("Leaf", [("n5","l6")],
      l$ LetE ("v7",[],IntTy,
               l$ PrimAppE AddP [l$ VarE "n5", l$ LitE 1]) $
      l$ LetE ("lf8",[],PackedTy "Tree" "lout4",
               l$ DataConE "lout4" "Leaf" [l$ VarE "v7"]) $
      l$ VarE "lf8")

  , ("Node", [("x9","l10"),("y11","l12")],
     l$ Ext $ L2.LetLocE "l13" (L2.AfterConstantLE 1 "lout4") $
     l$ LetE ("x14",[],PackedTy "Tree" "l13",
               l$ AppE "add1" ["l10","l13"] (l$ VarE "x9")) $
     l$ Ext $ L2.LetLocE "l15" (L2.AfterVariableLE "x14" "l13") $
     l$ LetE ("y16",[],PackedTy "Tree" "l15", l$ AppE "add1" ["l12","l15"] (l$ VarE "y11")) $
     l$ LetE ("z17",[],PackedTy "Tree" "lout4",
              l$ DataConE "lout4" "Node" [ l$ VarE "x14" , l$ VarE "y16"]) $
     l$ VarE "z17")
  ]
