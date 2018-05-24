{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Gibbon.Pretty ( Printer(..), Pretty(..), printL1, printL2, printL3 ) where

import Gibbon.L1.Syntax
import qualified Gibbon.L2.Syntax as L2
import qualified Gibbon.L3.Syntax as L3
import qualified Gibbon.L4.Syntax as L4
import Gibbon.Common
import Gibbon.GenericOps
import Data.Loc
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.GenericPretty

class Printer a where
    pprinter :: a -> String

printL1 :: Prog -> String
printL1 (Prog _ funs me) =
    let meDoc = case me of
                  Nothing -> empty
                  Just (e,_) -> renderMain $ pprint e
        funsDoc = vcat $ map (\fd -> renderfunc (fromVar $ funName fd) (doc $ funArg fd) (doc $ fst $ funTy fd) (pprint $ funBody fd)) $ M.elems funs 
    in render $ funsDoc $+$ meDoc

instance Printer Prog where
    pprinter = printL1

printL2 :: L2.Prog -> String
printL2 (L2.Prog _ funs me) =
    let meDoc = case me of
                  Nothing -> empty
                  Just (e,_) -> renderMain $ pprint e
        funsDoc = vcat $ map (\fd -> renderfunc (fromVar $ L2.funName fd) (doc $ L2.funArg fd) (doc $ L2.arrOut $ L2.funTy fd) (pprint $ L2.funBody fd)) $ M.elems funs 
    in render $ funsDoc $+$ meDoc

instance Printer L2.Prog where
    pprinter = printL2

printL3 :: L3.Prog -> String
printL3 (L3.Prog _ funs me) = 
    let meDoc = case me of
                  Nothing -> empty
                  Just (e,_) -> renderMain $ pprint e
        funsDoc = vcat $ map (\fd -> renderfunc (fromVar $ L3.funName fd) (doc $ L3.funArg fd) (doc $ fst $ L3.funTy fd) (pprint $ L3.funBody fd)) $ M.elems funs 
    in render $ funsDoc $+$ meDoc

instance Printer L3.Prog where
    pprinter = printL3

instance Printer L4.Prog where
    pprinter = show -- TODO: implement pretty printing for L4

renderfunc :: String -> Doc -> Doc -> Doc -> Doc
renderfunc f arg ty m = text f <+> arg <> colon <> ty <+> equals $$ nest 4 m 
    
renderMain :: Doc -> Doc
renderMain m = text "main" <+> equals $$ nest 4 m

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
                          nest 4 (vcat $ map (\(dc,vls,e) -> text dc <+> hcat (punctuate (text " ") (map (\(v,l) -> doc v <> colon <> doc l) vls)) <+> text "->" <+> pprint e) bnds)
          DataConE l dc es -> text dc <+> lbrack <> doc l <> rbrack <+>
                              lparen <> hcat (punctuate (text ",") (map pprint es)) <> rparen
          TimeIt e _ty _b -> pprint e
          Ext ext -> pprint ext
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

instance (Show l, Out l) => Pretty (L3.E3Ext l (UrTy l)) where
    pprint = doc -- TODO: replace this with actual pretty printing for L3 forms

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
