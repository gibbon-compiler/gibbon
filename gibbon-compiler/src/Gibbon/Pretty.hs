{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Gibbon.Pretty ( Printer(..), Pretty(..)) where

import Prelude hiding ((<>))
import Data.Loc
import Data.Text (unpack)
import Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.GenericPretty
import qualified Data.Map as M

import Gibbon.L1.Syntax
import Gibbon.L2.Syntax as L2
import Gibbon.L3.Syntax as L3
import Gibbon.Common
import Gibbon.GenericOps
import Gibbon.SExpFrontend (primMap)
import qualified Gibbon.L4.Syntax as L4

class Printer a where
    pprinter :: a -> String

instance (Pretty ex, Pretty (ArrowTy (TyOf ex))) => Printer (Prog ex) where
    pprinter (Prog _ funs me) =
        let meDoc = case me of
                      Nothing -> empty
                      Just (e,_) -> renderMain $ pprint e
            funsDoc = vcat $ map renderfunc $ M.elems funs
        in render $ funsDoc $+$ meDoc

instance Printer L4.Prog where
    pprinter = show -- TODO: implement pretty printing for L4

doubleColon :: Doc
doubleColon = colon <> colon

renderfunc :: forall ex. (Pretty ex, Pretty (ArrowTy (TyOf ex)))
           => FunDef ex -> Doc
renderfunc FunDef{funName,funArg,funTy,funBody} = text (fromVar funName) <+> doubleColon <+> pprint funTy $$
                                                  renderBod <> text "\n"
    where
      renderBod :: Doc
      renderBod = text (fromVar funName) <+> text (fromVar funArg) <+> equals $$ nest 4 (pprint funBody)

-- Function type for L1 and L3
instance Pretty (UrTy (), UrTy ()) where
    pprint (a,b) = pprint a <+> text "->" <+> pprint b

instance Pretty ArrowTy2 where
    -- TODO: start metadata at column 0 instead of aligning it with the type
    pprint fnty = pprint (arrIn fnty) <+> text "->" <+> pprint (arrOut fnty) $$
                  braces (text "locvars" <+> doc (locVars fnty) <> comma $$
                          text "effs: " <+> doc (arrEffs fnty) <> comma $$
                          text "locrets: " <+> doc (locRets fnty))

-- renderFnTy :: forall ex. (Pretty ex, Pretty (TyOf ex), FunctionTy (TyOf ex), Pretty (ArrowTy (TyOf ex)))
--            => FunDef ex -> Doc
-- renderFnTy FunDef{funTy,funName} =
--     text (fromVar funName) <+> doubleColon <+> pprint (inTy @(TyOf ex) funTy) <+>
--     text "->" <+> pprint (outTy @(TyOf ex) funTy)

renderMain :: Doc -> Doc
renderMain m = text "main" <+> equals $$ nest 4 m

class Pretty e where
    pprint :: e -> Doc

instance Pretty (NoExt l d) where
    pprint _ = empty

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprint (L _ e) = pprint e

instance (Show l, Ord l, Out l) => Pretty (Prim (UrTy l)) where
    pprint pr =
        -- We add PEndOf here because it's not exposed to the users, and as a result,
        -- is not defined as a primop in the parser primMap.
        let renderPrim = M.union (M.singleton PEndOf "pendof") $
                         M.fromList (map (\(a,b) -> (b,a)) (M.toList primMap))
        in text (unpack (renderPrim # pr))

instance (Show l, Out l, Eq l, Ord l, Pretty (e l (UrTy l)), Expression (e l (UrTy l)), TyOf (e l (UrTy l)) ~ TyOf (PreExp e l (UrTy l)), Pretty (UrTy l), Pretty l) => Pretty (PreExp e l (UrTy l)) where
    pprint ex0 =
        case ex0 of
          VarE v -> doc v
          LitE i -> int i
          LitSymE v -> doc v
          AppE v ls e -> let docMoreLocs = hcat (punctuate "," (map doc ls))
                         in doc v <+>
                            (if isEmpty docMoreLocs
                            then empty
                            else brackets docMoreLocs) <+>
                            (pprint e)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in pprint a1 <+> pprint pr <+> pprint a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprint pr

                  _ -> pprint pr <> parens (hsep $ map pprint es)

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
                          nest 4 (vcat $ map dobinds bnds)
          DataConE l dc es -> text dc <+>
                              (if isEmpty (pprint l)
                               then empty
                               else doc l) <+>
                              lparen <> hcat (punctuate (text ",") (map pprint es)) <> rparen
          TimeIt e _ty _b -> pprint e
          ParE a b -> pprint a <+> text "||" <+> pprint b
          Ext ext -> pprint ext
          MapE{} -> error $ "Unexpected form in program: " ++ show ex0
          FoldE{} -> error $ "Unexpected form in program: " ++ show ex0
        where
          dobinds (dc,vls,e) = text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,l) -> if isEmpty (pprint l)
                                                                           then doc v
                                                                           else doc v <> colon <> doc l)
                                                            vls))
                               <+> text "->" $+$ nest 4 (pprint e)

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

instance (Out l) => Pretty (L3.E3Ext l (UrTy l)) where
    pprint = doc -- TODO: replace this with actual pretty printing for L3 forms

instance (Out l) => Pretty (L2.PreLocExp l) where
    pprint le =
        case le of
          L2.StartOfLE r -> lparen <> text "startof" <+> text (show r) <> rparen
          L2.AfterConstantLE i l -> lparen <> doc l <+> text "+" <+> int i <> rparen
          L2.AfterVariableLE v l -> lparen <> doc l <+> text "+" <+> doc v <> rparen
          L2.InRegionLE r -> lparen <> text "inregion" <+> text (show r) <> rparen
          L2.FromEndLE l -> lparen <> text "fromend" <+> doc l <> rparen

instance Pretty () where
    pprint _ = empty

instance Pretty LocVar where
    pprint v = text "@" <+> text (fromVar v)

instance (Show l, Out l, Pretty l) => Pretty (UrTy l) where
    pprint ty =
        case ty of
          IntTy -> text "Int"
          BoolTy -> text "Bool"
          ProdTy tys -> parens $ hcat $ punctuate "," $ map pprint tys
          SymDictTy ty -> text "Dict" <+> pprint ty
          PackedTy tc l -> text "Packed" <+> text tc <+> pprint l
          ListTy ty -> text "List" <+> pprint ty
          PtrTy -> text "Ptr"
          CursorTy -> text "Cursor"
