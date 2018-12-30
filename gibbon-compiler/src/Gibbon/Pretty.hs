{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Gibbon.Pretty ( Printer(..), Pretty(..)) where

import           Prelude hiding ((<>))
import           Data.Loc
import           Data.Text (unpack)
import           Text.PrettyPrint as PP
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M

import qualified Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax
import           Gibbon.L2.Syntax as L2
import           Gibbon.L3.Syntax as L3
import           Gibbon.Common
import           Gibbon.SExpFrontend (primMap)
import qualified Gibbon.L4.Syntax as L4

class Printer a where
    pprinter :: a -> String

instance (Pretty ex, Pretty (TyOf ex), Pretty (ArrowTy (TyOf ex))) => Printer (Prog ex) where
    pprinter (Prog _ funs me) =
        let meDoc = case me of
                      Nothing -> empty
                      Just (e,ty) -> renderMain (pprint e) (pprint ty)
            funsDoc = vcat $ map renderfunc $ M.elems funs
        in render $ funsDoc $+$ meDoc

instance Printer L4.Prog where
    pprinter = show -- TODO: implement pretty printing for L4

doublecolon :: Doc
doublecolon = colon <> colon

renderfunc :: forall ex. (Pretty ex, Pretty (ArrowTy (TyOf ex)))
           => FunDef ex -> Doc
renderfunc FunDef{funName,funArg,funTy,funBody} = text (fromVar funName) <+> doublecolon <+> pprint funTy $$
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
--     text (fromVar funName) <+> doublecolon <+> pprint (inTy @(TyOf ex) funTy) <+>
--     text "->" <+> pprint (outTy @(TyOf ex) funTy)

renderMain :: Doc -> Doc -> Doc
renderMain m ty = text "main" <+> doublecolon <+> ty
                    $$ text "main" <+> equals $$ nest 4 m

class Pretty e where
    pprint :: e -> Doc

instance Pretty (NoExt l d) where
    pprint _ = empty

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprint (L _ e) = pprint e

instance (Out d, Show d, Ord d) => Pretty (Prim d) where
    pprint pr =
        -- We add PEndOf here because it's not exposed to the users, and as a result,
        -- is not defined as a primop in the parser primMap.
        let renderPrim = M.union (M.singleton PEndOf "pendof") $
                         M.fromList (map (\(a,b) -> (b,a)) (M.toList primMap))
        in text (unpack (renderPrim # pr))

instance (Show l, Out l, Ord l, Pretty (e l (UrTy l)), TyOf (e l (UrTy l)) ~ TyOf (PreExp e l (UrTy l)), Pretty (UrTy l), Pretty l) => Pretty (PreExp e l (UrTy l)) where
    pprint ex0 = pprintExp (l$ ex0)

pprintExp :: (Out l, Show l, Show d, Out d, Ord d, Pretty (e l d), Pretty l, Pretty d, Pretty (Prim d)) => L (PreExp e l d) -> Doc
pprintExp (L _ ex0) =
        case ex0 of
          VarE v -> doc v
          LitE i -> int i
          LitSymE v -> doc v
          AppE v ls e -> let docMoreLocs = hcat (punctuate "," (map doc ls))
                         in doc v <+>
                            (if isEmpty docMoreLocs
                            then empty
                            else brackets docMoreLocs) <+>
                            (pprintExp e)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in pprintExp a1 <+> pprint pr <+> pprintExp a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprint pr

                  _ -> pprint pr <> parens (hsep $ map pprintExp es)

          LetE (v,ls,ty,e1) e2 -> text "let" <+>
                                  doc v <+> doublecolon <+>
                                  brackets (hcat (punctuate comma (map doc ls))) <+>
                                  pprint ty <+>
                                  equals <+>
                                  pprintExp e1 <+>
                                  text "in" $+$
                                  pprintExp e2
          IfE e1 e2 e3 -> text "if" <+>
                          pprintExp e1 $+$
                          text "then" <+>
                          pprintExp e2 $+$
                          text "else" <+>
                          pprintExp e3
          MkProdE es -> lparen <> hcat (punctuate (text ", ") (map pprintExp es)) <> rparen
          ProjE i e -> text "#" <> int i <+> pprintExp e
          CaseE e bnds -> text "case" <+> pprintExp e <+> text "of" $+$
                          nest 4 (vcat $ map dobinds bnds)
          DataConE l dc es -> text dc <+>
                              (if isEmpty (pprint l)
                               then empty
                               else doc l) <+>
                              lparen <> hcat (punctuate (text ",") (map pprintExp es)) <> rparen
          TimeIt e _ty _b -> text "timeit" <+> parens (pprintExp e)
          ParE a b -> pprintExp a <+> text "||" <+> pprintExp b
          Ext ext -> pprint ext
          MapE{} -> error $ "Unexpected form in program: MapE"
          FoldE{} -> error $ "Unexpected form in program: FoldE"
        where
          dobinds (dc,vls,e) = text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,l) -> if isEmpty (pprint l)
                                                                           then doc v
                                                                           else doc v <> doublecolon <> doc l)
                                                            vls))
                               <+> text "->" $+$ nest 4 (pprintExp e)


instance Pretty L0.Ty0 where
  pprint ty =
      case ty of
        L0.IntTy   -> text "Int"
        L0.BoolTy  -> text "Bool"
        L0.TyVar v -> text (fromVar v)
        L0.ProdTy tys -> parens $ hcat $ punctuate "," $ map pprint tys
        L0.SymDictTy ty -> text "Dict" <+> pprint ty
        L0.ArrowTy a b  -> pprint a <+> text "->" <+> pprint b
        L0.PackedTy tc l -> text "Packed" <+> text tc <+> brackets (hcat (map pprint l))
        L0.ListTy ty -> brackets (pprint ty)

instance Pretty L0.TyScheme where
  pprint (L0.ForAll tvs ty) = text "forall" <+> hsep (map (text . fromVar) tvs) <+> text "." <+> pprint ty

-- Oh no, all other generic PreExp things are defined over (PreExp e l (UrTy l)).
instance Pretty (PreExp L0.E0Ext () L0.Ty0) where
  pprint ex0 = pprintExp (l$ ex0)

instance Pretty (L0.E0Ext () L0.Ty0) where
  pprint ex0 =
    case ex0 of
      L0.LambdaE (v,ty) bod -> parens (text "\\" <+> doc v <+> doublecolon <+> pprint ty <+> text " -> "
                                         $$ nest 4 (pprint bod))
      L0.PolyAppE{} -> doc ex0

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
