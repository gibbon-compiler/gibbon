{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Gibbon.Pretty ( Pretty(..) ) where

import           Prelude hiding ((<>))
import           Data.Loc
import           Data.Text (unpack)
import           Text.PrettyPrint
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M

import qualified Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax
import           Gibbon.L2.Syntax as L2
import           Gibbon.L3.Syntax as L3
import           Gibbon.Common
import           Gibbon.SExpFrontend (primMap)
import qualified Gibbon.L4.Syntax as L4

--------------------------------------------------------------------------------

-- | Rendering style.
data PPStyle
    = Haskell  -- ^ Prefer compatibility with GHC over anything else.
    | Internal -- ^ Noisiest, useful for Gibbon developers.
    deriving (Ord, Eq, Show, Read)


class Pretty e where
    pprintWithStyle :: PPStyle -> e -> Doc

    pprint :: e -> Doc
    pprint = pprintWithStyle Internal

    pprender :: e -> String
    pprender = render . pprint

    {-# MINIMAL pprintWithStyle  #-}


doublecolon :: Doc
doublecolon = colon <> colon

--------------------------------------------------------------------------------

-- A convenience wrapper over some of the constraints.
type HasPretty ex = (Pretty ex, Pretty (TyOf ex), Pretty (ArrowTy (TyOf ex)))

-- Program:
instance HasPretty ex => Pretty (Prog ex) where
    pprintWithStyle _ (Prog _ funs me) =
        let meDoc = case me of
                      Nothing -> empty
                      Just (e,ty) -> renderMain (pprint e) (pprint ty)
            funsDoc = vcat $ map pprint $ M.elems funs
        in funsDoc $+$ meDoc

renderMain :: Doc -> Doc -> Doc
renderMain m ty = text "main" <+> doublecolon <+> ty
                    $$ text "main" <+> equals $$ nest 4 m

-- Functions:
instance HasPretty ex => Pretty (FunDef ex) where
    pprintWithStyle _ FunDef{funName,funArg,funTy,funBody} =
        text (fromVar funName) <+> doublecolon <+> pprint funTy
          $$ renderBod <> text "\n"
      where
        renderBod :: Doc
        renderBod = text (fromVar funName) <+> text (fromVar funArg) <+> equals $$ nest 4 (pprint funBody)

-- TODO: datatypes

--------------------------------------------------------------------------------

-- Primitives
instance Ord d => Pretty (Prim d) where
    pprintWithStyle _ pr =
        -- We add PEndOf here because it's not exposed to the users, and as a result,
        -- is not defined as a primop in the parser primMap.
        -- TODO: Dictionaries!!!
        let renderPrim = M.union (M.singleton PEndOf "pendof") $
                         M.fromList (map (\(a,b) -> (b,a)) (M.toList primMap))
        in case M.lookup pr renderPrim of
              Nothing  -> error $ "pprint: Unknown primitive: " ++ render (pprint pr)
              Just txt -> text (unpack txt)


--------------------------------------------------------------------------------

-- Types:
instance Pretty () where
    pprintWithStyle _ _ = empty

instance Pretty Var where
    pprintWithStyle _ v = text (fromVar v)

instance (Pretty l) => Pretty (UrTy l) where
    pprintWithStyle _ ty =
        case ty of
          IntTy  -> text "Int"
          BoolTy -> text "Bool"
          ProdTy tys    -> parens $ hcat $ punctuate "," $ map pprint tys
          SymDictTy ty  -> text "Dict" <+> pprint ty
          PackedTy tc l -> text "Packed" <+> text tc <+> pprint l
          ListTy ty -> text "List" <+> pprint ty
          PtrTy     -> text "Ptr"
          CursorTy  -> text "Cursor"

-- Function type for L1 and L3
instance Pretty (UrTy (), UrTy ()) where
    pprintWithStyle _ (a,b) = pprint a <+> text "->" <+> pprint b

instance Pretty ArrowTy2 where
    -- TODO: start metadata at column 0 instead of aligning it with the type
    pprintWithStyle _ fnty =
                  pprint (arrIn fnty) <+> text "->" <+> pprint (arrOut fnty) $$
                  braces (text "locvars" <+> doc (locVars fnty) <> comma $$
                          text "effs: " <+> doc (arrEffs fnty) <> comma $$
                          text "locrets: " <+> doc (locRets fnty))

--------------------------------------------------------------------------------

-- Expressions

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprintWithStyle _ (L _ e) = pprint e

-- CSK: Needs a better name.
type HasPrettyToo e l d = (Ord d, Eq d, Pretty d, Pretty l, Pretty (e l d))

instance HasPrettyToo e l d => Pretty (PreExp e l d) where
    pprintWithStyle _ ex0 =
        case ex0 of
          VarE v -> pprint v
          LitE i -> int i
          LitSymE v -> pprint v
          AppE v ls e -> pprint v <+>
                         (if null ls
                          then empty
                          else brackets $ hcat (punctuate "," (map pprint ls))) <+>
                         (pprint e)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in pprint a1 <+> pprint pr <+> pprint a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprint pr

                  _ -> pprint pr <> parens (hsep $ map pprint es)

          LetE (v,ls,ty,e1) e2 -> text "let" <+>
                                  pprint v <+> doublecolon <+>
                                  (if null ls
                                   then empty
                                   else brackets (hcat (punctuate comma (map pprint ls)))) <+>
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
          MkProdE es -> lparen <> hcat (punctuate (text ", ") (map pprint es)) <> rparen
          ProjE i e -> text "#" <> int i <+> pprint e
          CaseE e bnds -> text "case" <+> pprint e <+> text "of" $+$
                          nest 4 (vcat $ map dobinds bnds)
          DataConE l dc es -> text dc <+>
                              (if isEmpty (pprint l)
                               then empty
                               else pprint l) <+>
                              lparen <> hcat (punctuate (text ",") (map pprint es)) <> rparen
          TimeIt e _ty _b -> text "timeit" <+> parens (pprint e)
          ParE a b -> pprint a <+> text "||" <+> pprint b
          Ext ext -> pprint ext
          MapE{} -> error $ "Unexpected form in program: MapE"
          FoldE{} -> error $ "Unexpected form in program: FoldE"
        where
          dobinds (dc,vls,e) = text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,l) -> if isEmpty (pprint l)
                                                                           then pprint v
                                                                           else pprint v <> doublecolon <> pprint l)
                                                            vls))
                               <+> text "->" $+$ nest 4 (pprint e)
-- L1
instance Pretty (NoExt l d) where
    pprintWithStyle _ _ = empty

-- L2
instance Pretty l => Pretty (L2.PreLocExp l) where
    pprintWithStyle _ le =
        case le of
          StartOfLE r -> lparen <> text "startof" <+> text (show r) <> rparen
          AfterConstantLE i l -> lparen <> pprint l <+> text "+" <+> int i <> rparen
          AfterVariableLE v l -> lparen <> pprint l <+> text "+" <+> doc v <> rparen
          InRegionLE r -> lparen <> text "inregion" <+> text (show r) <> rparen
          FromEndLE l -> lparen <> text "fromend" <+> pprint l <> rparen

instance HasPrettyToo E2Ext l (UrTy l) => Pretty (L2.E2Ext l (UrTy l)) where
    pprintWithStyle _ ex0 =
        case ex0 of
          LetRegionE r e -> text "letregion" <+>
                               doc r <+> text "in" $+$ pprint e
          LetLocE l le e -> text "letloc" <+>
                               pprint l <+> equals <+> pprint le <+> text "in" $+$ pprint e
          RetE ls v -> text "return" <+>
                          lbrack <> hcat (punctuate (text ",") (map pprint ls)) <> rbrack <+>
                          doc v
          FromEndE l -> text "fromend" <+> pprint l
          L2.BoundsCheck i l1 l2 -> text "boundscheck" <+> int i <+> pprint l1 <+> pprint l2
          IndirectionE tc dc (l1,v1) (l2,v2) e -> text "indirection" <+>
                                                     doc tc <+>
                                                     doc dc <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [pprint l1,text (fromVar v1)]) <>
                                                     rparen <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [pprint l2,text (fromVar v2)]) <>
                                                     rparen <+>
                                                     pprint e

-- L3
instance (Out l) => Pretty (L3.E3Ext l (UrTy l)) where
    pprintWithStyle _ = doc -- TODO: replace this with actual pretty printing for L3 forms

-- L4
instance Pretty L4.Prog where
   pprintWithStyle _ = doc -- TODO: replace this with actual pretty printing for L4 forms

--------------------------------------------------------------------------------

-- Oh no, all other generic PreExp things are defined over (PreExp e l (UrTy l)).
-- We have to redefine this for L0 (which doesn't use UrTy).

instance Pretty L0.Ty0 where
  pprintWithStyle _ ty =
      case ty of
        L0.IntTy   -> text "Int"
        L0.BoolTy  -> text "Bool"
        L0.TyVar v -> doc v
        L0.MetaTv v -> doc v
        L0.ProdTy tys -> parens $ hcat $ punctuate "," $ map pprint tys
        L0.SymDictTy ty -> text "Dict" <+> pprint ty
        L0.ArrowTy a b  -> pprint a <+> text "->" <+> pprint b
        L0.PackedTy tc l -> text "Packed" <+> text tc <+> brackets (hcat (map pprint l))
        L0.ListTy ty -> brackets (pprint ty)

instance Pretty L0.TyScheme where
  pprintWithStyle _ (L0.ForAll tvs ty) = text "forall" <+> hsep (map doc tvs) <+> text "." <+> pprint ty

instance Pretty (L0.E0Ext () L0.Ty0) where
  pprintWithStyle _ ex0 =
    case ex0 of
      L0.LambdaE (v,ty) bod -> parens (text "\\" <+> doc v <+> doublecolon <+> pprint ty <+> text " -> "
                                         $$ nest 4 (pprint bod))
      L0.PolyAppE{} -> doc ex0
