{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Gibbon.Pretty
  ( Pretty(..), PPStyle(..), render, pprintHsWithEnv ) where

import           Prelude hiding ((<>))
import           Data.Loc
import           Text.PrettyPrint
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M

import qualified Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax as L1
import           Gibbon.L2.Syntax as L2
import           Gibbon.L3.Syntax as L3
import           Gibbon.Common
import           Gibbon.HaskellFrontend ( primMap )
import qualified Gibbon.L4.Syntax as L4

--------------------------------------------------------------------------------

-- | Rendering style.
data PPStyle
    = PPHaskell  -- ^ Prefer compatibility with GHC over anything else.
    | PPInternal -- ^ Noisiest, useful for Gibbon developers.
    deriving (Ord, Eq, Show, Read)


class Pretty e where
    pprintWithStyle :: PPStyle -> e -> Doc

    pprint :: e -> Doc
    pprint = pprintWithStyle PPInternal

    {-# MINIMAL pprintWithStyle  #-}


doublecolon :: Doc
doublecolon = colon <> colon

indentLevel :: Int
indentLevel = 4

--------------------------------------------------------------------------------

-- A convenience wrapper over some of the constraints.
type HasPretty ex = (Pretty ex, Pretty (TyOf ex), Pretty (ArrowTy (TyOf ex)))

-- Program:
instance HasPretty ex => Pretty (Prog ex) where
    pprintWithStyle sty (Prog ddefs funs me) =
        let meDoc = case me of
                      Nothing -> empty
                      -- Uh, we need versions of hasBenchE for L0, L2 and L3 too :
                      -- Assume False for now.
                      Just (e,ty) -> renderMain False (pprintWithStyle sty e) (pprintWithStyle sty ty)
            ddefsDoc = vcat $ map (pprintWithStyle sty) $ M.elems ddefs
            funsDoc = vcat $ map (pprintWithStyle sty) $ M.elems funs
        in case sty of
             PPInternal -> ddefsDoc $+$ funsDoc $+$ meDoc
             PPHaskell  -> ghc_compat_prefix False $+$ ddefsDoc $+$ funsDoc $+$ meDoc $+$ ghc_compat_suffix False

renderMain :: Bool -> Doc -> Doc -> Doc
renderMain has_bench m ty =
  if has_bench
  then (text "gibbon_main" <+> doublecolon <+> "IO ()" $+$
        text "gibbon_main" <+> equals <+> text "do" $$ nest indentLevel m)
  else (text "gibbon_main" <+> doublecolon <+> ty $+$
        text "gibbon_main" <+> equals <+> nest indentLevel m)


-- Things we need to make this a valid compilation unit for GHC:
ghc_compat_prefix, ghc_compat_suffix :: Bool -> Doc
ghc_compat_prefix has_bench =
  text "{-# LANGUAGE ScopedTypeVariables #-}" $+$
  text "{-# LANGUAGE DeriveGeneric       #-}" $+$
  text "{-# LANGUAGE DeriveAnyClass      #-}" $+$
  text "{-# LANGUAGE DerivingStrategies  #-}" $+$
  text "" $+$
  text "module Main where" $+$
  text "" $+$
  text "-- Gibbon Prelude --" $+$
  text "" $+$
  text "import Prelude as P ( (==), id, print, lookup, ($)" $+$
  text "                    , Int, (+), (-), (*), quot, (<), (>), (<=), (>=), (^), mod" $+$
  text "                    , Bool(..), (||), (&&)" $+$
  text "                    , String, (++)" $+$
  text "                    , Show, Eq, IO)" $+$
  text "" $+$
  text "import Data.Maybe (fromJust, isJust)" $+$
  text "" $+$
  text "" $+$
  (if has_bench
   then (text "import Criterion (nf, benchmark, bench)" $+$
         text "import Control.DeepSeq (force, NFData)" $+$
         text "import GHC.Generics" $+$
         text "import System.Mem (performMajorGC)" $+$
         text "import Data.Time.Clock (getCurrentTime, diffUTCTime)" $+$
         text "import Prelude as P ( (.), return )" $+$
         text "" $+$
         text "gibbon_bench :: (NFData a, NFData b) => String -> (a -> b) -> a -> IO ()" $+$
         text "gibbon_bench str fn arg = benchmark (nf fn (force arg))" $+$
         text "" $+$
         text "")
   else (text "gibbon_bench :: String -> (a -> b) -> a -> b" $+$
         text "gibbon_bench _str fn arg = fn arg" $+$
         text "" $+$ empty)) $+$
  text "type Sym = String" $+$
  text "" $+$
  text "type Dict a = [(Sym,a)]" $+$
  text "" $+$
  text "timeit :: a -> a" $+$
  text "timeit = id" $+$
  text "" $+$
  text "rand :: Int" $+$
  text "rand = 10" $+$
  text "" $+$
  text "(/) :: Int -> Int -> Int" $+$
  text "(/) = quot" $+$
  text "" $+$
  text "eqsym :: Sym -> Sym -> Bool" $+$
  text "eqsym = (==)" $+$
  text "" $+$
  text "mod :: Int -> Int -> Int" $+$
  text "mod = P.mod" $+$
  text "" $+$
  text "symAppend :: Sym -> Sym -> Sym" $+$
  text "symAppend = (++)" $+$
  text "" $+$
  text "sizeParam :: Int" $+$
  text "sizeParam = 4" $+$
  text "" $+$
  text "dictEmpty _a = []" $+$
  text "" $+$
  text "dictInsert _a d x v = (x,v):d" $+$
  text "" $+$
  text "dictLookup d k = fromJust $ lookup k d" $+$
  text "" $+$
  text "dictHaskey d k = isJust $ lookup k d" $+$
  text "" $+$
  text "-- Gibbon Prelude ends --" $+$
  text ""

    -- text "{-# LANGUAGE ScopedTypeVariables #-}\n" $+$
    --                 text "module Main where\n" $+$
    --                 text "timeit = id\n" $+$
    --                 text "sizeParam = 4"

ghc_compat_suffix has_bench =
  if has_bench
  then "\nmain = gibbon_main"
  else text "\nmain = print gibbon_main"

-- Functions:
instance HasPretty ex => Pretty (FunDef ex) where
    pprintWithStyle sty FunDef{funName,funArgs,funTy,funBody} =
        text (fromVar funName) <+> doublecolon <+> pprintWithStyle sty funTy
          $$ renderBod <> text "\n"
      where
        renderBod :: Doc
        renderBod = text (fromVar funName) <+> (pprintWithStyle sty funArgs) <+> equals
                      $$ nest indentLevel (pprintWithStyle sty funBody)

-- Datatypes
instance Pretty ex => Pretty (DDef ex) where
    pprintWithStyle sty DDef{tyName,tyArgs,dataCons} =
        text "data" <+> pprintWithStyle sty tyName <+> hsep (map (pprintWithStyle sty) tyArgs)
          <+> equals <+> vcat (punctuate " | " $
                                 map (\(d,args) ->
                                        text d <+> hsep (map (\(_,b) -> pprintWithStyle sty b) args))
                                   dataCons)
          <+> (if sty == PPHaskell
               then text "\n  deriving Show"
               else empty)


-- Primitives
instance (Show d, Pretty d, Ord d) => Pretty (Prim d) where
    pprintWithStyle sty pr =
        let renderPrim = M.fromList (map (\(a,b) -> (b,a)) (M.toList primMap))
        in case M.lookup pr renderPrim of
              Nothing  ->
                  let wty ty = text "<" <> pprintWithStyle sty ty <> text ">"
                  in
                    case sty of
                      PPInternal -> case pr of
                                      DictEmptyP ty  -> text "DictEmpty"  <> wty ty
                                      DictHasKeyP ty -> text "DictHasKey" <> wty ty
                                      DictInsertP ty -> text "DictInsert" <> wty ty
                                      DictLookupP ty -> text "DictLookup" <> wty ty
                                      RequestEndOf   -> text "RequestEndOf"
                                      ErrorP str ty  -> text "ErrorP" <> wty ty <+> doubleQuotes (text str) <> space
                                      ReadPackedFile mb_fp tycon _ _ ->
                                        text "readFile " <+> text (pretty mb_fp) <+> doublecolon <+> text tycon
                                      _ -> error $ "pprint: Unknown primitive: " ++ show pr
                      PPHaskell  -> case pr of
                                      DictEmptyP _ty  -> text "dictEmpty"
                                      DictHasKeyP _ty -> text "dictHasKey"
                                      DictInsertP _ty -> text "dictInsert"
                                      DictLookupP _ty -> text "dictLookup"
                                      RequestEndOf   -> text "RequestEndOf"
                                      ErrorP str _ty -> text "error" <> doubleQuotes (text str)
                                      ReadPackedFile mb_fp tycon _ _ ->
                                        text "readFile " <+> text (pretty mb_fp) <+> doublecolon <+> text tycon
                                      _ -> error $ "pprint: Unknown primitive: " ++ show pr
              Just str -> text str


-- Types:
instance Pretty () where
    pprintWithStyle _ _ = empty

instance Pretty Var where
    pprintWithStyle _ v = text (fromVar v)

instance Pretty [Var] where
    pprintWithStyle _ ls = hsep $ map (text . fromVar) ls

instance Pretty TyVar where
    pprintWithStyle sty tyvar =
      case sty of
        PPHaskell -> case tyvar of
                       BoundTv v  -> text $ fromVar v
                       SkolemTv{} -> doc tyvar
                       UserTv v   -> text $ fromVar v
        PPInternal -> doc tyvar

instance (Pretty l) => Pretty (UrTy l) where
    pprintWithStyle sty ty =
        case ty of
          IntTy  -> text "Int"
          SymTy  -> text "Sym"
          BoolTy -> text "Bool"
          ProdTy tys    -> parens $ hcat $ punctuate "," $ map (pprintWithStyle sty) tys
          SymDictTy (Just var) ty1 -> case sty of
                                        PPHaskell  -> text "Dict" <+> pprintWithStyle sty ty1
                                        PPInternal -> text "Dict" <+> pprintWithStyle sty var <+> pprintWithStyle sty ty1
          SymDictTy Nothing ty1 -> case sty of
                                     PPHaskell  ->text "Dict" <+> pprintWithStyle sty ty1
                                     PPInternal -> text "Dict" <+> text "_" <+> pprintWithStyle sty ty1
          PackedTy tc loc ->
              case sty of
                PPHaskell  -> text tc
                PPInternal -> parens $ text "Packed" <+> text tc <+> pprintWithStyle sty loc
          ListTy ty1 -> brackets $ pprintWithStyle sty ty1
          PtrTy     -> text "Ptr"
          CursorTy  -> text "Cursor"
          ArenaTy   -> case sty of
                         PPHaskell  -> text "()"
                         PPInternal -> text "Arena"

-- Function type for L1 and L3
instance Pretty ([UrTy ()], UrTy ()) where
    pprintWithStyle sty (as,b) = hsep $ punctuate " ->" $ map (pprintWithStyle sty) (as ++ [b])

instance Pretty ArrowTy2 where
    -- TODO: start metadata at column 0 instead of aligning it with the type
    pprintWithStyle sty fnty =
        case sty of
          PPHaskell ->
            (hsep $ punctuate " ->" $ map (pprintWithStyle sty) (arrIns fnty)) <+> text "->" <+> pprintWithStyle sty (arrOut fnty)
          PPInternal ->
            pprintWithStyle PPHaskell fnty $$
              braces (text "locvars" <+> doc (locVars fnty) <> comma $$
                      text "effs: " <+> doc (arrEffs fnty) <> comma $$
                      text "locrets: " <+> doc (locRets fnty))


-- Expressions

-- CSK: Needs a better name.
type HasPrettyToo e l d = (Show d, Ord d, Eq d, Pretty d, Pretty l, Pretty (e l d), TyOf (e l (UrTy l)) ~ TyOf (PreExp e l (UrTy l)))

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprintWithStyle sty (L _ e) = pprintWithStyle sty e

instance Pretty (PreExp e l d) => Pretty [(PreExp e l d)] where
    pprintWithStyle sty ls = hsep $ map (pprintWithStyle sty) ls

instance Pretty (L (PreExp e l d)) => Pretty [(L (PreExp e l d))] where
    pprintWithStyle sty ls = hsep $ map (pprintWithStyle sty) ls

instance HasPrettyToo e l d => Pretty (PreExp e l d) where
    pprintWithStyle sty ex0 =
        case ex0 of
          VarE v -> pprintWithStyle sty v
          LitE i -> int i
          LitSymE v -> text "\"" <> pprintWithStyle sty v <> text "\""
          AppE v locs ls -> parens $
                             pprintWithStyle sty v <+>
                             (brackets $ hcat (punctuate "," (map pprint locs))) <+>
                             (pprintWithStyle sty ls)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in pprintWithStyle sty a1 <+> pprintWithStyle sty pr <+> pprintWithStyle sty a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprintWithStyle sty pr

                  _ -> case sty of
                         PPHaskell  -> pprintWithStyle sty pr <+> hsep (punctuate " " $ map (pprintWithStyle sty) es)
                         PPInternal -> pprintWithStyle sty pr <> parens (hsep $ punctuate "," $ map (pprintWithStyle sty) es)

          LetE (v,ls,ty,e1) e2 -> (text "let") <+>
                                  pprintWithStyle sty v <+> doublecolon <+>
                                  (if null ls
                                   then empty
                                   else brackets (hcat (punctuate comma (map (pprintWithStyle sty) ls)))) <+>
                                  pprintWithStyle sty ty <+>
                                  equals <+>
                                  pprintWithStyle sty e1 <+>
                                  text "in" $+$
                                  pprintWithStyle sty e2
          IfE e1 e2 e3 -> text "if" <+>
                          pprintWithStyle sty e1 $+$
                          text "then" <+>
                          pprintWithStyle sty e2 $+$
                          text "else" <+>
                          pprintWithStyle sty e3
          MkProdE es -> lparen <> hcat (punctuate (text ", ") (map (pprintWithStyle sty) es)) <> rparen
          ProjE i e ->
              let edoc = pprintWithStyle sty e
              in case sty of
                PPInternal -> parens $ text "#" <> int i <+> edoc
                PPHaskell  ->
                    case i of
                      0 -> text "fst" <+> edoc
                      1 -> text "snd" <+> edoc
                      _ -> error (render $ pprintWithStyle PPInternal ex0) -- text "#" <> int i <+> edoc
          CaseE e bnds -> text "case" <+> pprintWithStyle sty e <+> text "of" $+$
                          nest indentLevel (vcat $ map dobinds bnds)
          DataConE loc dc es -> parens $ text dc <+>
                                (if isEmpty (pprintWithStyle sty loc)
                                 then empty
                                 else pprintWithStyle sty loc) <+>
                                hsep (map (pprintWithStyle sty) es)
                              -- lparen <> hcat (punctuate (text ",") (map (pprintWithStyle sty) es)) <> rparen
          TimeIt e _ty _b -> text "timeit" <+> parens (pprintWithStyle sty e)
          SpawnE w v locs ls -> text "spawn" <+> pprintWithStyle sty w <+>
                                  parens (pprintWithStyle sty v <+>
                                           (brackets $ hcat (punctuate "," (map pprint locs))) <+>
                                           (pprintWithStyle sty ls))
          SyncE -> text "sync"
          WithArenaE v e -> case sty of
                              PPHaskell  -> (text "let") <+>
                                            pprintWithStyle sty v <+>
                                            equals <+>
                                            text "()" <+>
                                            text "in" $+$
                                            pprintWithStyle sty e
                              PPInternal -> text "letarena" <+> pprint v <+> text "in" $+$ pprint e
          Ext ext -> pprintWithStyle sty ext
          MapE{} -> error $ "Unexpected form in program: MapE"
          FoldE{} -> error $ "Unexpected form in program: FoldE"
        where
          dobinds (dc,vls,e) = text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,loc) -> if isEmpty (pprintWithStyle sty loc)
                                                                             then pprintWithStyle sty v
                                                                             else pprintWithStyle sty v <> doublecolon <> pprintWithStyle sty loc)
                                                            vls))
                               <+> text "->" $+$ nest indentLevel (pprintWithStyle sty e)
-- L1
instance (Pretty l, Pretty d, Ord d, Show d) => Pretty (E1Ext l d) where
    pprintWithStyle sty ext =
      case ext of
        BenchE fn tyapps args b -> text "gibbon_bench" <+> (doubleQuotes $ text "") <+> text (fromVar fn) <+>
                                   (brackets $ hcat (punctuate "," (map pprint tyapps))) <+>
                                   (pprintWithStyle sty args) <+> text (if b then "true" else "false")

-- L2
instance Pretty l => Pretty (L2.PreLocExp l) where
    pprintWithStyle _ le =
        case le of
          StartOfLE r -> lparen <> text "startof" <+> text (sdoc r) <> rparen
          AfterConstantLE i loc -> lparen <> pprint loc <+> text "+" <+> int i <> rparen
          AfterVariableLE v loc -> lparen <> pprint loc <+> text "+" <+> doc v <> rparen
          InRegionLE r  -> lparen <> text "inregion" <+> text (sdoc r) <> rparen
          FromEndLE loc -> lparen <> text "fromend" <+> pprint loc <> rparen
          FreeLE -> lparen <> text "free" <> rparen

instance HasPrettyToo E2Ext l (UrTy l) => Pretty (L2.E2Ext l (UrTy l)) where
    pprintWithStyle _ ex0 =
        case ex0 of
          LetRegionE r e -> text "letregion" <+>
                               doc r <+> text "in" $+$ pprint e
          LetLocE loc le e -> text "letloc" <+>
                                pprint loc <+> equals <+> pprint le <+> text "in" $+$ pprint e
          RetE ls v -> text "return" <+>
                          lbrack <> hcat (punctuate (text ",") (map pprint ls)) <> rbrack <+>
                          doc v
          FromEndE loc -> text "fromend" <+> pprint loc
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
  pprintWithStyle sty ty =
      case ty of
        L0.IntTy      -> text "Int"
        L0.SymTy0     -> text "Sym"
        L0.BoolTy     -> text "Bool"
        L0.TyVar v    -> doc v
        L0.MetaTv v   -> doc v
        L0.ProdTy tys -> parens $ hcat $ punctuate "," $ map (pprintWithStyle sty) tys
        L0.SymDictTy (Just v) ty1 -> text "Dict" <+> pprint v <+> pprint ty1
        L0.SymDictTy Nothing  ty1 -> text "Dict" <+> pprint ty1
        L0.ArrowTy as b  -> parens $ (hsep $ map (<+> "->") $ map (pprintWithStyle sty) as) <+> pprint b
        L0.PackedTy tc loc -> text "Packed" <+> text tc <+> brackets (hcat (map (pprintWithStyle sty) loc))
        L0.ListTy ty1 -> brackets (pprintWithStyle sty ty1)
        L0.ArenaTy    -> text "Arena"


instance Pretty L0.TyScheme where
  pprintWithStyle _ (L0.ForAll tvs ty) = text "forall" <+> hsep (map doc tvs) <> text "." <+> pprint ty

instance (Out a, Pretty a) => Pretty (L0.E0Ext a L0.Ty0) where
  pprintWithStyle sty ex0 =
    case ex0 of
      L0.LambdaE args bod -> parens (text "\\" <> parens (hsep (punctuate comma (map (\(v,ty) -> doc v <+> doublecolon <+> pprint ty) args))) <+> text "->"
                                         $$ nest indentLevel (pprint bod))
      L0.FunRefE tyapps f -> parens $ text "fn:" <> pprintWithStyle sty f <+> (brackets $ hcat (punctuate "," (map pprint tyapps)))
      L0.PolyAppE{} -> doc ex0
      L0.BenchE fn tyapps args b -> text "bench" <+> text (fromVar fn) <+>
                                    (brackets $ hcat (punctuate "," (map pprint tyapps))) <+>
                                    (pprintWithStyle sty args) <+> text (if b then "true" else "false")
      L0.ParE0 ls -> text "par" <+> lparen <> hcat (punctuate (text ", ") (map (pprintWithStyle sty) ls)) <> rparen


--------------------------------------------------------------------------------

{-

'pprintWithStyle' does not have enough information to translate 'ProjE' to
valid Haskell. In Gibbon, 'ProjE' can project a value out of an *arbitrary*
tuple. It works like the Haskell list index op (!!), rather than tuples. In
Haskell, we must pattern match on a tuple to extract elements out of it. And
we need to know the size of the tuple in order to generate a proper pattern.
'pprintHsWithEnv' carries a type environemt around for this purpose.

Another way to solve this would be to update Gibbon's AST to store this info:

    ... | ProjE (Int, Int) EXP | ...

But that would be  a big refactor.

-}

pprintHsWithEnv :: Prog1 -> Doc
pprintHsWithEnv p@Prog{ddefs,fundefs,mainExp} =
  let env2 = progToEnv p
      (meDoc,sfx, main_has_bench) =
        case mainExp of
          Nothing     -> (empty, empty, False)
          Just (e,ty) -> let main_has_bench1 = hasBenchE e in
                         (renderMain main_has_bench1 (ppExp main_has_bench1 env2 e) (pprintWithStyle sty ty)
                         , ghc_compat_suffix main_has_bench1
                         , main_has_bench1)
      mb_derive_more d = if main_has_bench
                         then d $$ (text "  deriving (Generic, NFData)" $$ text "")
                         else d
      ddefsDoc = vcat $ map (mb_derive_more . pprintWithStyle sty) $ M.elems ddefs
      funsDoc  = vcat $ map (ppFun env2) $ M.elems fundefs
  in (ghc_compat_prefix main_has_bench) $+$ ddefsDoc $+$ funsDoc $+$ meDoc $+$ sfx
  where
    -- | Verify some assumptions about BenchE.
    hasBenchE :: L Exp1 -> Bool
    hasBenchE (L _ ex) =
      case ex of
        Ext (BenchE{}) -> True
        -- Straightforward recursion ...
        VarE{}     -> False
        LitE{}     -> False
        LitSymE{}  -> False
        AppE{}     -> False
        PrimAppE{} -> False
        DataConE{} -> False
        ProjE _ _  -> False
        IfE _ b c  -> (go b) || (go c)
        MkProdE _  -> False
        LetE _ bod -> go bod
        CaseE _ mp -> any (== True) $ map (\(_,_,c) -> go c) mp
        TimeIt{}   -> False
        WithArenaE _ e -> (go e)
        SpawnE{}-> False
        SyncE   -> False
        MapE{}  -> error $ "hasBenchE: TODO MapE"
        FoldE{} -> error $ "hasBenchE: TODO FoldE"
      where go = hasBenchE

    sty = PPHaskell

    ppFun :: Env2 Ty1 -> FunDef1 -> Doc
    ppFun env2 FunDef{funName, funArgs, funTy, funBody} =
      text (fromVar funName) <+> doublecolon <+> pprintWithStyle sty funTy
             $$ renderBod <> text "\n"
      where
        env2' = extendsVEnv (M.fromList $ zip funArgs (inTys funTy)) env2
        renderBod :: Doc
        renderBod = text (fromVar funName) <+> (hsep $ map (text . fromVar) funArgs) <+> equals
                      $$ nest indentLevel (ppExp False env2' funBody)

    ppExp :: Bool -> Env2 Ty1 -> L Exp1 -> Doc
    ppExp monadic env2 (L _ ex0) =
      case ex0 of
          VarE v -> pprintWithStyle sty v
          LitE i -> int i
          LitSymE v -> text "\"" <> pprintWithStyle sty v <> text "\""
          AppE v _locs ls -> pprintWithStyle sty v <+>
                            (hsep $ map (ppExp monadic env2) ls)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in ppExp monadic env2 a1 <+> pprintWithStyle sty pr <+> ppExp monadic env2 a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprintWithStyle sty pr

                  _ -> pprintWithStyle sty pr <+> hsep (map (ppExp monadic env2) es)

          -- See #111.
          LetE (v,_, ty@(ProdTy tys),e1) e2 ->
            let -- Still avoiding 'PassM'.
                indexed_vars = map (\i -> (i, varAppend v (toVar $ "_proj_" ++ show i))) [0..(length tys - 1)]
                -- Substitute projections with variables bound by the pattern match.
                e2' = foldr (\(i,w) acc -> substE (l$ ProjE i (l$ VarE v)) (l$ VarE w) acc) e2 indexed_vars

                bind_rhs :: Doc -> Doc -> Doc
                bind_rhs d rhs = d <+> doublecolon <+> pprintWithStyle sty ty <+> equals <+> rhs

                env2' = foldr (\((_,w),t) acc -> extendVEnv w t acc) env2 (zip indexed_vars tys)

            in (text "let") <+>
               vcat [bind_rhs (pprintWithStyle sty v) (ppExp monadic env2 e1),
                     bind_rhs (parens $ hcat $ punctuate (text ",") (map (pprintWithStyle sty . snd) indexed_vars)) (ppExp monadic env2 (l$ VarE v))] <+>
               (if monadic
                then empty
                else text "in") $+$
               ppExp monadic (extendVEnv v ty env2') e2'

          LetE (v,_,ty,e1) e2  -> (text "let") <+>
                                  pprintWithStyle sty v <+> doublecolon <+>
                                  empty <+>
                                  pprintWithStyle sty ty <+>
                                  equals <+>
                                  ppExp monadic env2 e1 <+>
                                  (if monadic
                                   then empty
                                   else text "in") $+$
                                  ppExp monadic (extendVEnv v ty env2) e2
          IfE e1 e2 e3 -> text "if" <+>
                          ppExp monadic env2 e1 $+$
                          text "then" <+>
                          ppExp monadic env2 e2 $+$
                          text "else" <+>
                          ppExp monadic env2 e3
          MkProdE es -> lparen <> hcat (punctuate (text ", ") (map (ppExp monadic env2) es)) <> rparen
          ProjE i e ->
              case gRecoverType ddefs env2 e of
                ProdTy tys -> let edoc = ppExp monadic env2 e
                                  n    = length tys
                                  -- Gosh, do we also need a gensym here...
                                  v    = ("tup_proj_" ++ show i)
                                  pat  = parens $ hcat $
                                           punctuate (text ",") ([if i == j then text v else text "_" | j <- [0..n-1]])
                              in parens $ text "let " <+> pat <+> text "=" <+> edoc <+> text "in" <+> text v
                ty -> error $ "pprintHsWithEnv: " ++ sdoc ty ++ "is not a product. In " ++ sdoc ex0
          CaseE e bnds -> text "case" <+> ppExp monadic env2 e <+> text "of" $+$
                          nest indentLevel (vcat $ map (dobinds env2) bnds)
          DataConE _loc dc es ->
                              parens $ text dc <+>
                              hsep (map (ppExp monadic env2) es)
          TimeIt e _ty _b -> text "timeit" <+> parens (ppExp monadic env2 e)
          WithArenaE v e -> (text "let") <+>
                            pprintWithStyle sty v <+>
                            equals <+>
                            text "()" <+>
                            text "in" $+$
                            ppExp monadic env2 e
          -- text "letarena" <+> pprint v <+> text "in" $+$ ppExp env2 e
          Ext (BenchE fn _locs args _b) ->
             --  -- Criterion
             -- let args_doc = hsep $ map (ppExp env2) args
             -- in text "gibbon_bench" <+> (doubleQuotes (text (fromVar fn) <+> args_doc)) <+> text (fromVar fn) <+> args_doc
            let args_doc = hsep $ map ((\x -> parens $ text "force" <+> x) . ppExp monadic env2) args
            in text "performMajorGC" $+$
               text "t1 <- getCurrentTime" $+$
               text "let x" <+> equals <+> text (fromVar fn) <+> args_doc $+$
               text "t2 <- getCurrentTime" $+$
               text "print (diffUTCTime t2 t1)" $+$
               text "print x"
          MapE{} -> error $ "Unexpected form in program: MapE"
          FoldE{}-> error $ "Unexpected form in program: FoldE"
        where
          dobinds env21 (dc,vls,e) =
                           let tys    = lookupDataCon ddefs dc
                               vars   = map fst vls
                               env21' = extendsVEnv (M.fromList $ zip vars tys) env21
                           in  text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,loc) -> if isEmpty (pprintWithStyle sty loc)
                                                                             then pprintWithStyle sty v
                                                                             else pprintWithStyle sty v <> doublecolon <> pprintWithStyle sty loc)
                                                            vls))
                               <+> text "->" $+$ nest indentLevel (ppExp monadic env21' e)
