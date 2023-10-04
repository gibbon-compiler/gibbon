module Gibbon.L1.GenSML where

import Gibbon.L1.Syntax
import Gibbon.Common

import Text.PrettyPrint hiding ((<>))
import Data.Maybe
import Control.Monad
import Data.Map hiding (foldr, fold, null, empty)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Symbol

import Data.Foldable hiding ( toList )
import Data.Graph
import Data.Tree ( flatten )


ppExt :: E1Ext () Ty1 -> Doc
ppExt ext0 = case ext0 of
  BenchE _var _uts _pes _b -> error "BenchE"
  AddFixed _var _n -> error "AddFixed"
  StartOfPkdCursor _var -> error "StartOfPkdCursor"

ppE :: Exp1 -> Doc
ppE e0 = case e0 of
  VarE var -> ppVar var
  LitE n -> int n
  CharE c -> char c
  FloatE x -> double x
  LitSymE var -> doubleQuotes $ ppVar var
  AppE var _ pes -> ppAp (ppVar var) pes
  PrimAppE pr pes -> ppPrim pr pes
  LetE (v, _, _, e) pe' ->
    hsep
      [ "\n  let val", ppVar v, "="
      , ppE e, "in"
      , ppE pe', "end"
      ]
  IfE pe' pe2 pe3 ->
    ("\n  " <>) $ parens $ hsep
      [ "if", ppE pe'
      , "then", ppE pe2
      , "\n   else", ppE pe3
      ]
  MkProdE pes -> parens $ interleave comma $ ppE <$> pes
  ProjE 0 pe' -> parens $ hsep
    [ "case", ppE pe', "of"
    , "(t0, _) => t0"
    ]
  ProjE 1 pe' -> parens $ hsep
    [ "case", ppE pe', "of"
    , "(_, t1) => t1"
    ]
  ProjE n pe' -> parens $ hsep [hcat ["#", int $ succ n], ppE pe']
  CaseE pe' x0 ->
    parens $ hsep
      [ hsep ["case", ppE pe', "of"]
      , interleave "\n  |" ((\(dc, vs, e) -> hsep
        [ text dc
        , case vs of
          [] -> mempty
          _ -> parens $ interleave comma $ ppVar . fst <$> vs
        , "=>", ppE e
        ]) <$> x0)
      ]
  DataConE _ty0 s [] -> text s
  DataConE _ty0 s pes ->
    parens $ hsep
      [ text s
      , parens $ interleave comma $ ppE <$> pes
      ]

  TimeIt _pe' _ty0 _b -> _
  WithArenaE _var _pe' -> error "WithArenaE"
  SpawnE _var _ty0s _pes -> error "SpawnE"
  SyncE -> error "SyncE"
  MapE _x0 _pe' -> error "MapE"
  FoldE _x0 _x1 _pe' -> error "FoldE"

  Ext ee -> ppExt ee

ppCurried :: Doc -> [Exp1] -> Doc
ppCurried var pes = parens $ hsep $ var : (ppE <$> pes)

ppAp :: Doc -> [Exp1] -> Doc
ppAp var pes =
  parens $ var <> case pes of
    [] -> empty               -- don't confuse with application to unit (1 arg)
    [x] -> space <> ppE x
    _ -> parens $ interleave "," $ ppE <$> pes

ppVar :: Var -> Doc
ppVar = text . getVar

getVar :: Var -> String
getVar (Var s) = case unintern s of
  "val" -> "val_"
  "as" -> "as_"
  "open" -> "open_"
  "rec" -> "rec_"
  "fun" -> "fun_"
  "end" -> "end_"
  '_' : z -> "internal_" ++ z
  z -> z

interleave :: Doc -> [Doc] -> Doc
interleave sepr lst = case lst of
  [] -> mempty
  d : ds -> (d <+>) $ fold $ (sepr <+>) <$> ds

binary :: String -> [Exp1] -> Doc
binary opSym pes =
  parens $ hsep [l, text opSym, r]
  where
    (l, r) = extractBinary opSym pes

extractBinary :: String -> [Exp1] -> (Doc, Doc)
extractBinary opSym pes = case ppE <$> pes of
  [l, r] -> (l, r)
  es -> error $ fold
    [ "L0 error: (", opSym, ") is provided "
    , show $ length es, " arguments"
    ]

extractUnary :: String -> [Exp1] -> Doc
extractUnary opSym pes = case ppE <$> pes of
  [x] -> x
  es -> error $ fold
    [ "L0 error: (", opSym, ") is provided "
    , show $ length es, " arguments"
    ]

ppFail :: String -> Doc
ppFail s = hsep
  [ "raise"
  , parens $ hsep ["Fail", doubleQuotes $ text s]
  ]

ppPrim :: Prim Ty1 -> [Exp1] -> Doc
ppPrim pr pes = case pr of
  AddP -> binary "+" pes
  SubP -> binary "-" pes
  MulP -> binary "*" pes
  DivP -> binary "div" pes
  ModP -> binary "mod" pes
  ExpP -> binary "**" pes
  RandP -> ppCurried "MltonRandom.rand()" pes
  EqIntP -> binary "=" pes
  LtP -> binary "<" pes
  GtP -> binary ">" pes
  LtEqP -> binary "<=" pes
  GtEqP -> binary ">=" pes
  FAddP -> binary "+" pes
  FSubP -> binary "-" pes
  FMulP -> binary "*" pes
  FDivP -> binary "/" pes
  FExpP ->
    let
      (l, r) = extractBinary "pow" pes
    in
    parens $ hsep
      [ "Math.pow"
      , parens $ hcat [l, comma, r]
      ]
  FRandP -> ppCurried "Random.randFloat" pes
  EqFloatP -> binary "=" pes
  EqCharP -> binary "=" pes
  FLtP -> binary "<" pes
  FGtP -> binary ">" pes
  FLtEqP -> binary "<=" pes
  FGtEqP -> binary ">=" pes
  FSqrtP -> ppAp "Math.sqrt" pes
  IntToFloatP -> ppAp "Real.fromInt" pes
  FloatToIntP -> ppAp "Int.fromReal" pes
  FTanP -> ppAp "Math.tan" pes
  EqSymP -> binary "=" pes
  EqBenchProgP _ -> error "GenSML: EqBenchProgP"
  OrP -> binary "orelse" pes
  AndP -> binary "andalso" pes
  MkTrue -> "true"
  MkFalse -> "false"
  ErrorP s _ -> ppFail s
  SizeParam -> int 1  -- ?
  IsBig -> error "IsBig"
  GetNumProcessors -> error "GetNumProcessors"
  PrintInt -> printer "Int" $ ppE $ head pes
  PrintChar -> printer "Char" $ ppE $ head pes
  PrintFloat -> printer "Float" $ ppE $ head pes
  PrintBool -> ppAp "(fn true => \"True\" | false => \"False\")" pes
  PrintSym -> ppAp "print" pes
  ReadInt -> error "ReadInt"  -- Have every program read from stdin?
  DictInsertP _ -> error "DictInsertP"
  DictLookupP _ -> error "DictLookupP"
  DictEmptyP _ -> error "DictEmptyP"
  DictHasKeyP _ -> error "DictHasKeyP"
  SymSetEmpty -> error "SymSetEmpty"
  SymSetInsert -> error "SymSetInsert"
  SymSetContains -> error "SymSetContains"
  SymHashEmpty -> error "SymHashEmpty"
  SymHashInsert -> error "SymHashInsert"
  SymHashLookup -> error "SymHashLookup"
  SymHashContains -> error "SymHashContains"
  IntHashEmpty -> error "IntHashEmpty"
  IntHashInsert -> error "IntHashInsert"
  IntHashLookup -> error "IntHashLookup"
  PDictAllocP _ty0 _ty0' -> error "PDictAllocP"
  PDictInsertP _ty0 _ty0' -> error "PDictInsertP"
  PDictLookupP _ty0 _ty0' -> error "PDictLookupP"
  PDictHasKeyP _ty0 _ty0' -> error "PDictHasKeyP"
  PDictForkP _ty0 _ty0' -> error "PDictForkP"
  PDictJoinP _ty0 _ty0' -> error "PDictJoinP"
  LLAllocP _ty0 -> error "LLAllocP"
  LLIsEmptyP _ty0 -> error "LLIsEmptyP"  -- Implement these? 
  LLConsP _ty0 -> error "LLConsP"
  LLHeadP _ty0 -> error "LLHeadP"
  LLTailP _ty0 -> error "LLTailP"
  LLFreeP _ty0 -> error "LLFreeP"
  LLFree2P _ty0 -> error "LLFree2P"
  LLCopyP _ty0 -> error "LLCopyP"
  VAllocP _ty0 ->
    ppAp "(fn internal__ => ArraySlice.full(Array.array(internal__, 0)))" pes
  VFreeP _ty0 -> error "VFreeP"
  VFree2P _ty0 -> error "VFree2P"
  VLengthP _ty0 -> ppAp "ArraySlice.length" pes
  VNthP _ty0 -> ppAp "ArraySlice.sub" pes
  VSliceP _ty0 -> case pes of
    [pe1, pe2, pe3] -> hcat
      [ "ArraySlice.subslice"
      , parens $ interleave comma
        [ ppE pe3
        , ppE pe1
        , parens $ "SOME" <+> ppE pe2
        ]
      ]
    _ -> _
  InplaceVUpdateP _ty0 -> hsep
      [ "let val _ ="
      , ppAp "ArraySlice.update" pes
      , "in", ppE $ head pes
      , "end"
      ]
  VConcatP _ty0 -> ppFail "VConcatP"
  VSortP _ty0 -> ppFail "VSortP"
  InplaceVSortP _ty0 -> ppCurried qsort pes
  VMergeP _ty0 -> ppFail "VMergeP"
  Write3dPpmFile _s -> error "Write3dPpmFile"
  ReadPackedFile _m_s _s _m_var _ty0 -> error "ReadPackedFile"
  WritePackedFile _s _ty0 -> error "WritePackedFile"
  ReadArrayFile _ma _ty0 -> error "ReadArrayFile"
  RequestEndOf -> error "RequestEndOf"
  RequestSizeOf -> error "RequestSizeOf"
  Gensym -> error "Gensym"

ppProgram :: Prog1 -> Doc
ppProgram prog = hcat
  [ ppDDefs $ ddefs prog
  , ppFunDefs $ fundefs prog
  , ppMainExpr $ mainExp prog
  , "\n"
  ]

ppFunDefs :: Map Var (FunDef Exp1) -> Doc
ppFunDefs funDefs =
  foldMap ppBlock organize
  where
    ppBlock = either ppValDef ppFunRec
    organize = sortDefs (elems funDefs) >>= separateDefs

separateDefs :: [FunDef Exp1] -> [Either (FunDef Exp1) [FunDef Exp1]]
separateDefs funDefs = case funDefs of
  [] -> []
  fd : fds -> case funArgs fd of
    [] -> Left fd : separateDefs fds
    _ -> case separateDefs fds of
      [] -> [Right [fd]]
      fds'@(Left _ : _) -> Right [fd] : fds'
      Right fds' : fds'' ->  Right (fd : fds') : fds''

ppValDef :: FunDef Exp1 -> Doc
ppValDef funDef =
  hsep
    [ "val"
    , ppVar $ funName funDef
    , "="
    , ppE $ funBody funDef
    ] <> semi

ppFunRec :: [FunDef Exp1] -> Doc
ppFunRec fdefs =
  reduceFunDefs "fun" (head fdefs) $
    foldr (reduceFunDefs "and") ";\n" (tail fdefs)

reduceFunDefs :: Doc -> FunDef Exp1 -> Doc -> Doc
reduceFunDefs keyword funDef doc =
  "\n" <> case funArgs funDef of
    [] -> hsep
      [ keyword
      , ppVar $ funName funDef
      , "="
      , ppE $ funBody funDef
      ] <> doc
    fargs -> hsep
      [ keyword
      , ppVar name
      , parens $ interleave comma $ ppVar <$> fargs
      , "="
      , case name of
        "print_check" -> parens mempty
        "print_space" -> "print \" \""
        "print_newline" -> "print \"\\n\""
        _ -> ppE $ funBody funDef
      ] <> doc
      where name = funName funDef

ppMainExpr :: Maybe (Exp1, Ty1) -> Doc
ppMainExpr opt = case opt of
  Nothing -> mempty
  Just (exp1, ty1) -> 
    "val _ = " <> printerTy1 ty1 (ppE exp1) <> semi
    <> "\nval _ = print \"\\n\""

ppDDefs :: DDefs1 -> Doc
ppDDefs ddefs = case elems ddefs of
  [] -> mempty
  h : t -> hsep
    [ "datatype"
    , ppDDef h
    , hcat $ ("\nand" <+>) . ppDDef <$> t
    , ";\n"
    ]

ppDDef :: DDef1 -> Doc
ppDDef ddef = hsep
  [ hsep $ ppTyVar <$> tyArgs ddef
  , ("dat_" <>) $ ppVar $ tyName ddef
  , "="
  , interleave
      "|"
      (ppBody <$> dataCons ddef)
  ]
  where
    ppBody (s, lst) = text s <+> case lst of
      [] -> mempty
      _ -> "of" <+> parens (interleave " *" $ ppTy1 . snd <$> lst)

ppTyVar :: TyVar -> Doc
ppTyVar tyVar = case tyVar of
  BoundTv var -> "'" <> ppVar var
  SkolemTv _s _n -> _
  UserTv var -> "'" <> ppVar var

ppTy1 :: Ty1 -> Doc
ppTy1 ty1 = case ty1 of
  IntTy -> "int"
  CharTy -> "char"
  FloatTy -> "real"
  BoolTy -> "bool"
  ProdTy ty1s -> interleave " * " $ ppTy1 <$> ty1s
  SymDictTy _m_var _ty1' -> _
  PDictTy _ty1' _ty12 -> _
  SymSetTy -> _
  SymHashTy -> _
  IntHashTy -> _
  PackedTy s () -> " dat_" <> text s
  VectorTy ty1' -> ppTy1 ty1' <+> "ArraySlice.slice"
  ListTy ty1' -> ppTy1 ty1' <+> "list"
  ArenaTy -> _

  SymTy -> _
  PtrTy -> _
  CursorTy -> _

printerTy1 :: Ty1 -> Doc -> Doc
printerTy1 ty1 d = case ty1 of
  IntTy -> printer "Int" d
  CharTy -> printer "Char" d
  FloatTy -> printer "Float" d
  SymTy -> _
  BoolTy -> parens $ "(fn true => print \"True\" | false => print \"False\") " <> d
  ProdTy uts -> 
    parens $ hsep
      [ "case", d, "of"
      , parens $ interleave comma $ ("x__" <>) . int . fst <$> zip [1..] uts
      , "-> let"
      , foldMap ppSub $ zip [1..] uts
      , "in ()"
      ]
    where
      ppSub (i, x) = "val _ = " <> printerTy1 x ("x__" <> int i)
  SymDictTy _m_var _ut -> _
  PackedTy s () -> "internal_print_" <> text s <> parens d
  VectorTy ut -> 
    parens $ hsep
      [ quotePrint "#("
      , toss $ hsep 
        [ "case length", d, "of"
        , "0 -> ()"
        , "1 ->", printerTy1 ut $ "ArraySlice.sub" <> parens (d <> ", 0")
        , "_ ->"
        , toss $ printerTy1 ut $ "ArraySlice.sub" <> parens (d <> ", 0")
        , "ArraySlice.app", parens $ 
          "fn y__ => " <> quotePrint ", " <> printerTy1 ut "y__"
        , "xs__"
        ]
      , "print \")\""
      ]
  PDictTy _ut _ut' -> _
  ListTy ut -> 
    parens $ hsep
      [ quotePrint "["
      , toss $ hsep [ "case", d, "of"
        , "[] -> ()"
        , "| [x__] ->", printerTy1 ut "x__"
        , "| [x__ :: xs__] ->"
        , toss $ printerTy1 ut "x__"
        , "list.app", parens $ 
          "fn y__ => " <> quotePrint ", " <> printerTy1 ut "y__"
        , "xs__"
        ]
      , "print \"]\""
      ]
  ArenaTy -> _
  SymSetTy -> _
  SymHashTy -> _
  IntHashTy -> _
  PtrTy -> _
  CursorTy -> _

printer :: Doc -> Doc -> Doc
printer p d = parens $ "print" <> parens (p <> ".toString" <> parens d)

toss :: Doc -> Doc
toss s = "let val _ = " <> s <> " in "
justPrint :: Doc -> Doc
justPrint s = toss $ "print " <> s
quotePrint :: Doc -> Doc
quotePrint = justPrint . quotes

qsort :: Doc
qsort = parens $ text
  "fn arr => fn cmp => \n\
  \  let\n\
  \    fun qsort(arr, lo, hi) = \n\
  \      if cmp lo hi < 0 then\n\
  \        let\n\
  \          val pivot = ArraySlice.sub(arr, hi)\n\
  \          val i = ref (lo - 1)\n\
  \          val j = ref lo\n\
  \          val _ = \n\
  \            while cmp (!j) (hi - 1) < 1 do\n\
  \              let\n\
  \                val _ = \n\
  \                  if cmp (ArraySlice.sub(arr, !j)) pivot < 0 then\n\
  \                    let\n\
  \                      val _ = i := !i + 1\n\
  \                      val tmp = ArraySlice.sub(arr, !i)\n\
  \                      val _ = ArraySlice.update(arr, !i, ArraySlice.sub(arr, !j))\n\
  \                      val _ = ArraySlice.update(arr, !j, tmp)\n\
  \                    in\n\
  \                      ()\n\
  \                    end\n\
  \                  else ()\n\
  \              in\n\
  \                j := !j + 1\n\
  \              end\n\
  \          val tmp = ArraySlice.sub(arr, !i + 1)\n\
  \          val _ = ArraySlice.update(arr, !i + 1, ArraySlice.sub(arr, hi))\n\
  \          val _ = ArraySlice.update(arr, hi, tmp)\n\
  \          val p = !i + 1\n\
  \          val _ = qsort(arr, lo, p - 1)\n\
  \          val _ = qsort(arr, p + 1, hi)\n\
  \        in\n\
  \          ()\n\
  \        end\n\
  \    else ()\n\
  \    val _ = qsort(arr, 0, ArraySlice.length arr - 1)\n\
  \  in\n\
  \    arr\
  \  end\n"

varsEs :: Set.Set String -> [Exp1] -> Set.Set String
varsEs = foldMap . varsE

varsE :: Set.Set String -> Exp1 -> Set.Set String
varsE vs pe0 = case pe0 of
  -- VarE var -> collect var
  VarE _ -> mempty
  AppE var _ pes -> vpes pes <> collect var
  PrimAppE _ pes -> vpes pes
  LetE (_, _, _, pe') pe -> vpe pe <> vpe pe'
  IfE pe pe' pe3 -> vpes [pe, pe', pe3]
  MkProdE pes -> vpes pes
  ProjE _ pe -> vpe pe
  CaseE pe x0 -> vpe pe <> foldMap (\(_, _, pe') -> vpe pe') x0
  DataConE _ _ pes -> vpes pes
  TimeIt pe _ _ -> vpe pe
  WithArenaE _ pe -> vpe pe
  SpawnE _ _ pes -> vpes pes
  SyncE -> _
  MapE _ _ -> _
  FoldE {} -> _
  _ -> mempty
  where
    vpe = varsE vs
    vpes = varsEs vs
    collect var
      | Set.member s vs = Set.singleton s
      | otherwise = mempty
      where s = getVar var

addFunBinding :: FunDef ex -> Map String (FunDef ex) -> Map String (FunDef ex)
addFunBinding funDef = Map.insert (getVar $ funName funDef) funDef

allFunEntries :: [FunDef ex] -> Map String (FunDef ex)
allFunEntries = foldr addFunBinding Map.empty

allFunNames :: [FunDef ex] -> Set.Set String
allFunNames = Set.fromList . fmap (getVar . funName)

getDependencies :: [FunDef Exp1] -> Map String [FunDef Exp1]
getDependencies funDefs =
  foldr reduceDeps Map.empty funDefs
  where
    funMap = allFunEntries funDefs
    funSet = allFunNames funDefs
    toNode = fromMaybe _ . flip Map.lookup funMap
    toDep = fmap toNode . Set.toList . varsE funSet . funBody
    reduceDeps = insert . getVar . funName <*> toDep

sortDefs :: [FunDef Exp1] -> [[FunDef Exp1]]
sortDefs defs =
  fmap ((\(_, n, _) -> n) . back) . flatten <$> scc gr
  where
    (gr, back, _) = graphFromEdges $ mkNode <$> toList depMap
    mkNode (s, lst) = (s, fromMaybe _ (Map.lookup s nameMap), lst)
    depMap = getDependencies defs
    nameMap = fromList $ join ((,) . getVar . funName) <$> defs
