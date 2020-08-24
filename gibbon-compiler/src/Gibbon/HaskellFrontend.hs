{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}

module Gibbon.HaskellFrontend
  ( parseFile, primMap, multiArgsToOne ) where

import           Data.Foldable ( foldrM )
import           Data.Maybe (catMaybes, isJust)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.IORef
import           Language.Haskell.Exts.Extension
import           Language.Haskell.Exts.Parser
import           Language.Haskell.Exts.Syntax as H
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Exts.SrcLoc
import           System.Environment ( getEnvironment )
import           System.Directory
import           System.FilePath
import           Control.Monad

import           Gibbon.L0.Syntax as L0
import           Gibbon.Common

--------------------------------------------------------------------------------

{-

Importing modules:
~~~~~~~~~~~~~~~~~~

We use the same notion of search paths as GHC[1], except that GHC also has a
set of "known" packages (base, containers, etc.) where it looks for modules.
Gibbon doesn't have those, and the rootset for our search is a singleton {"."}.
Consider this directory structure:
    .
    |── A
    |   └── B
    |       |── C.hs
    |       |── D.hs
    |       |── Foo.hs
    |── Bar.hs

If Bar.hs has a `import A.B.C`, we look for a file `./A/B/C.hs`. However, note
that this design is much more primitive than what Cabal/Stack allow. Can A.B.C
import A.B.D? It depends on where we invoke GHC from. If we do it from ".", then
yes, because A.B.D exists at A/B/D.hs. But if we run "ghc C.hs", it will fail since
it expects A.B.D to be at A/B/A/B/D.hs.

[1] https://downloads.haskell.org/ghc/8.6.4/docs/html/users_guide/separate_compilation.html?#the-search-path

-}


parseFile :: FilePath -> IO (PassM Prog0)
parseFile path = do
    pstate0_ref <- newIORef emptyParseState
    parseFile' pstate0_ref [] path

data ParseState = ParseState
    { imported :: M.Map (String, FilePath) Prog0 }

emptyParseState :: ParseState
emptyParseState = ParseState M.empty

parseMode :: ParseMode
parseMode = defaultParseMode { extensions = [ EnableExtension ScopedTypeVariables
                                            , EnableExtension CPP ]
                                            ++ (extensions defaultParseMode)
                             }

parseFile' :: IORef ParseState -> [String] -> FilePath -> IO (PassM Prog0)
parseFile' pstate_ref import_route path = do
  str <- readFile path
  let parsed = parseModuleWithMode parseMode str
  case parsed of
    ParseOk hs -> desugarModule pstate_ref import_route (takeDirectory path) hs
    ParseFailed _ er -> do
      error ("haskell-src-exts failed: " ++ er)

data TopLevel
  = HDDef (DDef Ty0)
  | HFunDef (FunDef Exp0)
  | HMain (Maybe (Exp0, Ty0))
  | HInline Var
  deriving (Show, Eq)

type TopTyEnv = TyEnv TyScheme

desugarModule :: (Show a,  Pretty a)
              => IORef ParseState -> [String] -> FilePath -> Module a -> IO (PassM Prog0)
desugarModule pstate_ref import_route dir (Module _ head_mb _pragmas imports decls) = do
  let -- Since top-level functions and their types can't be declared in
      -- single top-level declaration we first collect types and then collect
      -- definitions.
      funtys = foldr collectTopTy M.empty decls
  imported_progs :: [PassM Prog0] <- mapM (processImport pstate_ref (mod_name : import_route) dir) imports
  let prog = do
        toplevels <- catMaybes <$> mapM (collectTopLevel funtys) decls
        let (defs,_vars,funs,inlines,main) = foldr classify init_acc toplevels
            funs' = foldr (\v acc -> M.update (\fn -> Just (fn {funInline = Inline})) v acc) funs inlines
        imported_progs' <- mapM id imported_progs
        let (defs0,funs0) =
              foldr
                (\Prog{ddefs,fundefs} (defs1,funs1) ->
                     let ddef_names1 = M.keysSet defs1
                         ddef_names2 = M.keysSet ddefs
                         fn_names1 = M.keysSet funs1
                         fn_names2 = M.keysSet fundefs
                         em1 = S.intersection ddef_names1 ddef_names2
                         em2 = S.intersection fn_names1 fn_names2
                         conflicts1 = foldr
                                        (\d acc ->
                                             if (ddefs M.! d) /= (defs1 M.! d)
                                             then d : acc
                                             else acc)
                                        []
                                        em1
                         conflicts2 = foldr
                                        (\f acc ->
                                             if (fundefs M.! f) /= (funs1 M.! f)
                                             then dbgTraceIt (sdoc ((fundefs M.! f), (funs1 M.! f))) (f : acc)
                                             else acc)
                                        []
                                        em2
                     in case (conflicts1, conflicts2) of
                            ([], []) -> (M.union ddefs defs1,  M.union fundefs funs1)
                            (_x:_xs,_) -> error $ "Conflicting definitions of " ++ show conflicts1 ++ " found in " ++ mod_name
                            (_,_x:_xs) -> error $ "Conflicting definitions of " ++ show (S.toList em2) ++ " found in " ++ mod_name)
                (defs, funs')
                imported_progs'
        pure (Prog defs0 funs0 main)
  pure prog
  where
    init_acc = (M.empty, M.empty, M.empty, S.empty, Nothing)
    mod_name = moduleName head_mb

    moduleName :: Maybe (ModuleHead a) -> String
    moduleName Nothing = "Main"
    moduleName (Just (ModuleHead _ mod_name1 _warnings _exports)) =
      mnameToStr mod_name1

    classify thing (defs,vars,funs,inlines,main) =
      case thing of
        HDDef d   -> (M.insert (tyName d) d defs, vars, funs, inlines, main)
        HFunDef f -> (defs, vars, M.insert (funName f) f funs, inlines, main)
        HMain m ->
          case main of
            Nothing -> (defs, vars, funs, inlines, m)
            Just _  -> error $ "A module cannot have two main expressions."
                               ++ show mod_name
        HInline v   -> (defs,vars,funs,S.insert v inlines,main)
desugarModule _ _ _ m = error $ "desugarModule: " ++ prettyPrint m

stdlibModules :: [String]
stdlibModules = ["Gibbon.Prelude", "Gibbon.Vector", "Gibbon.Vector.Parallel"]

processImport :: IORef ParseState -> [String] -> FilePath -> ImportDecl a -> IO (PassM Prog0)
processImport pstate_ref import_route dir decl@ImportDecl{..} = do
    when (mod_name `elem` import_route) $
      error $ "Circular dependency detected. Import path: "++ show (mod_name : import_route)
    when (importQualified) $ error $ "Qualified imports not supported yet. Offending import: " ++  prettyPrint decl
    when (isJust importAs) $ error $ "Module aliases not supported yet. Offending import: " ++  prettyPrint decl
    when (isJust importSpecs) $ error $ "Selective imports not supported yet. Offending import: " ++  prettyPrint decl
    (ParseState imported) <- readIORef pstate_ref
    mod_fp <- if mod_name `elem` stdlibModules
                then stdlibImportPath mod_name
                else modImportPath importModule dir
    dbgTrace 5 ("Looking at " ++ mod_name) (pure ())
    dbgTrace 5 ("Previously imported: " ++ show (M.keysSet imported)) (pure ())
    prog <- case M.lookup (mod_name, mod_fp) imported of
                Just prog -> do
                    dbgTrace 5 ("Already imported " ++ mod_name) (pure ())
                    pure prog
                Nothing -> do
                    dbgTrace 5 ("Importing " ++ mod_name ++ " from " ++ mod_fp) (pure ())
                    prog0 <- parseFile' pstate_ref import_route mod_fp
                    (ParseState imported') <- readIORef pstate_ref
                    let (prog0',_) = defaultRunPassM prog0
                    let imported'' = M.insert (mod_name, mod_fp) prog0' imported'
                    let pstate' = ParseState { imported = imported'' }
                    writeIORef pstate_ref pstate'
                    pure prog0'

    pure (pure prog)
  where
    mod_name = mnameToStr importModule

stdlibImportPath :: String -> IO FilePath
stdlibImportPath mod_name = do
    env <- getEnvironment
    let stdlibPath = case lookup "GIBBONDIR" env of
                    Just p -> p </> "gibbon-stdlib" </> modNameToFilename mod_name
                    -- Assume we're running from the compiler dir!
                    Nothing -> modNameToFilename mod_name
    e <- doesFileExist stdlibPath
    unless e $ error$ "stdlib.hs file not found at path: "++stdlibPath
                     ++"\n Consider setting GIBBONDIR to repo root.\n"
    pure stdlibPath
  where
    modNameToFilename :: String -> String
    modNameToFilename "Gibbon.Prelude" = "Gibbon" </> "Prelude.hs"
    modNameToFilename "Gibbon.Vector" = "Gibbon" </> "Vector.hs"
    modNameToFilename "Gibbon.Vector.Parallel" = "Gibbon" </> "Vector" </> "Parallel.hs"
    modNameToFilename oth = error $ "Unknown module: " ++ oth

modImportPath :: ModuleName a -> String -> IO FilePath
modImportPath importModule dir = do
    let mod_name = mnameToStr importModule
    mb_fp <- findModule dir importModule
    case mb_fp of
        Nothing -> error $ "Cannot find module: " ++
                   show mod_name ++ " in " ++ dir
        Just mod_fp -> pure mod_fp

-- | Look for a module on the filesystem.
findModule :: FilePath -> ModuleName a -> IO (Maybe FilePath)
findModule dir m = do
  let mod_fp  = dir </> moduleNameToSlashes m <.> "hs"
  doesFileExist mod_fp >>= \b ->
    if b
    then pure $ Just mod_fp
    else pure Nothing

-- | Returns the string version of the module name, with dots replaced by slashes.
--
moduleNameToSlashes :: ModuleName a -> String
moduleNameToSlashes (ModuleName _ s) = dots_to_slashes s
  where dots_to_slashes = map (\c -> if c == '.' then pathSeparator else c)


builtinTys :: S.Set Var
builtinTys = S.fromList $
    [ "Int", "Float", "Bool", "Sym", "SymHash", "SymSet", "SymDict", "Arena", "Vector" ]

keywords :: S.Set Var
keywords = S.fromList $ map toVar $
    [ "quote", "bench", "error", "par", "spawn", "is_big"
    -- operations on vectors
    , "valloc", "vnth", "vlength", "vslice", "inplacevupdate",
      "vsort", "inplacevsort", "vfree", "vfree2"
    ] ++ M.keys primMap

desugarTopType :: (Show a,  Pretty a) => Type a -> TyScheme
desugarTopType ty =
  case ty of
    -- forall tvs ty.
    TyForall _ mb_tvbind _ ty1 ->
      let tyvars = case mb_tvbind of
                     Just bnds -> map desugarTyVarBind bnds
                     Nothing   -> []
      in ForAll tyvars (desugarType ty1)
    -- quantify over all tyvars.
    _ -> let ty' = desugarType ty
             tyvars = tyVarsInTy ty'
        in ForAll tyvars ty'

desugarType :: (Show a,  Pretty a) => Type a -> Ty0
desugarType ty =
  case ty of
    H.TyVar _ (Ident _ t) -> L0.TyVar $ UserTv (toVar t)
    TyTuple _ Boxed tys   -> ProdTy (map desugarType tys)
    TyCon _ (Special _ (UnitCon _))     -> ProdTy []
    TyCon _ (UnQual _ (Ident _ "Int"))  -> IntTy
    TyCon _ (UnQual _ (Ident _ "Float"))-> FloatTy
    TyCon _ (UnQual _ (Ident _ "Bool")) -> BoolTy
    TyCon _ (UnQual _ (Ident _ "Sym"))  -> SymTy0
    TyCon _ (UnQual _ (Ident _ "SymSet"))  -> SymSetTy
    TyCon _ (UnQual _ (Ident _ "SymHash"))  -> SymHashTy
    TyCon _ (UnQual _ (Ident _ con))    -> PackedTy con []
    TyFun _ t1 t2 -> let t1' = desugarType t1
                         t2' = desugarType t2
                     in ArrowTy [t1'] t2'
    TyParen _ ty1 -> desugarType ty1
    TyApp _ tycon arg ->
      case desugarType tycon of
        PackedTy con tyargs ->
            case (con,tyargs) of
                ("Vector",[]) -> VectorTy (desugarType arg)
                _ -> PackedTy con (tyargs ++ [desugarType arg])
        _ -> error $ "desugarType: Unexpected type arguments: " ++ prettyPrint ty
    _ -> error $ "desugarType: Unsupported type: " ++ prettyPrint ty


-- Like 'desugarTopType' but understands boxity.
desugarTopType' :: (Show a,  Pretty a) => Type a -> (IsBoxed, TyScheme)
desugarTopType' ty =
  case ty of
    -- forall tvs ty.
    TyForall _ mb_tvbind _ ty1 ->
      let tyvars = case mb_tvbind of
                     Just bnds -> map desugarTyVarBind bnds
                     Nothing   -> []
          (boxity, ty') = desugarType' ty1
      in (boxity, ForAll tyvars ty')
    -- quantify over all tyvars.
    _ -> let (boxity, ty') = desugarType' ty
             tyvars = tyVarsInTy ty'
        in (boxity, ForAll tyvars ty')

-- Like 'desugarType' but understands boxity.
desugarType' :: (Show a,  Pretty a) => Type a -> (IsBoxed, Ty0)
desugarType' ty =
  case ty of
    TyBang _ _ (NoUnpack _) ty1 -> (True, desugarType ty1)
    _ -> (False, desugarType ty)

-- | Transform a multi-argument function type to one where all inputs are a
-- single tuple argument. E.g. (a -> b -> c -> d) => ((a,b,c) -> d).
unCurryTopTy :: TyScheme -> TyScheme
unCurryTopTy (ForAll tyvars ty) = ForAll tyvars (unCurryTy ty)

unCurryTy :: Ty0 -> Ty0
unCurryTy ty1 =
  case ty1 of
    ArrowTy _ ArrowTy{} ->
      let (a,b) = go [] ty1
          a' = map unCurryTy a
      in ArrowTy a' b
    _ -> ty1
  where
    go :: [Ty0] -> Ty0 -> ([Ty0], Ty0)
    go acc ty =
      case ty of
        ArrowTy as b -> (go (acc++as) b)
        _ -> (acc,ty)

-- ^ A map between SExp-frontend prefix function names, and Gibbon
-- abstract Primops.
primMap :: M.Map String (Prim a)
primMap = M.fromList
  [ ("+", AddP)
  , ("-", SubP)
  , ("*", MulP)
  , ("/", DivP)
  , ("div", DivP)
  , ("^", ExpP)
  , (".+.", FAddP)
  , (".-.", FSubP)
  , (".*.", FMulP)
  , ("./.", FDivP)
  , ("sqrt", FSqrtP)
  , ("==", EqIntP)
  , (".==.", EqFloatP)
  , ("<", LtP)
  , (">", GtP)
  , ("<=", LtEqP)
  , (">=", GtEqP)
  , (".<.", FLtP)
  , (".>.", FGtP)
  , (".<=.", FLtEqP)
  , (".>=.", FGtEqP)
  , ("mod", ModP)
  , ("||" , OrP)
  , ("&&", AndP)
  , ("eqsym", EqSymP)
  , ("rand", RandP)
  , ("frand", FRandP)
  , ("intToFloat", IntToFloatP)
  , ("floatToInt", FloatToIntP)
  , ("sizeParam", SizeParam)
  , ("getNumProcessors", GetNumProcessors)
  , ("True", MkTrue)
  , ("False", MkFalse)
  , ("gensym", Gensym)
  , ("printint", PrintInt)
  , ("printfloat", PrintFloat)
  , ("printbool", PrintBool)
  , ("printsym", PrintSym)
  , ("readint", ReadInt)
  , ("is_big", IsBig)
  , ("empty_set", SymSetEmpty)
  , ("insert_set", SymSetInsert)
  , ("contains_set", SymSetContains)
  , ("empty_hash", SymHashEmpty)
  , ("insert_hash", SymHashInsert)
  , ("lookup_hash", SymHashLookup)
  ]

desugarExp :: (Show a, Pretty a) => TopTyEnv -> Exp a -> PassM Exp0
desugarExp toplevel e =
  case e of
    Paren _ (ExpTypeSig _ (App _ (H.Var _ f) (Lit _ lit)) tyc)
        | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit) (desugarType tyc)) []
    -- Paren _ (App _ (H.Var _ f) (Lit _ lit))
    --     | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit
    Paren _ e2 -> desugarExp toplevel e2
    H.Var _ qv -> do
      let v = (toVar $ qnameToStr qv)
      if v == "gensym"
      then pure $ PrimAppE Gensym []
      else if v == "rand"
      then pure $ PrimAppE RandP []
      else if v == "frand"
      then pure $ PrimAppE FRandP []
      else if v == "sync"
      then pure SyncE
      else if v == "sizeParam"
      then pure $ PrimAppE SizeParam []
      else if v == "getNumProcessors"
      then pure $ PrimAppE GetNumProcessors []
      else if v == "empty_set"
      then pure $ PrimAppE SymSetEmpty []
      else if v == "empty_hash"
      then pure $ PrimAppE SymHashEmpty []
      else case M.lookup v toplevel of
             Just sigma ->
               case tyFromScheme sigma of
                 ArrowTy{} ->
                   -- Functions with >0 args must be VarE's here -- the 'App _ e1 e2'
                   -- case below depends on it.
                   pure $ VarE v
                 -- Otherwise, 'v' is a top-level value binding, which we
                 -- encode as a function which takes no arguments.
                 _ -> pure $ AppE v [] []
             Nothing -> pure $ VarE v
    Lit _ lit  -> desugarLiteral lit

    Lambda _ pats bod -> do
      bod' <- desugarExp toplevel bod
      args <- mapM desugarPatWithTy pats
      pure $ Ext $ LambdaE args bod'

    App _ e1 e2 -> do
        desugarExp toplevel e1 >>= \case
          (VarE f) ->
            case M.lookup (fromVar f) primMap of
              Just p  -> (\e2' -> PrimAppE p [e2']) <$> desugarExp toplevel e2
              Nothing ->
                  if f == "quote"
                  then case e2 of
                         Lit _ lit -> pure $ LitSymE (toVar $ litToString lit)
                         _ -> error "desugarExp: quote only works with String literals. E.g quote \"hello\""
                  else if f == "readArrayFile"
                  then case e2 of
                         Tuple _ Boxed [Lit _ name,Lit _ len] -> do
                           t <- newMetaTy
                           pure $ PrimAppE (ReadArrayFile (Just (litToString name, litToInt len)) t) []
                         Con _ (Special _ (UnitCon _)) -> do
                           t <- newMetaTy
                           pure $ PrimAppE (ReadArrayFile Nothing t) []
                         _ -> error $ "desugarExp: couldn't parse readArrayFile; " ++ prettyPrint e2
                  else if f == "bench"
                  then do
                    e2' <- desugarExp toplevel e2
                    pure $ Ext $ BenchE "HOLE" [] [e2'] False
                  else if f == "timeit"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty <- newMetaTy
                    pure $ TimeIt e2' ty False
                  else if f == "iterate"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty <- newMetaTy
                    pure $ TimeIt e2' ty True
                  else if f == "error"
                  then case e2 of
                         Lit _ lit -> pure $ PrimAppE (ErrorP (litToString lit) IntTy) [] -- assume int (!)
                         _ -> error "desugarExp: error expects String literal."
                  else if f == "par"
                  then do
                    e2' <- desugarExp toplevel e2
                    pure $ Ext $ ParE0 [e2']
                  else if f == "spawn"
                  then do
                    e2' <- desugarExp toplevel e2
                    pure $ SpawnE "HOLE" [] [e2']
                  else if f == "valloc"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VAllocP ty) [e2']
                  else if f == "vfree"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VFreeP ty) [e2']
                  else if f == "vfree2"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VFree2P ty) [e2']
                  else if f == "vnth"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VNthP ty) [e2']
                  else if f == "vlength"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VLengthP ty) [e2']
                  else if f == "inplacevupdate"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (InplaceVUpdateP ty) [e2']
                  else if f == "vconcat"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VConcatP ty) [e2']
                  else if f == "vsort"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VSortP ty) [e2']
                  else if f == "inplacevsort"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (InplaceVSortP ty) [e2']
                  else if f == "vslice"
                  then do
                    e2' <- desugarExp toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VSliceP ty) [e2']
                  else if f == "fst"
                  then do
                    e2' <- desugarExp toplevel e2
                    pure $ ProjE 0 e2'
                  else if f == "snd"
                  then do
                    e2' <- desugarExp toplevel e2
                    pure $ ProjE 1 e2'
                  else AppE f [] <$> (: []) <$> desugarExp toplevel e2
          (DataConE tyapp c as) ->
            case M.lookup c primMap of
              Just p  -> pure $ PrimAppE p as
              Nothing ->
                  if c == "quote"
                  then case e2 of
                         Lit _ lit -> pure $ LitSymE (toVar $ litToString lit)
                         _ -> error "desugarExp: quote only works with String literals. E.g quote \"hello\""
                  else if c == "readArrayFile"
                  then case e2 of
                         Tuple _ Boxed [Lit _ name,Lit _ len] -> do
                           t <- newMetaTy
                           pure $ PrimAppE (ReadArrayFile (Just (litToString name, litToInt len)) t) []
                         Con _ (Special _ (UnitCon _)) -> do
                           t <- newMetaTy
                           pure $ PrimAppE (ReadArrayFile Nothing t) []
                         _ -> error $ "desugarExp: couldn't parse readArrayFile; " ++ prettyPrint e2
                  else (\e2' -> DataConE tyapp c (as ++ [e2'])) <$> desugarExp toplevel e2
          (Ext (ParE0 ls)) -> do
            e2' <- desugarExp toplevel e2
            pure $ Ext $ ParE0 (ls ++ [e2'])
          (AppE f [] ls) -> do
            e2' <- desugarExp toplevel e2
            pure $ AppE f [] (ls ++ [e2'])

          (Ext (BenchE fn [] ls b)) -> do
            e2' <- desugarExp toplevel e2
            pure $ Ext $ BenchE fn [] (ls ++ [e2']) b

          (SpawnE fn [] ls) -> do
            e2' <- desugarExp toplevel e2
            pure $ SpawnE fn [] (ls ++ [e2'])

          (PrimAppE p ls) -> do
            e2' <- desugarExp toplevel e2
            pure $ PrimAppE p (ls ++ [e2'])

          TimeIt{} ->
            error "desugarExp: TimeIt can only accept 1 expression."

          f -> error ("desugarExp: Couldn't parse function application: (: " ++ show f ++ ")")

    Let _ (BDecls _ decls) rhs -> do
      rhs' <- desugarExp toplevel rhs
      let funtys = foldr collectTopTy M.empty decls
      foldrM (generateBind toplevel funtys) rhs' decls

    If _ a b c -> do
      a' <- desugarExp toplevel a
      b' <- desugarExp toplevel b
      c' <- desugarExp toplevel c
      pure $ IfE a' b' c'

    Tuple _ Unboxed _ -> error $ "desugarExp: Only boxed tuples are allowed: " ++ prettyPrint e
    Tuple _ Boxed es  -> MkProdE <$> mapM (desugarExp toplevel) es

    Case _ scrt alts -> do
      scrt' <- desugarExp toplevel scrt
      CaseE scrt' <$> mapM (desugarAlt toplevel) alts

    Con _ (Special _ (UnitCon _)) -> pure $ MkProdE []

    Con _ qname -> do
      let dcon = qnameToStr qname
      case M.lookup dcon primMap of
        Just p  -> pure $ PrimAppE p []
        Nothing -> do
          -- Just a placeholder for now, the typechecker will fill this hole.
          ty <- newMetaTy
          pure $ DataConE ty dcon []

    -- TODO: timeit: parsing it's type isn't straightforward.

    InfixApp _ e1 (QVarOp _ (UnQual _ (Symbol _ "!!!"))) e2 -> do
      e1' <- desugarExp toplevel e1
      case e2 of
        Lit _ lit -> do
          let i = litToInt lit
          pure $ ProjE i e1'
        _ -> error $ "desugarExp: !!! expects a integer. Got: " ++ prettyPrint e2

    InfixApp _ e1 op e2 -> do
      e1' <- desugarExp toplevel e1
      e2' <- desugarExp toplevel e2
      let op' = desugarOp op
      pure $ PrimAppE op' [e1', e2']

    NegApp _ e1 -> do
      e1' <- desugarExp toplevel e1
      pure $ PrimAppE SubP [LitE 0, e1']

    _ -> error ("desugarExp: Unsupported expression: " ++ prettyPrint e)

desugarFun :: (Show a,  Pretty a) => TopTyEnv -> TopTyEnv -> Decl a -> PassM (Var, [Var], TyScheme, Exp0)
desugarFun toplevel env decl =
  case decl of
    FunBind _ [Match _ fname pats (UnGuardedRhs _ bod) _where] -> do
      let fname_str = nameToStr fname
          fname_var = toVar (fname_str)
      args <- mapM (\p -> desugarPatWithTy p >>= pure . fst) pats
      fun_ty <- case M.lookup fname_var env of
                  Nothing -> do
                     arg_tys <- mapM (\_ -> newMetaTy) args
                     ret_ty  <- newMetaTy
                     let funty = ArrowTy arg_tys ret_ty
                     pure $ (ForAll [] funty)
                  Just ty -> pure ty
      bod' <- desugarExp toplevel bod
      pure $ (fname_var, args, unCurryTopTy fun_ty, bod')
    _ -> error $ "desugarFun: Found a function with multiple RHS, " ++ prettyPrint decl

multiArgsToOne :: [Var] -> [Ty0] -> Exp0 -> (Var, Exp0)
multiArgsToOne args tys ex =
  let new_arg = toVar "multi_arg"
  in (new_arg, tuplizeRefs new_arg args tys ex)

collectTopTy :: (Show a,  Pretty a) => Decl a -> TopTyEnv -> TopTyEnv
collectTopTy d env =
  case d of
    TypeSig _ names ty ->
      let ty' = desugarTopType ty
      in foldr (\n acc -> M.insert (toVar $ nameToStr n) ty' acc) env names
    _ -> env

collectTopLevel :: (Show a,  Pretty a) => TopTyEnv -> Decl a -> PassM (Maybe TopLevel)
collectTopLevel env decl =
  let toplevel = env in
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> pure Nothing

    DataDecl _ (DataType _) _ctx decl_head cons _deriving_binds -> do
      let (ty_name,  ty_args) = desugarDeclHead decl_head
          cons' = map desugarConstr cons
      if ty_name `S.member` builtinTys
      then error $ sdoc ty_name ++ " is a built-in type."
      else pure $ Just $ HDDef (DDef ty_name ty_args cons')

    -- Reserved for HS.
    PatBind _ (PVar _ (Ident _ "main")) (UnGuardedRhs _ _) _binds ->
      pure Nothing

    PatBind _ (PVar _ (Ident _ "gibbon_main")) (UnGuardedRhs _ rhs) _binds -> do
      rhs' <- fixupSpawn <$> verifyBenchEAssumptions True <$> desugarExp toplevel rhs
      ty <- newMetaTy
      pure $ Just $ HMain $ Just (rhs', ty)

    PatBind _ (PVar _ (Ident _ fn)) (UnGuardedRhs _ rhs) _binds ->
       case M.lookup (toVar fn) env of
         Nothing -> error $ "collectTopLevel: Top-level binding with no type signature: " ++ fn
         Just fun_ty ->
             -- This is a top-level function binding of the form:
             --     f = \x -> ...
             case rhs of
               Lambda _ pats bod -> do
                 bod' <- desugarExp toplevel bod
                 case pats of
                   [] -> error "Impossible"
                   _  -> do
                     args <- mapM (\p -> desugarPatWithTy p >>= pure . fst) pats
                     pure $ Just $ HFunDef (FunDef { funName = toVar fn
                                                   , funArgs = args
                                                   , funTy   = fun_ty
                                                   , funBody = fixupSpawn bod'
                                                   , funRec  = NotRec
                                                   , funInline = NoInline
                                                   })

               -- This is a top-level function that doesn't take any arguments.
               _ -> do
                 rhs' <- desugarExp toplevel rhs
                 let fun_ty'  = ArrowTy [] (tyFromScheme fun_ty)
                     fun_ty'' = ForAll (tyVarsInTy fun_ty') fun_ty'
                 pure $ Just $ HFunDef (FunDef { funName = toVar fn
                                               , funArgs = []
                                               , funTy   = fun_ty''
                                               , funBody = fixupSpawn rhs'
                                               , funRec  = NotRec
                                               , funInline = NoInline
                                               })


    FunBind{} -> do (name,args,ty,bod) <- desugarFun toplevel env decl
                    pure $ Just $ HFunDef (FunDef { funName = name
                                                  , funArgs = args
                                                  , funTy   = ty
                                                  , funBody = fixupSpawn bod
                                                  , funRec  = NotRec
                                                  , funInline = NoInline
                                                  })

    InlineSig _ _ _ qname -> pure $ Just $ HInline (toVar $ qnameToStr qname)

    _ -> error $ "collectTopLevel: Unsupported top-level expression: " ++ show decl


-- pure $ LitE (litToInt lit)
desugarLiteral :: Literal a -> PassM Exp0
desugarLiteral lit =
  case lit of
    (Int _ i _)  -> pure $ LitE (fromIntegral i)
    (Frac _ i _) -> pure $ FloatE (fromRational i)
    _ -> error ("desugarLiteral: Only integer litrals are allowed: " ++ prettyPrint lit)


litToInt :: Literal a -> Int
litToInt (Int _ i _) = (fromIntegral i)
litToInt lit         = error ("litToInt: Not an integer: " ++ prettyPrint lit)

litToString :: Literal a -> String
litToString (String _ a _) = a
litToString lit            = error ("litToString: Expected a String, got: " ++ prettyPrint lit)

qnameToStr :: H.QName a -> String
qnameToStr qname =
  case qname of
    Qual _ mname n -> (mnameToStr mname ++ "." ++ nameToStr n)
    UnQual _ n     -> (nameToStr n)
    Special{}      -> error $ "desugarExp: Special identifiers not supported: " ++ prettyPrint qname

mnameToStr :: ModuleName a -> String
mnameToStr (ModuleName _ s) = s

desugarOp :: QOp a -> (Prim Ty0)
desugarOp qop =
  case qop of
    QVarOp _ (UnQual _ (Symbol _ op)) ->
      case M.lookup op primMap of
        Just pr -> pr
        Nothing -> error $ "desugarExp: Unsupported binary op: " ++ show op
    op -> error $ "desugarExp: Unsupported op: " ++ prettyPrint op

desugarAlt :: (Show a,  Pretty a) => TopTyEnv -> Alt a -> PassM (DataCon, [(Var,Ty0)], Exp0)
desugarAlt toplevel alt =
  case alt of
    Alt _ (PApp _ qname ps) (UnGuardedRhs _ rhs) Nothing -> do
      let conName = qnameToStr qname
      ps' <- mapM (\x -> case x of
                            PVar _ v -> (pure . toVar . nameToStr) v
                            PWildCard _ -> gensym "wildcard_"
                            _        -> error "desugarExp: Non-variable pattern in case.")
                  ps
      rhs' <- desugarExp toplevel rhs
      ps'' <- mapM (\v -> (v,) <$> newMetaTy) ps'
      pure (conName, ps'', rhs')
    Alt _ _ GuardedRhss{} _ -> error "desugarExp: Guarded RHS not supported in case."
    Alt _ _ _ Just{}        -> error "desugarExp: Where clauses not allowed in case."
    Alt _ pat _ _           -> error $ "desugarExp: Unsupported pattern in case: " ++ prettyPrint pat

generateBind :: (Show a,  Pretty a) => TopTyEnv -> TopTyEnv -> Decl a -> Exp0 -> PassM (Exp0)
generateBind toplevel env decl exp2 =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> pure exp2
    PatBind _ _ _ Just{}        -> error "generateBind: where clauses not allowed"
    PatBind _ _ GuardedRhss{} _ -> error "generateBind: Guarded right hand side not supported."
    PatBind _ (PTuple _ Boxed pats) (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp toplevel rhs
      w <- gensym "tup"
      ty' <- newMetaTy
      let tupexp e = LetE (w,[],ty',rhs') e
          binds = reverse $ zip pats [0..]
      prjexp <- generateTupleProjs toplevel env binds (VarE w) exp2
      pure $ tupexp prjexp
    PatBind _ pat (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp toplevel rhs
      w <- case pat of
             PVar _ v    -> pure $ toVar (nameToStr v)
             PWildCard _ -> gensym "wildcard_"
             _           -> error "generateBind: "
      ty' <- case M.lookup w env of
                Nothing -> newMetaTy
                Just (ForAll _ ty) -> pure ty
      pure $ LetE (w, [], ty', rhs') exp2
    FunBind{} -> do (name,args,ty,bod) <- desugarFun toplevel env decl
                    pure $ LetE (name,[], tyFromScheme ty, Ext $ LambdaE (zip args (inTys ty)) bod) exp2
    oth -> error ("generateBind: Unsupported pattern: " ++ prettyPrint oth)

generateTupleProjs :: (Show a, Pretty a) => TopTyEnv -> TopTyEnv -> [(Pat a,Int)] -> Exp0 -> Exp0 -> PassM (Exp0)
generateTupleProjs _toplevel _env [] _tup exp2 = pure exp2
generateTupleProjs toplevel env ((p,n):pats) tup exp2 =
    case p of
        (PVar _ v) -> do
            let w = toVar (nameToStr v)
            go w
        (PWildCard _) -> do
            w <- gensym "wildcard"
            go w
        _ -> error $ "generateTupleProjs: Pattern not handled: " ++ prettyPrint p

  where
    go w = do
        ty' <- case M.lookup w env of
                   Nothing -> newMetaTy
                   Just (ForAll _ ty) -> pure ty
        let prjexp = LetE (w,[],ty',ProjE n tup) exp2
        generateTupleProjs toplevel env pats tup prjexp

desugarConstr :: (Show a,  Pretty a) => QualConDecl a -> (DataCon,[(IsBoxed, Ty0)])
desugarConstr qdecl =
  case qdecl of
    QualConDecl _ _tyvars _ctx (ConDecl _ name arg_tys) ->
      -- N.B. This is a type scheme only to make the types work everywhere else
      -- in code. However, we shouldn't actually quantify over any additional
      -- type variables here. We only support Rank-1 types.
      ( nameToStr name , map desugarType' arg_tys )
    _ -> error ("desugarConstr: Unsupported data constructor: " ++ prettyPrint qdecl)

desugarDeclHead :: DeclHead a -> (Var, [TyVar])
desugarDeclHead = go []
  where
    go acc decl_head =
      case decl_head of
        DHead _ name -> (toVar (nameToStr name), acc)
        DHParen _ dh -> go acc dh
        DHApp _ dh tyvar ->
            let (v,acc') = go acc dh
            in (v, acc' ++ [desugarTyVarBind tyvar])
        _ -> error ("collectTopLevel: Unsupported data declaration: " ++ prettyPrint decl_head)

desugarTyVarBind :: TyVarBind a -> TyVar
desugarTyVarBind (UnkindedVar _ name) = UserTv (toVar (nameToStr name))
desugarTyVarBind v@KindedVar{} = error $ "desugarTyVarBind: Vars with kinds not supported yet." ++ prettyPrint v

desugarPatWithTy :: (Show a, Pretty a) => Pat a -> PassM (Var, Ty0)
desugarPatWithTy pat =
  case pat of
    (PParen _ p)        -> desugarPatWithTy p
    (PatTypeSig _ p ty) -> do (v,_ty) <- desugarPatWithTy p
                              pure (v, desugarType ty)
    (PVar _ n)          -> (toVar $ nameToStr n, ) <$> newMetaTy
    (PWildCard _)       -> (\a b -> (a,b)) <$> gensym "wildcard_" <*> newMetaTy
    _ -> error ("desugarPatWithTy: Unsupported pattern: " ++ show pat)

nameToStr :: Name a -> String
nameToStr (Ident _ s)  = s
nameToStr (Symbol _ s) = s

instance Pretty SrcSpanInfo where

-- | SpawnE's are parsed in a strange way. If we see a 'spawn (f x1 x2)',
-- we parse it as 'SpawnE HOLE [] [(f x1 x2)]'. This function patches it
-- to 'SpawnE f [] [x1 x2]'.
fixupSpawn :: Exp0 -> Exp0
fixupSpawn ex =
  case ex of
    Ext (LambdaE vars bod) -> Ext (LambdaE vars (go bod))
    Ext (PolyAppE a b)     -> Ext (PolyAppE (go a) (go b))
    Ext (FunRefE{})        -> ex
    Ext (BenchE fn tyapps args b) -> Ext (BenchE fn tyapps (map go args) b)
    Ext (ParE0 ls) -> Ext (ParE0 (map go ls))
    Ext (L p e)    -> Ext (L p (go e))
    -- Straightforward recursion ...
    VarE{}     -> ex
    LitE{}     -> ex
    FloatE{}   -> ex
    LitSymE{}  -> ex
    AppE fn tyapps args -> AppE fn tyapps (map go args)
    PrimAppE pr args -> PrimAppE pr (map go args)
    DataConE dcon tyapps args -> DataConE dcon tyapps (map go args)
    ProjE i e  -> ProjE i $ go e
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE $ map go ls
    -- Only allow BenchE in tail position
    LetE (v,locs,ty,rhs) bod -> LetE (v,locs,ty, go rhs) (go bod)
    CaseE scrt mp -> CaseE (go scrt) $ map (\(a,b,c) -> (a,b, go c)) mp
    TimeIt e ty b -> TimeIt (go e) ty b
    WithArenaE v e -> WithArenaE v (go e)
    SpawnE _ _ args ->
      case args of
          [(AppE fn tyapps ls)] -> SpawnE fn tyapps ls
          _ -> error $ "fixupSpawn: incorrect use of spawn: " ++ sdoc ex
    SyncE   -> SyncE
    MapE{}  -> error $ "fixupSpawn: TODO MapE"
    FoldE{} -> error $ "fixupSpawn: TODO FoldE"
  where go = fixupSpawn

-- | Verify some assumptions about BenchE.
verifyBenchEAssumptions :: Bool -> Exp0 -> Exp0
verifyBenchEAssumptions bench_allowed ex =
  case ex of
    Ext (LambdaE vars bod) -> Ext (LambdaE vars (not_allowed bod))
    Ext (PolyAppE a b)     -> Ext (PolyAppE (not_allowed a) (not_allowed b))
    Ext (FunRefE{})        -> ex
    Ext (BenchE _ tyapps args b) ->
      if bench_allowed then
        case args of
          ((VarE fn) : oth) -> Ext (BenchE fn tyapps oth b)
          _ -> error $ "desugarModule: bench is a reserved keyword. Usage: bench fn_name args. Got: " ++ sdoc args
      else error $ "verifyBenchEAssumptions: 'bench' can only be used as a tail of the main expression, but it was used in a function. In: " ++ sdoc ex
    Ext (ParE0 ls) -> Ext (ParE0 (map not_allowed ls))
    Ext (L p e)    -> Ext (L p (go e))
    -- Straightforward recursion ...
    VarE{}     -> ex
    LitE{}     -> ex
    FloatE{}   -> ex
    LitSymE{}  -> ex
    AppE fn tyapps args -> AppE fn tyapps (map not_allowed args)
    PrimAppE pr args -> PrimAppE pr (map not_allowed args)
    DataConE dcon tyapps args -> DataConE dcon tyapps (map not_allowed args)
    ProjE i e  -> ProjE i $ not_allowed e
    IfE a b c  -> IfE (not_allowed a) (go b) (go c)
    MkProdE ls -> MkProdE $ map not_allowed ls
    LetE (v,locs,ty,rhs) bod -> LetE (v,locs,ty, not_allowed rhs) (go bod)
    CaseE scrt mp -> CaseE (go scrt) $ map (\(a,b,c) -> (a,b, go c)) mp
    TimeIt e ty b -> TimeIt (not_allowed e) ty b
    WithArenaE v e -> WithArenaE v (go e)
    SpawnE fn tyapps args -> SpawnE fn tyapps (map not_allowed args)
    SyncE    -> SyncE
    MapE{}  -> error $ "verifyBenchEAssumptions: TODO MapE"
    FoldE{} -> error $ "verifyBenchEAssumptions: TODO FoldE"
  where go = verifyBenchEAssumptions bench_allowed
        not_allowed = verifyBenchEAssumptions False
