{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}

module Gibbon.HaskellFrontend
  ( parseFile, primMap, multiArgsToOne, desugarLinearExts ) where

import           Control.Monad
import           Data.Foldable ( foldrM, foldl' )
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
import           System.Process
import           System.Exit
import           System.IO

import           Gibbon.L0.Syntax as L0
import           Gibbon.Common
import           Gibbon.DynFlags

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


parseFile :: Config -> FilePath -> IO (PassM Prog0)
parseFile cfg path = do
    pstate0_ref <- newIORef emptyParseState
    parseFile' cfg pstate0_ref [] path


data ParseState = ParseState
    { imported :: M.Map (String, FilePath) Prog0 }

emptyParseState :: ParseState
emptyParseState = ParseState M.empty

parseMode :: ParseMode
parseMode = defaultParseMode { extensions = [ EnableExtension ScopedTypeVariables
                                            , EnableExtension CPP
                                            , EnableExtension TypeApplications
                                            ]
                                            ++ (extensions defaultParseMode)
                             }

parseFile' :: Config -> IORef ParseState -> [String] -> FilePath -> IO (PassM Prog0)
parseFile' cfg pstate_ref import_route path = do
  when (gopt Opt_GhcTc (dynflags cfg)) $
      typecheckWithGhc cfg path
  str <- readFile path
  let cleaned = removeLinearArrows str
  let parsed = parseModuleWithMode parseMode cleaned
  case parsed of
    ParseOk hs -> desugarModule cfg pstate_ref import_route (takeDirectory path) hs
    ParseFailed loc er -> do
      error ("haskell-src-exts failed: " ++ er ++ ", at " ++ prettyPrint loc)

-- | ASSUMPTION: gibbon-stdlib is available to Cabal.
--
-- Currently 'run_all_tests.sh' installs it with 'cabal v1-install . -w ghc-9.0.1'.
typecheckWithGhc :: Config -> FilePath -> IO ()
typecheckWithGhc cfg path = do
  when (verbosity cfg >= 3) $
    putStr " [compiler] Running pass, GHC typechecker\n   => "
  let cmd = "ghc-9.0.1 -package gibbon-stdlib-0.1 -XNoImplicitPrelude -fno-code " ++ path
  (_, Just hout, Just herr, phandle) <-
        createProcess (shell cmd)
            { std_out = CreatePipe
            , std_err = CreatePipe
            , cwd = Just (takeDirectory path)
            }
  exitCode <- waitForProcess phandle
  case exitCode of
    ExitSuccess -> do
      when (verbosity cfg >= 3) $ do
        out <- hGetContents hout
        err <- hGetContents herr
        putStrLn out
        putStrLn err
      pure ()
    ExitFailure _ -> do
      err <- hGetContents herr
      error err

-- | Really basic, and won't catch every occurence of a linear arrow.
--
-- But its only a stop-gap until we move to ghc-lib-parser, which can parse
-- linear types and other things not supported by haskell-src-exts (e.g. CPP).
removeLinearArrows :: String -> String
removeLinearArrows str =
    fst $
    foldr (\c (acc,saw_one) ->
                if saw_one && c == '%'
                then (acc, False)
                else if saw_one && c /= '%'
                then (c:'1':acc, False)
                else if c == '1'
                then (acc, True)
                else (c:acc, False))
           ([],False)
           str
    {-
     - messup up indendataion and causes compilation errors.
     -
     - unlines .
     - map (unwords .
     -      map (\w -> if w == "%1->" || w == "%1 ->"
     -                 then "->"
     -                 else w) .
     -      words) .
     - lines
     -}

data TopLevel
  = HDDef (DDef Ty0)
  | HFunDef (FunDef Exp0)
  | HMain (Maybe (Exp0, Ty0))
  | HInline Var
  deriving (Show, Eq)

type TopTyEnv = TyEnv TyScheme
type TypeSynEnv = M.Map TyCon Ty0

desugarModule :: (Show a,  Pretty a)
              => Config -> IORef ParseState -> [String] -> FilePath -> Module a -> IO (PassM Prog0)
desugarModule cfg pstate_ref import_route dir (Module _ head_mb _pragmas imports decls) = do
  let type_syns = foldl collectTypeSynonyms M.empty decls
      -- Since top-level functions and their types can't be declared in
      -- single top-level declaration we first collect types and then collect
      -- definitions.
      funtys = foldr (collectTopTy type_syns) M.empty decls
  imported_progs :: [PassM Prog0] <- mapM (processImport cfg pstate_ref (mod_name : import_route) dir) imports
  let prog = do
        toplevels <- catMaybes <$> mapM (collectTopLevel type_syns funtys) decls
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
desugarModule _ _ _ _ m = error $ "desugarModule: " ++ prettyPrint m

stdlibModules :: [String]
stdlibModules = ["Gibbon.Prim", "Gibbon.Prelude", "Gibbon.Vector", "Gibbon.Vector.Parallel", "Gibbon.List"]

processImport :: Config -> IORef ParseState -> [String] -> FilePath -> ImportDecl a -> IO (PassM Prog0)
processImport cfg pstate_ref import_route dir decl@ImportDecl{..}
    -- When compiling with Gibbon, we should *NOT* inline things defined in Gibbon.Prim.
    | mod_name == "Gibbon.Prim" = pure (pure (Prog M.empty M.empty Nothing))
    | otherwise = do
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
                    prog0 <- parseFile' cfg pstate_ref import_route mod_fp
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
    modNameToFilename "Gibbon.List" = "Gibbon" </> "List.hs"
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
    [ "Int", "Float", "Bool", "Sym", "SymHash", "IntHash", "SymSet", "SymDict", "Arena", "Vector" ]

keywords :: S.Set Var
keywords = S.fromList $ map toVar $
    -- These cannot be added to primMap because they all require special handling while parsing.
    --
    [ "quote", "bench", "error", "par", "spawn", "is_big"
    -- operations on vectors
    , "valloc", "vnth", "vlength", "vslice", "inplacevupdate",
      "vsort", "inplacevsort", "vfree", "vfree2"
    -- parallel dictionaries
    , "alloc_pdict", "insert_pdict", "lookup_pdict", "member_pdict", "fork_pdict", "join_pdict"
    -- linked lists
    , "alloc_ll", "is_empty_ll", "cons_ll", "head_ll", "tail_ll", "free_ll", "free2_ll", "copy_ll"
    ] ++ M.keys primMap

desugarTopType :: (Show a,  Pretty a) => TypeSynEnv -> Type a -> TyScheme
desugarTopType type_syns ty =
  case ty of
    -- forall tvs ty.
    TyForall _ mb_tvbind _ ty1 ->
      let tyvars = case mb_tvbind of
                     Just bnds -> map desugarTyVarBind bnds
                     Nothing   -> []
      in ForAll tyvars (desugarType type_syns ty1)
    -- quantify over all tyvars.
    _ -> let ty' = desugarType type_syns ty
             tyvars = tyVarsInTy ty'
        in ForAll tyvars ty'

desugarType :: (Show a,  Pretty a) => TypeSynEnv -> Type a -> Ty0
desugarType type_syns ty =
  case ty of
    H.TyVar _ (Ident _ t) -> L0.TyVar $ UserTv (toVar t)
    TyTuple _ Boxed tys   -> ProdTy (map (desugarType type_syns) tys)
    TyCon _ (Special _ (UnitCon _))     -> ProdTy []
    TyCon _ (UnQual _ (Ident _ "Int"))  -> IntTy
    TyCon _ (UnQual _ (Ident _ "Float"))-> FloatTy
    TyCon _ (UnQual _ (Ident _ "Bool")) -> BoolTy
    TyCon _ (UnQual _ (Ident _ "Sym"))  -> SymTy0
    TyCon _ (UnQual _ (Ident _ "SymSet"))  -> SymSetTy
    TyCon _ (UnQual _ (Ident _ "SymHash"))  -> SymHashTy
    TyCon _ (UnQual _ (Ident _ "IntHash"))  -> IntHashTy
    TyCon _ (UnQual _ (Ident _ con)) ->
      case M.lookup con type_syns of
        Nothing -> PackedTy con []
        Just ty' -> ty'
    TyFun _ t1 t2 -> let t1' = desugarType type_syns t1
                         t2' = desugarType type_syns t2
                     in ArrowTy [t1'] t2'
    TyParen _ ty1 -> desugarType type_syns ty1
    TyApp _ tycon arg ->
      let ty' = desugarType type_syns tycon in
      case ty' of
        PackedTy con tyargs ->
            case (con,tyargs) of
                ("Vector",[]) -> VectorTy (desugarType type_syns arg)
                ("List",[]) -> ListTy (desugarType type_syns arg)
                ("PDict",[]) ->
                  let arg' = desugarType type_syns arg in
                  case arg' of
                    ProdTy [k, v] -> PDictTy k v
                    _ -> error $ "desugarType: Unexpected PDictTy argument: " ++ show arg'
                _ ->
                  case M.lookup con type_syns of
                    Nothing -> PackedTy con (tyargs ++ [desugarType type_syns arg])
                    Just ty'' -> ty''
        _ -> error $ "desugarType: Unexpected type arguments: " ++ show ty'
    _ -> error $ "desugarType: Unsupported type: " ++ show ty


-- Like 'desugarTopType' but understands boxity.
desugarTopType' :: (Show a,  Pretty a) => TypeSynEnv -> Type a -> (IsBoxed, TyScheme)
desugarTopType' type_syns ty =
  case ty of
    -- forall tvs ty.
    TyForall _ mb_tvbind _ ty1 ->
      let tyvars = case mb_tvbind of
                     Just bnds -> map desugarTyVarBind bnds
                     Nothing   -> []
          (boxity, ty') = desugarType' type_syns ty1
      in (boxity, ForAll tyvars ty')
    -- quantify over all tyvars.
    _ -> let (boxity, ty') = desugarType' type_syns ty
             tyvars = tyVarsInTy ty'
        in (boxity, ForAll tyvars ty')

-- Like 'desugarType' but understands boxity.
desugarType' :: (Show a,  Pretty a) => TypeSynEnv -> Type a -> (IsBoxed, Ty0)
desugarType' type_syns ty =
  case ty of
    TyBang _ _ (NoUnpack _) ty1 -> (True, desugarType type_syns ty1)
    _ -> (False, desugarType type_syns ty)

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
  , ("tan", FTanP)
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
  , ("contains_hash", SymHashContains)
  , ("empty_int_hash", IntHashEmpty)
  , ("insert_int_hash", IntHashInsert)
  , ("lookup_int_hash", IntHashLookup)
  ]

desugarExp :: (Show a, Pretty a) => TypeSynEnv -> TopTyEnv -> Exp a -> PassM Exp0
desugarExp type_syns toplevel e =
  case e of
    Paren _ (ExpTypeSig _ (App _ (H.Var _ f) (Lit _ lit)) tyc)
        | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit) (desugarType type_syns tyc)) []
    -- Paren _ (App _ (H.Var _ f) (Lit _ lit))
    --     | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit
    Paren _ e2 -> desugarExp type_syns toplevel e2
    H.Var _ qv -> do
      let str = qnameToStr qv
          v = (toVar str)
      if str == "alloc_pdict"
      then do
        kty  <- newMetaTy
        vty  <- newMetaTy
        pure $ PrimAppE (PDictAllocP kty vty) []
      else if str == "alloc_ll"
      then do
        ty  <- newMetaTy
        pure $ PrimAppE (LLAllocP ty) []
      else if v == "sync"
      then pure SyncE
      else if v == "lsync"
      then pure SyncE
      else if M.member str primMap
      then pure $ PrimAppE (primMap M.! str) []
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
      bod' <- desugarExp type_syns toplevel bod
      (vars,tys,bindss) <- unzip3 <$> mapM (desugarPatWithTy type_syns) pats
      let binds = concat bindss
          args = zip vars tys
      pure $ Ext $ LambdaE args (mkLets binds bod')

    App _ e1 e2 -> do
        desugarExp type_syns toplevel e1 >>= \case
          (VarE f) ->
            case M.lookup (fromVar f) primMap of
              Just p  -> (\e2' -> PrimAppE p [e2']) <$> desugarExp type_syns toplevel e2
              Nothing ->
                  if f == "quote"
                  then case e2 of
                         Lit _ lit -> pure $ LitSymE (toVar $ litToString lit)
                         _ -> error "desugarExp: quote only accepts string literals. E.g quote \"hello\""
                  else if f == "eqBenchProg"
                  then case e2 of
                         Lit _ lit -> pure $ (PrimAppE (EqBenchProgP (litToString lit)) [])
                         _ -> error "desugarExp: eqBenchProg only accepts string literals."
                  else if f == "readArrayFile"
                  then let go e0 = case e0 of
                                    Con _ (UnQual _ (Ident _ "Nothing")) -> do
                                      t <- newMetaTy
                                      pure $ PrimAppE (ReadArrayFile Nothing t) []
                                    App _ (Con _ (UnQual _ (Ident _ "Just"))) (Tuple _ Boxed [Lit _ name, Lit _ len]) -> do
                                      t <- newMetaTy
                                      pure $ PrimAppE (ReadArrayFile (Just (litToString name, litToInt len)) t) []
                                    Paren _ e3 -> go e3
                                    _ -> error $ "desugarExp: couldn't parse readArrayFile; " ++ show e0
                       in go e2
                  else if f == "readPackedFile"
                  then let go e0 = case e0 of
                                     TypeApp _ (TyCon _ (UnQual _ (Ident _ con))) -> do
                                       let ty = PackedTy con []
                                       pure $ PrimAppE (ReadPackedFile Nothing con Nothing ty) []
                                     _ -> error $ "desugarExp: couldn't parse readPackedFile; " ++ show e0
                       in go e2
                  else if f == "writePackedFile"
                  then
                    case e2 of
                      Lit _ fp -> do
                        ty <- newMetaTy
                        pure $ PrimAppE (WritePackedFile (litToString fp) ty) []
                      _ -> error $ "desugarExp: couldn't parse writePackedFile; " ++ show e2
                  else if f == "bench"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ Ext $ BenchE "HOLE" [] [e2'] False
                  else if f == "timeit"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty <- newMetaTy
                    pure $ TimeIt e2' ty False
                  else if f == "iterate"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty <- newMetaTy
                    pure $ TimeIt e2' ty True
                  else if f == "error"
                  then case e2 of
                         Lit _ lit -> pure $ PrimAppE (ErrorP (litToString lit) IntTy) [] -- assume int (!)
                         _ -> error "desugarExp: error expects String literal."
                  else if f == "par"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ Ext $ ParE0 [e2']
                  else if f == "spawn"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ SpawnE "HOLE" [] [e2']
                  else if f == "valloc"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VAllocP ty) [e2']
                  else if f == "vfree"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VFreeP ty) [e2']
                  else if f == "vfree2"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VFree2P ty) [e2']
                  else if f == "vnth"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VNthP ty) [e2']
                  else if f == "vlength"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VLengthP ty) [e2']
                  else if f == "inplacevupdate"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (InplaceVUpdateP ty) [e2']
                  else if f == "vconcat"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VConcatP ty) [e2']
                  else if f == "vsort"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VSortP ty) [e2']
                  else if f == "inplacevsort"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (InplaceVSortP ty) [e2']
                  else if f == "vslice"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VSliceP ty) [e2']

                  else if f == "vmerge"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (VMergeP ty) [e2']
                  else if f == "insert_pdict"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    kty  <- newMetaTy
                    vty  <- newMetaTy
                    pure $ PrimAppE (PDictInsertP kty vty) [e2']

                  else if f == "lookup_pdict"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    kty  <- newMetaTy
                    vty  <- newMetaTy
                    pure $ PrimAppE (PDictLookupP kty vty) [e2']
                  else if f == "member_pdict"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    kty  <- newMetaTy
                    vty  <- newMetaTy
                    pure $ PrimAppE (PDictHasKeyP kty vty) [e2']
                  else if f == "fork_pdict"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    kty  <- newMetaTy
                    vty  <- newMetaTy
                    pure $ PrimAppE (PDictForkP kty vty) [e2']
                  else if f == "join_pdict"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    kty  <- newMetaTy
                    vty  <- newMetaTy
                    pure $ PrimAppE (PDictJoinP kty vty) [e2']
                  else if f == "is_empty_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLIsEmptyP ty) [e2']
                  else if f == "cons_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLConsP ty) [e2']
                  else if f == "head_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLHeadP ty) [e2']
                  else if f == "tail_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLTailP ty) [e2']
                  else if f == "free_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLFreeP ty) [e2']
                  else if f == "free2_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLFree2P ty) [e2']
                  else if f == "copy_ll"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty  <- newMetaTy
                    pure $ PrimAppE (LLCopyP ty) [e2']
                  else if f == "fst"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ ProjE 0 e2'
                  else if f == "snd"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ ProjE 1 e2'
                  else if f == "printPacked"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty <- newMetaTy
                    pure $ Ext (PrintPacked ty e2')
                  else if f == "copyPacked"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty <- newMetaTy
                    pure $ Ext (CopyPacked ty e2')
                  else if f == "travPacked"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    ty <- newMetaTy
                    pure $ Ext (TravPacked ty e2')
                  else if f == "unsafeAlias"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ Ext (LinearExt (AliasE e2'))
                  else if f == "unsafeToLinear"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ Ext (LinearExt (ToLinearE e2'))
                  else if f == "lseq"
                  then do
                    e2' <- desugarExp type_syns toplevel e2
                    pure $ Ext (LinearExt (LseqE e2' undefined))
                  else if S.member f keywords
                  then error $ "desugarExp: Keyword not handled: " ++ sdoc f
                  else AppE f [] <$> (: []) <$> desugarExp type_syns toplevel e2
          (DataConE tyapp c as) -> (\e2' -> DataConE tyapp c (as ++ [e2'])) <$> desugarExp type_syns toplevel e2
          (Ext (ParE0 ls)) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ Ext $ ParE0 (ls ++ [e2'])
          (AppE f [] ls) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ AppE f [] (ls ++ [e2'])

          (Ext (BenchE fn [] ls b)) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ Ext $ BenchE fn [] (ls ++ [e2']) b

          (SpawnE fn [] ls) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ SpawnE fn [] (ls ++ [e2'])

          (PrimAppE (WritePackedFile fp ty) ls) -> do
             e2' <- desugarExp type_syns toplevel e2
             pure $ PrimAppE (WritePackedFile fp ty) (ls ++ [e2'])

          (PrimAppE (ReadPackedFile _mb_fp tycon mb_var ty) []) ->
             let go e0 = case e0 of
                           Con _ (UnQual _ (Ident _ "Nothing")) -> do
                             pure (PrimAppE (ReadPackedFile Nothing tycon mb_var ty) [])
                           App _ (Con _ (UnQual _ (Ident _ "Just"))) (Lit _ name) -> do
                             pure (PrimAppE (ReadPackedFile (Just (litToString name)) tycon mb_var ty) [])
                           Paren _ e3 -> go e3
                           _ -> error $ "desugarExp: couldn't parse readPackedFile; " ++ show e0
             in go e2

          (PrimAppE (VMergeP elty) ls) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ PrimAppE (VMergeP elty) (ls ++ [e2'])
          (PrimAppE p ls) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure $ PrimAppE p (ls ++ [e2'])

          TimeIt{} ->
            error "desugarExp: TimeIt can only accept 1 expression."

          (Ext (LinearExt (LseqE a _))) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure (Ext (LinearExt (LseqE a e2')))

          (Ext (LinearExt (ToLinearE (AppE f [] ls)))) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure (Ext (LinearExt (ToLinearE (AppE f [] (ls ++ [e2'])))))

          (Ext (LinearExt (ToLinearE (DataConE tyapp dcon ls)))) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure (Ext (LinearExt (ToLinearE (DataConE tyapp dcon (ls ++ [e2'])))))

          (Ext (LinearExt (ToLinearE (Ext (LambdaE [(v,ty)] bod))))) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure (Ext (LinearExt (ToLinearE (LetE (v,[],ty,e2') bod))))

          (Ext (LinearExt (ToLinearE (VarE fn)))) -> do
            e2' <- desugarExp type_syns toplevel e2
            pure (Ext (LinearExt (ToLinearE (AppE fn [] [e2']))))

          f -> error ("desugarExp: Couldn't parse function application: (: " ++ show f ++ ")")

    Let _ (BDecls _ decls) rhs -> do
      rhs' <- desugarExp type_syns toplevel rhs
      let funtys = foldr (collectTopTy type_syns) M.empty decls
      foldrM (generateBind type_syns toplevel funtys) rhs' decls

    If _ a b c -> do
      a' <- desugarExp type_syns toplevel a
      b' <- desugarExp type_syns toplevel b
      c' <- desugarExp type_syns toplevel c
      pure $ IfE a' b' c'

    Tuple _ Unboxed _ -> error $ "desugarExp: Only boxed tuples are allowed: " ++ prettyPrint e
    Tuple _ Boxed es  -> MkProdE <$> mapM (desugarExp type_syns toplevel) es

    Case _ scrt alts -> do
      scrt' <- desugarExp type_syns toplevel scrt
      CaseE scrt' <$> mapM (desugarAlt type_syns toplevel) alts

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
      e1' <- desugarExp type_syns toplevel e1
      case e2 of
        Lit _ lit -> do
          let i = litToInt lit
          pure $ ProjE i e1'
        _ -> error $ "desugarExp: !!! expects a integer. Got: " ++ prettyPrint e2

    InfixApp _ e1 op e2 -> do
      e1' <- desugarExp type_syns toplevel e1
      e2' <- desugarExp type_syns toplevel e2
      case op of
        QVarOp _ (UnQual _ (Symbol _ "&")) -> do
          pure $ Ext (LinearExt (ReverseAppE e2' e1'))
        _ -> do
          let op' = desugarOp op
          pure $ PrimAppE op' [e1', e2']

    NegApp _ e1 -> do
      e1' <- desugarExp type_syns toplevel e1
      pure $ PrimAppE SubP [LitE 0, e1']

    _ -> error ("desugarExp: Unsupported expression: " ++ prettyPrint e)

desugarFun :: (Show a,  Pretty a) => TypeSynEnv -> TopTyEnv -> TopTyEnv -> Decl a -> PassM (Var, [Var], TyScheme, Exp0)
desugarFun type_syns toplevel env decl =
  case decl of
    FunBind _ [Match _ fname pats (UnGuardedRhs _ bod) _where] -> do
      let fname_str = nameToStr fname
          fname_var = toVar (fname_str)
      (vars,_tys,bindss) <- unzip3 <$> mapM (desugarPatWithTy type_syns) pats
      let binds = concat bindss
          args = vars
      fun_ty <- case M.lookup fname_var env of
                  Nothing -> do
                     arg_tys <- mapM (\_ -> newMetaTy) args
                     ret_ty  <- newMetaTy
                     let funty = ArrowTy arg_tys ret_ty
                     pure $ (ForAll [] funty)
                  Just ty -> pure ty
      bod' <- desugarExp type_syns toplevel bod
      pure $ (fname_var, args, unCurryTopTy fun_ty, (mkLets binds bod'))
    _ -> error $ "desugarFun: Found a function with multiple RHS, " ++ prettyPrint decl

multiArgsToOne :: [Var] -> [Ty0] -> Exp0 -> (Var, Exp0)
multiArgsToOne args tys ex =
  let new_arg = toVar "multi_arg"
  in (new_arg, tuplizeRefs new_arg args tys ex)

collectTopTy :: (Show a,  Pretty a) => TypeSynEnv -> Decl a -> TopTyEnv -> TopTyEnv
collectTopTy type_syns d env =
  case d of
    TypeSig _ names ty ->
      let ty' = desugarTopType type_syns ty
      in foldr (\name acc ->
                  let tycon_var = toVar (nameToStr name) in
                  case M.lookup tycon_var acc of
                    Nothing ->  M.insert tycon_var ty' acc
                    Just{} -> error $ "collectTopTy: Multiple type signatures for: " ++ show tycon_var)
         env names
    _ -> env

collectTypeSynonyms :: (Show a,  Pretty a) => TypeSynEnv -> Decl a -> TypeSynEnv
collectTypeSynonyms env d =
  case d of
    TypeDecl _ (DHead _ name) ty ->
      let ty' = desugarType env ty
          tycon = nameToStr name
      in case M.lookup tycon env of
           Nothing -> M.insert tycon ty' env
           Just{} -> error $ "collectTypeSynonyms: Multiple type synonym declarations: " ++ show tycon
    _ -> env

collectTopLevel :: (Show a,  Pretty a) => TypeSynEnv -> TopTyEnv -> Decl a -> PassM (Maybe TopLevel)
collectTopLevel type_syns env decl =
  let toplevel = env in
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> pure Nothing

    -- 'collectTypeSynonyms'.
    TypeDecl{} -> pure Nothing

    DataDecl _ (DataType _) _ctx decl_head cons _deriving_binds -> do
      let (ty_name,  ty_args) = desugarDeclHead decl_head
          cons' = map (desugarConstr type_syns) cons
      if ty_name `S.member` builtinTys
      then error $ sdoc ty_name ++ " is a built-in type."
      else pure $ Just $ HDDef (DDef ty_name ty_args cons')

    -- Reserved for HS.
    PatBind _ (PVar _ (Ident _ "main")) (UnGuardedRhs _ _) _binds ->
      pure Nothing

    PatBind _ (PVar _ (Ident _ "gibbon_main")) (UnGuardedRhs _ rhs) _binds -> do
      rhs' <- fixupSpawn <$> verifyBenchEAssumptions True <$> desugarExp type_syns toplevel rhs
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
                 bod' <- desugarExp type_syns toplevel bod
                 case pats of
                   [] -> error "Impossible"
                   _  -> do
                     (vars,_tys,bindss) <- unzip3 <$> mapM (desugarPatWithTy type_syns) pats
                     let binds = concat bindss
                         args = vars
                     pure $ Just $ HFunDef (FunDef { funName = toVar fn
                                                   , funArgs = args
                                                   , funTy   = fun_ty
                                                   , funBody = fixupSpawn (mkLets binds bod')
                                                   , funRec  = NotRec
                                                   , funInline = NoInline
                                                   })

               -- This is a top-level function that doesn't take any arguments.
               _ -> do
                 rhs' <- desugarExp type_syns toplevel rhs
                 let fun_ty'  = ArrowTy [] (tyFromScheme fun_ty)
                     fun_ty'' = ForAll (tyVarsInTy fun_ty') fun_ty'
                 pure $ Just $ HFunDef (FunDef { funName = toVar fn
                                               , funArgs = []
                                               , funTy   = fun_ty''
                                               , funBody = fixupSpawn rhs'
                                               , funRec  = NotRec
                                               , funInline = NoInline
                                               })


    FunBind{} -> do (name,args,ty,bod) <- desugarFun type_syns toplevel env decl
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
    Special{}      -> error $ "qnameToStr: Special identifiers not supported: " ++ prettyPrint qname

mnameToStr :: ModuleName a -> String
mnameToStr (ModuleName _ s) = s

desugarOp :: QOp a -> (Prim Ty0)
desugarOp qop =
  case qop of
    QVarOp _ (UnQual _ (Symbol _ op)) ->
      case M.lookup op primMap of
        Just pr -> pr
        Nothing -> error $ "desugarOp: Unsupported binary op: " ++ show op
    op -> error $ "desugarOp: Unsupported op: " ++ prettyPrint op

desugarAlt :: (Show a,  Pretty a) => TypeSynEnv -> TopTyEnv -> Alt a -> PassM (DataCon, [(Var,Ty0)], Exp0)
desugarAlt type_syns toplevel alt =
  case alt of
    Alt _ (PApp _ qname ps) (UnGuardedRhs _ rhs) Nothing -> do
      let conName = qnameToStr qname
      ps' <- mapM (\x -> case x of
                            PVar _ v -> (pure . toVar . nameToStr) v
                            PWildCard _ -> gensym "wildcard_"
                            _        -> error "desugarExp: Non-variable pattern in case.")
                  ps
      rhs' <- desugarExp type_syns toplevel rhs
      ps'' <- mapM (\v -> (v,) <$> newMetaTy) ps'
      pure (conName, ps'', rhs')
    Alt _ _ GuardedRhss{} _ -> error "desugarExp: Guarded RHS not supported in case."
    Alt _ _ _ Just{}        -> error "desugarExp: Where clauses not allowed in case."
    Alt _ pat _ _           -> error $ "desugarExp: Unsupported pattern in case: " ++ prettyPrint pat

generateBind :: (Show a,  Pretty a) => TypeSynEnv -> TopTyEnv -> TopTyEnv -> Decl a -> Exp0 -> PassM (Exp0)
generateBind type_syns toplevel env decl exp2 =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> pure exp2
    -- 'collectTypeSynonyms' takes care of this.
    TypeDecl{} -> pure exp2
    PatBind _ _ _ Just{}        -> error "generateBind: where clauses not allowed"
    PatBind _ _ GuardedRhss{} _ -> error "generateBind: Guarded right hand side not supported."
    PatBind _ (PTuple _ Boxed pats) (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp type_syns toplevel rhs
      w <- gensym "tup"
      ty' <- newMetaTy
      let tupexp e = LetE (w,[],ty',rhs') e
          binds = reverse $ zip pats [0..]
      prjexp <- generateTupleProjs toplevel env binds (VarE w) exp2
      pure $ tupexp prjexp
    PatBind _ pat (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp type_syns toplevel rhs
      w <- case pat of
             PVar _ v    -> pure $ toVar (nameToStr v)
             PWildCard _ -> gensym "wildcard_"
             _           -> error "generateBind: "
      ty' <- case M.lookup w env of
               Nothing -> newMetaTy
               Just (ForAll _ ty) -> pure ty
      pure $ LetE (w, [], ty', rhs') exp2
    FunBind{} -> do (name,args,ty,bod) <- desugarFun type_syns toplevel env decl
                    pure $ LetE (name,[], tyFromScheme ty, Ext $ LambdaE (zip args (inTys ty)) bod) exp2
    oth -> error ("generateBind: Unsupported pattern: " ++ prettyPrint oth)

generateTupleProjs :: (Show a, Pretty a) => TopTyEnv -> TopTyEnv -> [(Pat a,Int)] -> Exp0 -> Exp0 -> PassM (Exp0)
generateTupleProjs _toplevel _env [] _tup exp2 = pure exp2
generateTupleProjs toplevel env ((p,n):pats) tup exp2 =
    case p of
        (PVar _ v) -> do
            let w = toVar (nameToStr v)
            go w
        -- Don't bind wildcards from patterns.
        (PWildCard _) -> do
          generateTupleProjs toplevel env pats tup exp2

        _ -> error $ "generateTupleProjs: Pattern not handled: " ++ prettyPrint p

  where
    go w = do
        ty' <- case M.lookup w env of
                   Nothing -> newMetaTy
                   Just (ForAll _ ty) -> pure ty
        let prjexp = LetE (w,[],ty',ProjE n tup) exp2
        generateTupleProjs toplevel env pats tup prjexp

desugarConstr :: (Show a,  Pretty a) => TypeSynEnv -> QualConDecl a -> (DataCon,[(IsBoxed, Ty0)])
desugarConstr type_syns qdecl =
  case qdecl of
    QualConDecl _ _tyvars _ctx (ConDecl _ name arg_tys) ->
      -- N.B. This is a type scheme only to make the types work everywhere else
      -- in code. However, we shouldn't actually quantify over any additional
      -- type variables here. We only support Rank-1 types.
      ( nameToStr name , map (desugarType' type_syns) arg_tys )
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

desugarPatWithTy :: (Show a, Pretty a) => TypeSynEnv -> Pat a -> PassM (Var, Ty0, [L0.Binds Exp0])
desugarPatWithTy type_syns pat =
  case pat of
    (PParen _ p)        -> desugarPatWithTy type_syns p
    (PatTypeSig _ p ty) -> do (v,_ty,binds) <- desugarPatWithTy type_syns p
                              pure (v, desugarType type_syns ty, binds)
    (PVar _ n)          -> do ty <- newMetaTy
                              pure (toVar (nameToStr n), ty, [])
    (PWildCard _)       -> do v <- gensym "wildcard_"
                              ty <- newMetaTy
                              pure (v,ty,[])
    (PTuple _ Boxed pats) -> do (vars,tys,bindss) <- unzip3 <$> mapM (desugarPatWithTy type_syns) pats
                                tup <- gensym "tup"
                                let binds0 = concat bindss
                                    binds1 = map (\(v,ty,i) -> (v,[],ty,ProjE i (VarE tup))) (zip3 vars tys [0..])
                                    tupty = ProdTy tys
                                pure (tup,tupty,binds0 ++ binds1)

    (PApp _ (UnQual _ (Ident _ "Ur")) [one]) -> desugarPatWithTy type_syns one

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
    Ext (PrintPacked ty arg) -> Ext (PrintPacked ty (go arg))
    Ext (CopyPacked ty arg) -> Ext (CopyPacked ty (go arg))
    Ext (TravPacked ty arg) -> Ext (TravPacked ty (go arg))
    Ext (L p e)    -> Ext (L p (go e))
    Ext (LinearExt ext) ->
      case ext of
        ReverseAppE fn arg -> Ext (LinearExt (ReverseAppE (go fn) (go arg)))
        LseqE a b   -> Ext (LinearExt (LseqE (go a) (go b)))
        AliasE a    -> Ext (LinearExt (AliasE (go a)))
        ToLinearE a -> Ext (LinearExt (ToLinearE (go a)))
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
    Ext (PrintPacked ty arg) -> Ext (PrintPacked ty (not_allowed arg))
    Ext (CopyPacked ty arg) -> Ext (CopyPacked ty (not_allowed arg))
    Ext (TravPacked ty arg) -> Ext (TravPacked ty (not_allowed arg))
    Ext (L p e)    -> Ext (L p (go e))
    Ext (LinearExt{}) -> error "verifyBenchEAssumptions: LinearExt not handled."
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

--------------------------------------------------------------------------------

desugarLinearExts :: Prog0 -> PassM Prog0
desugarLinearExts (Prog ddefs fundefs main) = do
    main' <- case main of
               Nothing -> pure Nothing
               Just (e,ty) -> do
                 let ty' = goty ty
                 e' <- go e
                 pure $ Just (e', ty')
    fundefs' <- mapM (\fn -> do
                           bod <- go (funBody fn)
                           let (ForAll tyvars ty) = (funTy fn)
                               ty' = goty ty
                           pure $ fn { funBody = bod
                                     , funTy = (ForAll tyvars ty')
                                     })
                     fundefs
    pure (Prog ddefs fundefs' main')
  where
    goty :: Ty0 -> Ty0
    goty ty =
      case ty of
        ProdTy tys -> ProdTy (map goty tys)
        SymDictTy v t -> SymDictTy v (goty t)
        PDictTy k v -> PDictTy (goty k) (goty v)
        ArrowTy tys b  -> ArrowTy (map goty tys) (goty b)
        PackedTy "Ur" [one] -> one
        PackedTy t tys -> PackedTy t (map goty tys)
        VectorTy t -> VectorTy (goty t)
        ListTy t -> ListTy (goty t)
        _ -> ty

    go :: PreExp E0Ext Ty0 Ty0 -> PassM Exp0
    go ex =
      case ex of
        VarE{}    -> pure ex
        LitE{}    -> pure ex
        FloatE{}  -> pure ex
        LitSymE{} -> pure ex
        AppE f tyapps args -> do args' <- mapM go args
                                 pure (AppE f tyapps args')
        PrimAppE pr args   -> do args' <- mapM go args
                                 pure (PrimAppE pr args')
        LetE (v,locs,ty,rhs) bod -> do
          let ty' = goty ty
          rhs' <- go rhs
          bod' <- go bod
          pure $ LetE (v,locs,ty',rhs') bod'
        IfE a b c -> do a' <- go a
                        b' <- go b
                        c' <- go c
                        pure (IfE a' b' c')
        MkProdE ls -> do ls' <- mapM go ls
                         pure (MkProdE ls')
        ProjE i e  -> do e' <- go e
                         pure (ProjE i e')
        CaseE scrt alts -> do scrt' <- go scrt
                              alts' <- mapM (\(a,b,c) -> do c' <- go c
                                                            pure (a,b,c'))
                                            alts
                              pure (CaseE scrt' alts')
        DataConE _ "Ur" [arg]   -> do arg' <- go arg
                                      pure arg'
        DataConE locs dcon args -> do args' <- mapM go args
                                      pure (DataConE locs dcon args')
        TimeIt e ty b -> do e' <- go e
                            let ty' = goty ty
                            pure (TimeIt e' ty' b)
        WithArenaE v e -> do e' <- go e
                             pure (WithArenaE v e')
        SpawnE f tyapps args -> do args' <- mapM go args
                                   pure (SpawnE f tyapps args')
        SyncE -> pure SyncE
        MapE{}  -> error "desugarLinearExts: MapE"
        FoldE{} -> error "desugarLinearExts: FoldE"
        Ext ext ->
          case ext of
            LambdaE args bod -> do bod' <- go bod
                                   let args' = map (\(v,ty) -> (v,goty ty)) args
                                   pure (Ext (LambdaE args' bod'))
            PolyAppE fn arg  -> do fn' <- go fn
                                   arg' <- go arg
                                   pure (Ext (PolyAppE fn' arg'))
            FunRefE{} -> pure ex
            BenchE fn tyapps args b -> do args' <- mapM go args
                                          pure (Ext (BenchE fn tyapps args' b))
            ParE0 ls -> do ls' <- mapM go ls
                           pure (Ext (ParE0 ls'))
            PrintPacked ty arg -> do arg' <- go arg
                                     pure (Ext (PrintPacked ty arg'))
            CopyPacked ty arg -> do arg' <- go arg
                                    pure (Ext (CopyPacked ty arg'))
            TravPacked ty arg -> do arg' <- go arg
                                    pure (Ext (TravPacked ty arg'))
            L p e -> do e' <- go e
                        pure (Ext (L p e'))
            LinearExt lin ->
              case lin of
                ReverseAppE fn (Ext (LinearExt (AliasE e))) -> do
                  fn' <- go fn
                  case fn' of
                    Ext (LambdaE [(v,ProdTy tys)] bod) -> do
                      let ty = head tys
                          bod'' = foldl' (\acc i -> gSubstE (ProjE i (VarE v)) (VarE v) acc) bod [0..(length tys)]
                      pure (LetE (v,[],ty,e) bod'')
                    _ -> error $ "desugarLinearExts: couldn't desugar " ++ sdoc ex
                ReverseAppE fn arg -> do
                  fn'  <- go fn
                  arg' <- go arg
                  case fn' of
                    Ext (LambdaE [(v,ty)] bod) -> do
                      pure (LetE (v,[],ty,arg') bod)
                    _ -> error $ "desugarLinearExts: couldn't desugar " ++ sdoc ex
                LseqE _ b   -> do b' <- go b
                                  pure b'
                AliasE a    -> do v <- gensym "aliased"
                                  ty <- newMetaTy
                                  pure (LetE (v,[],ty,MkProdE [a,a]) (VarE v))
                ToLinearE a -> do a' <- go a
                                  pure a'
