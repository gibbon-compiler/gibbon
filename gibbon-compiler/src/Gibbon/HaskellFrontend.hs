{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Gibbon.HaskellFrontend
  ( parseFile, primMap, multiArgsToOne ) where

import           Data.Foldable ( foldrM )
import           Data.Loc as Loc
import           Data.Maybe (catMaybes)
import qualified Data.Map as M
import           Language.Haskell.Exts.Extension
import           Language.Haskell.Exts.Parser
import           Language.Haskell.Exts.Syntax as H
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Exts.SrcLoc

import           Gibbon.L0.Syntax as L0
import           Gibbon.Common

--------------------------------------------------------------------------------

parseFile :: FilePath -> IO (PassM Prog0)
parseFile path = do
  let parse_mode = defaultParseMode { extensions =
                                        [EnableExtension ScopedTypeVariables]
                                        ++ (extensions defaultParseMode)}
  parsed <- parseModuleWithMode parse_mode <$> (readFile path)
  case parsed of
    ParseOk hs -> pure $ desugarModule hs
    ParseFailed _ er -> do
      error ("haskell-src-exts failed: " ++ er)

data TopLevel
  = HDDef (DDef Ty0)
  | HFunDef (FunDef (L Exp0))
  | HMain (Maybe (L Exp0, Ty0))
  | HAnnotation (Var, [Int])
  deriving (Show, Eq)

type TopTyEnv = TyEnv TyScheme

desugarModule :: (Show a,  Pretty a) => Module a -> PassM Prog0
desugarModule (Module _ head_mb _pragmas _imports decls) = do
  let -- Since top-level functions and their types can't be declared in
      -- single top-level declaration we first collect types and then collect
      -- definitions.
      funtys = foldr collectTopTy M.empty decls

  toplevels <- catMaybes <$> mapM (collectTopLevel funtys) decls
  let (defs,_vars,funs,main) = foldr classify init_acc toplevels
  pure (Prog defs funs main)
  where
    init_acc = (M.empty, M.empty, M.empty, Nothing)
    mod_name = moduleName head_mb

    moduleName :: Maybe (ModuleHead a) -> String
    moduleName Nothing = "Module404"
    moduleName (Just (ModuleHead _ mod_name1 _warnings _exports)) =
      let (ModuleName _ name) = mod_name1 in name

    classify thing (defs,vars,funs,main) =
      case thing of
        HDDef d   -> (M.insert (tyName d) d defs, vars, funs, main)
        -- HVDef v   -> (defs, M.insert (vName v) v vars, funs, main)
        HFunDef f -> (defs, vars, M.insert (funName f) f funs, main)
        HMain m ->
          case main of
            Nothing -> (defs, vars, funs, m)
            Just _  -> error $ "A module cannot have two main expressions."
                               ++ show mod_name
        HAnnotation _a -> (defs, vars, funs, main)
desugarModule m = error $ "desugarModule: " ++ prettyPrint m

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
    TyCon _ (UnQual _ (Ident _ "Int"))  -> IntTy
    TyCon _ (UnQual _ (Ident _ "Bool")) -> BoolTy
    TyCon _ (UnQual _ (Ident _ "Sym"))  -> SymTy0
    TyCon _ (UnQual _ (Ident _ con))    -> PackedTy con []
    TyFun _ t1 t2 -> let t1' = desugarType t1
                         t2' = desugarType t2
                     in ArrowTy [t1'] t2'
    TyList _ (H.TyVar _ (Ident _ con))  -> ListTy (L0.TyVar $ UserTv (toVar con))
    TyParen _ ty1 -> desugarType ty1
    TyApp _ tycon arg ->
      case desugarType tycon of
        PackedTy con tyargs -> PackedTy con (tyargs ++ [desugarType arg])
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
  , ("==", EqIntP)
  , ("<", LtP)
  , (">", GtP)
  , ("<=", LtEqP)
  , (">=", GtEqP)
  , ("^", ExpP)
  , ("mod", ModP)
  , ("||" , OrP)
  , ("&&", AndP)
  , ("eqsym", EqSymP)
  , ("rand", RandP)
  , ("sizeParam", SizeParam)
  , ("symAppend", SymAppend)
  , ("True", MkTrue)
  , ("False", MkFalse)
  , ("gensym", Gensym)
  ]

desugarExp :: (Show a, Pretty a) => TopTyEnv -> Exp a -> PassM (L Exp0)
desugarExp toplevel e = L NoLoc <$>
  case e of
    Paren _ (ExpTypeSig _ (App _ (H.Var _ f) (Lit _ lit)) tyc)
        | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit) (desugarType tyc)) []
    -- Paren _ (App _ (H.Var _ f) (Lit _ lit))
    --     | (qnameToStr f) == "error" -> pure $ PrimAppE (ErrorP (litToString lit
    Paren _ e2 -> Loc.unLoc <$> desugarExp toplevel e2
    H.Var _ qv -> do
      let v = (toVar $ qnameToStr qv)
      if v == "gensym"
      then pure $ PrimAppE Gensym []
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
    Lit _ lit  -> pure $ LitE (litToInt lit)

    Lambda _ pats bod -> do
      bod' <- desugarExp toplevel bod
      args <- mapM desugarPatWithTy pats
      pure $ Ext $ LambdaE args bod'

    App _ e1 e2 -> do
        desugarExp toplevel e1 >>= \case
          L _ (VarE f) ->
            case M.lookup (fromVar f) primMap of
              Just p  -> (\e2' -> PrimAppE p [e2']) <$> desugarExp toplevel e2
              Nothing ->
                  if f == "quote"
                  then case e2 of
                         Lit _ lit -> pure $ LitSymE (toVar $ litToString lit)
                         _ -> error "desugarExp: quote only works with String literals. E.g quote \"hello\""
                  else if f == "bench"
                       then do
                         e2' <- desugarExp toplevel e2
                         pure $ Ext $ BenchE "HOLE" [] [e2'] False
                       else if f == "error"
                            then case e2 of
                                   Lit _ lit -> pure $ PrimAppE (ErrorP (litToString lit) IntTy) [] -- assume int (!)
                                   _ -> error "desugarExp: error expects String literal."
                            else AppE f [] <$> (: []) <$> desugarExp toplevel e2
          L _ (DataConE tyapp c as) ->
            case M.lookup c primMap of
              Just p  -> pure $ PrimAppE p as
              Nothing ->
                  if c == "quote"
                  then case e2 of
                         Lit _ lit -> pure $ LitSymE (toVar $ litToString lit)
                         _ -> error "desugarExp: quote only works with String literals. E.g quote \"hello\""
                  else (\e2' -> DataConE tyapp c (as ++ [e2'])) <$> desugarExp toplevel e2
          L _ (AppE f [] ls) -> do
            e2' <- desugarExp toplevel e2
            pure $ AppE f [] (ls ++ [e2'])

          L _ (Ext (BenchE fn [] ls b)) -> do
            e2' <- desugarExp toplevel e2
            pure $ Ext $ BenchE fn [] (ls ++ [e2']) b

          L _ (PrimAppE p ls) -> do
            e2' <- desugarExp toplevel e2
            pure $ PrimAppE p (ls ++ [e2'])

          f -> error ("desugarExp: Couldn't parse function application: (: " ++ show f ++ ")")

    Let _ (BDecls _ decls) rhs -> do
      rhs' <- desugarExp toplevel rhs
      let funtys = foldr collectTopTy M.empty decls
      Loc.unLoc <$> foldrM (generateBind toplevel funtys) rhs' decls

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

    Con _ qname -> do
      let dcon = qnameToStr qname
      case M.lookup dcon primMap of
        Just p  -> pure $ PrimAppE p []
        Nothing -> do
          -- Just a placeholder for now, the typechecker will fill this hole.
          ty <- newMetaTy
          pure $ DataConE ty dcon []

    -- TODO: timeit: parsing it's type isn't straightforward.

    InfixApp _ e1 (QVarOp _ (UnQual _ (Symbol _ ".||."))) e2 ->
      ParE <$> desugarExp toplevel e1 <*> desugarExp toplevel e2

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
      pure $ PrimAppE SubP [l$ LitE 0, e1']

    _ -> error ("desugarExp: Unsupported expression: " ++ prettyPrint e)

desugarFun :: (Show a,  Pretty a) => TopTyEnv -> TopTyEnv -> Decl a -> PassM (Var, [Var], TyScheme, L Exp0)
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

multiArgsToOne :: [Var] -> [Ty0] -> L Exp0 -> (Var, L Exp0)
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
      pure $ Just $ HDDef (DDef ty_name ty_args cons')

    -- Reserved for HS.
    PatBind _ (PVar _ (Ident _ "main")) (UnGuardedRhs _ _) _binds ->
      pure Nothing

    PatBind _ (PVar _ (Ident _ "gibbon_main")) (UnGuardedRhs _ rhs) _binds -> do
      rhs' <- verifyBenchEAssumptions True <$> desugarExp toplevel rhs
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
                                                   , funBody = bod' })

               -- This is a top-level function that doesn't take any arguments.
               _ -> do
                 rhs' <- desugarExp toplevel rhs
                 let fun_ty'  = ArrowTy [] (tyFromScheme fun_ty)
                     fun_ty'' = ForAll (tyVarsInTy fun_ty') fun_ty'
                 pure $ Just $ HFunDef (FunDef { funName = toVar fn
                                               , funArgs = []
                                               , funTy   = fun_ty''
                                               , funBody = rhs' })


    FunBind{} -> do (name,args,ty,bod) <- desugarFun toplevel env decl
                    pure $ Just $ HFunDef (FunDef { funName = name
                                                  , funArgs = args
                                                  , funTy   = ty
                                                  , funBody = bod })

    AnnPragma _ a -> do
      case a of
        Ann _ (Ident _ fn_name) (Tuple _ Boxed [H.Var _ (UnQual _ (Ident _ "gibbon_payload")), List _ ps]) -> do
          let payloads = foldr (\e acc -> case e of
                                            Lit _ lit -> litToInt lit : acc
                                            _ -> acc)
                               []
                               ps
          pure $ Just $ HAnnotation (toVar fn_name, payloads)
        _ -> pure Nothing
    _ -> error $ "collectTopLevel: Unsupported top-level expression: " ++ show decl

litToInt :: Literal a -> Int
litToInt (Int _ i _) = (fromIntegral i) -- lossy conversion here
litToInt lit         = error ("desugarExp: Only integer litrals are allowed: " ++ prettyPrint lit)

litToString :: Literal a -> String
litToString (String _ a _) = a
litToString lit            = error ("desugarExp: Expected a String, got: " ++ prettyPrint lit)

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

desugarAlt :: (Show a,  Pretty a) => TopTyEnv -> Alt a -> PassM (DataCon, [(Var,Ty0)], L Exp0)
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

generateBind :: (Show a,  Pretty a) => TopTyEnv -> TopTyEnv -> Decl a -> L Exp0 -> PassM (L Exp0)
generateBind toplevel env decl exp2 =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> pure exp2
    PatBind _ _ _ Just{}        -> error "desugarExp: where clauses not allowed"
    PatBind _ _ GuardedRhss{} _ -> error "desugarExp: Guarded right hand side not supported."
    PatBind _ (PVar _ v) (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp toplevel rhs
      let w = toVar (nameToStr v)
      ty' <- case M.lookup w env of
                Nothing -> newMetaTy
                Just (ForAll _ ty) -> pure ty
      pure $ l$ LetE (w, [], ty', rhs') exp2
    PatBind _ (PTuple _ Boxed pats) (UnGuardedRhs _ rhs) Nothing -> do
      rhs' <- desugarExp toplevel rhs
      w <- gensym "tup"
      ty' <- newMetaTy
      let tupexp e = l$ LetE (w,[],ty',rhs') e
      prjexp <- generateTupleProjs toplevel env (zip pats [0..]) (l$ VarE w) exp2
      pure $ tupexp prjexp
    FunBind{} -> do (name,args,ty,bod) <- desugarFun toplevel env decl
                    pure $ l$ LetE (name,[], tyFromScheme ty, l$ Ext $ LambdaE (zip args (inTys ty)) bod) exp2
    oth -> error ("desugarExp: Unsupported pattern: " ++ prettyPrint oth)

generateTupleProjs :: (Show a, Pretty a) => TopTyEnv -> TopTyEnv -> [(Pat a,Int)] -> L Exp0 -> L Exp0 -> PassM (L Exp0)
generateTupleProjs toplevel env ((PVar _ v,n):pats) tup exp2 = do
    let w = toVar (nameToStr v)
    ty' <- case M.lookup w env of
             Nothing -> newMetaTy
             Just (ForAll _ ty) -> pure ty
    let prjexp = l$ LetE (w,[],ty',l$ ProjE n tup) exp2
    generateTupleProjs toplevel env pats tup prjexp
generateTupleProjs _toplevel _env [] _tup exp2 =
    pure exp2
generateTupleProjs _ _ _ _ _ = error "generateTupleProjs: Pattern not handled."

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

-- | Verify some assumptions about BenchE.
verifyBenchEAssumptions :: Bool -> L Exp0 -> L Exp0
verifyBenchEAssumptions bench_allowed (L p ex) = L p $
  case ex of
    Ext (LambdaE vars bod) -> Ext (LambdaE vars (not_allowed bod))
    Ext (PolyAppE a b)     -> Ext (PolyAppE (not_allowed a) (not_allowed b))
    Ext (FunRefE{})        -> ex
    Ext (BenchE _ tyapps args b) ->
      if bench_allowed then
        case args of
          (L _ (VarE fn) : oth) -> Ext (BenchE fn tyapps oth b)
          _ -> error $ "desugarModule: bench is a reserved keyword. Usage: bench fn_name args. Got: " ++ sdoc args
      else error $ "verifyBenchEAssumptions: 'bench' can only be used as a tail of the main expression, but it was used in a function. In: " ++ sdoc ex
    -- Straightforward recursion ...
    VarE{}     -> ex
    LitE{}     -> ex
    LitSymE{}  -> ex
    AppE fn tyapps args -> AppE fn tyapps (map not_allowed args)
    PrimAppE pr args -> PrimAppE pr (map not_allowed args)
    DataConE dcon tyapps args -> DataConE dcon tyapps (map not_allowed args)
    ProjE i e  -> ProjE i $ not_allowed e
    IfE a b c  -> IfE (not_allowed a) (go b) (go c)
    MkProdE ls -> MkProdE $ map not_allowed ls
    -- Only allow BenchE in tail position
    LetE (v,locs,ty,rhs) bod -> LetE (v,locs,ty, not_allowed rhs) (go bod)
    CaseE scrt mp -> CaseE (go scrt) $ map (\(a,b,c) -> (a,b, go c)) mp
    TimeIt e ty b -> TimeIt (not_allowed e) ty b
    ParE{} -> error "verifyBenchEAssumptions: TODO ParE"
    WithArenaE v e -> WithArenaE v (go e)
    MapE{}  -> error $ "verifyBenchEAssumptions: TODO MapE"
    FoldE{} -> error $ "verifyBenchEAssumptions: TODO FoldE"
  where go = verifyBenchEAssumptions bench_allowed
        not_allowed = verifyBenchEAssumptions False
