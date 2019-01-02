{-# LANGUAGE LambdaCase #-}

module Gibbon.HaskellFrontend
  ( parseFile ) where

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

parseFile :: FilePath -> IO (Prog0, Int)
parseFile path = do
  let parse_mode = defaultParseMode { extensions =
                                        [EnableExtension ScopedTypeVariables]
                                        ++ (extensions defaultParseMode)}
  fmap (parseModuleWithMode parse_mode) (readFile path) >>= \case
    ParseOk hs -> do
        return ( desugarModule hs, 0 )
    ParseFailed _ er -> do
      error ("haskell-src-exts failed: " ++ er)

data TopLevel
  = HDDef (DDef Ty0)
  | HFunDef (FunDef (L Exp0))
  | HMain (Maybe (L Exp0, Ty0))
  deriving (Show, Read, Eq, Ord)

type TopTyEnv = TyEnv TyScheme

desugarModule :: (Show a,  Pretty a) => Module a -> Prog0
desugarModule (Module _ head_mb _pragmas _imports decls) =
  let -- Since top-level functions and their types can't be declared in
      -- single top-level declaration we first collect types and then collect
      -- definitions.
      funtys = foldr collectTopTy M.empty decls

      toplevels = catMaybes $ map (collectTopLevel funtys) decls
      (defs,_vars,funs,main) = foldr classify init_acc toplevels
  in (Prog defs funs main)
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
desugarModule m = error $ "desugarModule: " ++ prettyPrint m

desugarTopType :: (Show a,  Pretty a) => Type a -> TyScheme
desugarTopType ty =
  let ty' = desugarType ty
      tyvars = tyVarsInType ty'
  in ForAll tyvars ty'

desugarType :: (Show a,  Pretty a) => Type a -> Ty0
desugarType ty =
  case ty of
    H.TyVar _ (Ident _ t) -> L0.TyVar (toVar t)
    TyTuple _ Boxed tys   -> ProdTy (map desugarType tys)
    TyCon _ (UnQual _ (Ident _ "Int"))  -> IntTy
    TyCon _ (UnQual _ (Ident _ "Bool")) -> BoolTy
    TyCon _ (UnQual _ (Ident _ con))    -> PackedTy con []
    TyFun _ t1 t2 -> let t1' = desugarType t1
                         t2' = desugarType t2
                     in ArrowTy t1' t2'
    TyList _ (H.TyVar _ (Ident _ con))  -> ListTy (L0.TyVar (toVar con))
    TyParen _ ty1 -> desugarType ty1
    TyApp _ tycon arg ->
      case desugarType tycon of
        PackedTy con tyargs -> PackedTy con (tyargs ++ [desugarType arg])
        _ -> error $ "desugarType: Unexpected type arguments: " ++ prettyPrint ty

    _ -> error $ "desugarType: Unsupported type: " ++ prettyPrint ty

-- Like 'desugarTopType' but understands boxity.
desugarTopType' :: (Show a,  Pretty a) => Type a -> (IsBoxed, TyScheme)
desugarTopType' ty =
  let (boxity, ty') = desugarType' ty
      tyvars = tyVarsInType ty'
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
    ArrowTy{} -> let (a,b) = go [] ty1
                 in ArrowTy (ProdTy a) b
    _ -> ty1
  where
    go :: [Ty0] -> Ty0 -> ([Ty0], Ty0)
    go acc ty =
      case ty of
        ArrowTy a b -> (go (acc++[a]) b)
        _ -> (acc,ty)

-- ^ A map between SExp-frontend prefix function names, and Gibbon
-- abstract Primops.
primMap :: M.Map String (Prim Ty0)
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
  , ("||" , OrP)
  , ("&&", AndP)
  , ("^", ExpP)
  , ("eqsym", EqSymP)
  , ("mod", ModP)
  , ("rand", RandP)
  , ("sizeParam", SizeParam)
  , ("symAppend", SymAppend)
  , ("True", MkTrue)
  , ("False", MkFalse)
  ]

desugarExp :: (Show a, Pretty a) => Exp a -> L Exp0
desugarExp e = L NoLoc $
  case e of
    Paren _ e2 -> Loc.unLoc (desugarExp e2)
    H.Var _ qv -> VarE (toVar $ qnameToStr qv)

    Lit _ lit  -> LitE (litToInt lit)

    Lambda _ [pat] bod ->
      Ext $ LambdaE (desugarPatWithTy pat) (desugarExp bod)

    Lambda _ pats bod ->
      let (args, tys) = unzip $ map desugarPatWithTy pats
          (lam_arg, bod') = multiArgsToOne args tys (desugarExp bod)
      in Ext $ LambdaE (lam_arg, ProdTy tys) bod'

    App _ e1 e2 ->
        case desugarExp e1 of
          L _ (VarE f) ->
            case M.lookup (fromVar f) primMap of
              Just p  -> PrimAppE p [desugarExp e2]
              Nothing -> AppE f [] (desugarExp e2)
          L _ (DataConE tyapp c as) ->
            case M.lookup c primMap of
              Just p  -> PrimAppE p as
              Nothing -> DataConE tyapp c (as ++ [desugarExp e2])
          L _ (AppE f [] lit) ->
            let e2' = desugarExp e2
            in (AppE f [] (L NoLoc $ MkProdE [lit,e2']))
          L _ (PrimAppE p lit) ->
            let e2' = desugarExp e2
            in (PrimAppE p (lit ++ [e2']))
          f -> error ("desugarExp: Only variables allowed in operator position in function applications. (found: " ++ show f ++ ")")

    Let _ (BDecls _ decls) rhs ->
      let rhs' = desugarExp rhs
          funtys = foldr collectTopTy M.empty decls
      in Loc.unLoc $ foldr (generateBind funtys) rhs' decls

    If _ a b c ->
      let a' = desugarExp a
          b' = desugarExp b
          c' = desugarExp c
      in IfE a' b' c'

    Tuple _ Unboxed _ -> error $ "desugarExp: Only boxed tuples are allowed: " ++ prettyPrint e
    Tuple _ Boxed es  -> MkProdE (map desugarExp es)

    Case _ scrt alts ->
        let scrt' = desugarExp scrt
        in CaseE scrt' (map desugarAlt alts)

    Con _ qname ->
      let dcon = qnameToStr qname
      in case M.lookup dcon primMap of
           Just p  -> PrimAppE p []
           -- Just a placeholder for now.
           Nothing -> DataConE (L0.TyVar "blah") dcon []

    -- TODO: timeit: parsing it's type isn't straightforward.

    InfixApp _ e1 (QVarOp _ (UnQual _ (Symbol _ ".||."))) e2 ->
      ParE (desugarExp e1) (desugarExp e2)

    InfixApp _ e1 op e2 ->
      let e1' = desugarExp e1
          e2' = desugarExp e2
          op' = desugarOp  op
      in (PrimAppE op' [e1', e2'])

    _ -> error ("desugarExp: Unsupported expression: " ++ prettyPrint e)

desugarFun :: (Show a,  Pretty a) => TopTyEnv -> Decl a -> (Var, Var, TyScheme, L Exp0)
desugarFun env decl =
  case decl of
    FunBind _ [Match _ fname pats (UnGuardedRhs _ bod) _where] ->
      let fname_str = nameToStr fname
          fname_var = toVar (fname_str)

      in case M.lookup fname_var env of
           Nothing -> error $ "desugarFun: Top-level function with no type signature: " ++ fname_str
           Just fun_ty ->
             let bod' = desugarExp bod
                 (arg,ty,bod'') =
                   case pats of
                     []  -> (toVar "_", fun_ty, bod')
                     [a] -> (desugarPat a, fun_ty, bod')
                     -- Here we directly desugar multiple arguments
                     -- into a tuple argument.
                     -- N.B. this prevents curried functions.
                     _ -> let fun_ty' = unCurryTopTy fun_ty
                              ProdTy tys = inTy fun_ty'
                              args = map desugarPat pats
                              (new_arg, bod''') = multiArgsToOne args tys bod'
                          in (new_arg, fun_ty', bod''')
             in (fname_var, arg, ty, bod'')
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

collectTopLevel :: (Show a,  Pretty a) => TopTyEnv -> Decl a -> Maybe TopLevel
collectTopLevel env decl =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> Nothing

    DataDecl _ (DataType _) _ctx decl_head cons _deriving_binds ->
      let (ty_name,  ty_args) = desugarDeclHead decl_head
          cons' = map desugarConstr cons
      in Just $ HDDef (DDef ty_name ty_args cons')

    PatBind _ (PVar _ (Ident _ "main")) (UnGuardedRhs _ rhs) _binds ->
      -- Start with a void type. The typechecker will fix it.
      Just $ HMain $ Just (desugarExp rhs, L0.TyVar "a")

    PatBind _ (PVar _ (Ident _ fn)) (UnGuardedRhs _ rhs) _binds ->
       case M.lookup (toVar fn) env of
         Nothing -> error $ "collectTopLevel: Top-level binding with no type signature: " ++ fn
         Just fun_ty ->
             -- This is a function binding of the form:
             --     f = \x -> ...
             case rhs of
               Lambda _ pats bod ->
                 let bod' = desugarExp bod
                     (fun_ty'', new_arg, bod'') =
                       case pats of
                         [] -> error ""
                         [pat] -> (fun_ty, desugarPat pat, bod')
                         _ -> let fun_ty' = unCurryTopTy fun_ty
                                  ProdTy tys = inTy fun_ty'
                                  args = map desugarPat pats
                                  (a,b) = multiArgsToOne args tys bod'
                              in (fun_ty, a, b)
                 in  Just $ HFunDef (FunDef { funName = toVar fn
                                            , funArg  = new_arg
                                            , funTy   = fun_ty''
                                            , funBody = bod'' })
               oth -> error $ "collectTopLevel: Unsupprted top-level expression: " ++ prettyPrint oth

    FunBind{} -> let (name,arg,ty,bod) = desugarFun env decl
                 in Just $ HFunDef (FunDef { funName = name
                                           , funArg  = arg
                                           , funTy   = ty
                                           , funBody = bod })

    _ -> error $ "collectTopLevel: Unsupported top-level expression: " ++ prettyPrint decl

litToInt :: Literal a -> Int
litToInt (Int _ i _) = (fromIntegral i) -- lossy conversion here
litToInt lit         = error ("desugarExp: Literal not supported: " ++ prettyPrint lit)

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

desugarAlt :: (Show a,  Pretty a) => Alt a -> (DataCon, [(Var,Ty0)], L Exp0)
desugarAlt alt =
  case alt of
    Alt _ (PApp _ qname ps) (UnGuardedRhs _ rhs) Nothing ->
      let conName = qnameToStr qname
          ps' = map (\x -> case x of
                             PVar _ v -> (toVar . nameToStr) v
                             _        -> error "desugarExp: Non-variable pattern in case.")
                    ps
          rhs' = desugarExp rhs
      in (conName, [(v,(L0.TyVar "blah")) | v <- ps'], rhs')
    Alt _ _ GuardedRhss{} _ -> error "desugarExp: Guarded RHS not supported in case."
    Alt _ _ _ Just{}        -> error "desugarExp: Where clauses not allowed in case."
    Alt _ pat _ _           -> error $ "desugarExp: Unsupported pattern in case: " ++ prettyPrint pat

generateBind :: (Show a,  Pretty a) => TopTyEnv -> Decl a -> L Exp0 -> L Exp0
generateBind env decl exp2 =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> exp2
    PatBind _ _ _ Just{}        -> error "desugarExp: where clauses not allowed"
    PatBind _ _ GuardedRhss{} _ -> error "desugarExp: Guarded right hand side not supported."
    PatBind _ (PVar _ v) (UnGuardedRhs _ rhs) Nothing ->
      let rhs' = desugarExp rhs
          w = toVar (nameToStr v)
      in case M.lookup w env of
           Nothing -> error $ "desugarExp: Missing type signature for a let bound variable: " ++ nameToStr v
           Just (ForAll _ ty) -> l$ LetE (w, [], ty, rhs') exp2
    PatBind _ not_var _ _ -> error $ "desugarExp: Only variable bindings are allowed in let."
                                     ++ "(found: "++ prettyPrint not_var ++ ")"
    FunBind{} -> let (name,arg,ty,bod) = desugarFun env decl
                 in l$ LetE (name,[], tyFromScheme ty, l$ Ext $ LambdaE (arg, inTy ty) bod) exp2
    oth -> error ("desugarExp: Unsupported pattern: " ++ prettyPrint oth)


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
desugarTyVarBind (UnkindedVar _ name) = toVar (nameToStr name)
desugarTyVarBind v@KindedVar{} = error $ "desugarTyVarBind: Vars with kinds not supported yet." ++ prettyPrint v

desugarPat :: Pat a -> Var
desugarPat (PVar _ n) = toVar (nameToStr n)
desugarPat pat        = error ("desugarPat: Unsupported pattern: " ++ prettyPrint pat)

desugarPatWithTy :: (Show a, Pretty a) => Pat a -> (Var, Ty0)
desugarPatWithTy (PParen _ (PatTypeSig _ pat ty)) = (desugarPat pat, desugarType ty)
desugarPatWithTy pat = error ("desugarPatWithTy: Unsupported pattern: " ++ show pat)

nameToStr :: Name a -> String
nameToStr (Ident _ s)  = s
nameToStr (Symbol _ s) = s

instance Pretty SrcSpanInfo where
