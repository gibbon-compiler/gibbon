{-# LANGUAGE LambdaCase           #-}

module Gibbon.HaskellFrontend
  ( parseFile ) where

import           Data.Loc
import           Data.Maybe (catMaybes)
import qualified Data.Map as M
import           Language.Haskell.Exts.Parser
import           Language.Haskell.Exts.Syntax as H

import           Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax ( PreExp(..), Prim(..),  tuplizeRefs )
import           Gibbon.Common


data TopLevel
  = HDDef (PDDef Ty0)
  | HFunDef (PFDef Ty0 (L Exp0))
  | HMain (Maybe (L Exp0))
  deriving (Show, Read, Eq, Ord)

type TyEnv0 = TyEnv (Scheme Ty0)

desugarModule :: (Show a) => Module a -> L0.PProg
desugarModule (Module _ head_mb _pragmas _imports decls) =
  let -- Since top-level functions and their types can't be declared in
      -- single top-level declaration we first collect types and then collect
      -- definitions.
      funtys = foldr collectTopTy M.empty decls

      toplevels = catMaybes $ map (collectTopLevel funtys) decls
      (defs,funs,main) = foldr classify init_acc toplevels
  in (PProg defs funs M.empty main)
  where
    init_acc = (M.empty, M.empty, Nothing)
    mod_name = moduleName head_mb

    moduleName :: Maybe (ModuleHead a) -> String
    moduleName Nothing = "Module404"
    moduleName (Just (ModuleHead _ mod_name1 _warnings _exports)) =
      let (ModuleName _ name) = mod_name1 in name

    classify thing (defs,funs,main) =
      case thing of
        HDDef d   -> (M.insert (dName d) d defs, funs, main)
        HFunDef f -> (defs, M.insert (fName f) f funs, main)
        HMain e ->
          case main of
            Nothing -> (defs, funs, e)
            Just _  -> error $ "A module cannot have two main expressions."
                               ++ show mod_name
desugarModule m = error $ "desugarModule: " ++ show m

desugarTopType :: (Show a) => Type a -> Scheme Ty0
desugarTopType ty =
  let ty' = desugarType ty
      tyvars = tyVarsInType ty'
  in ForAll tyvars ty'

desugarType :: (Show a) => Type a -> Ty0
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
    _ -> error $ "desugarType: Unsupported type: " ++ show ty

-- Like 'desugarTopType' but understands boxity.
desugarTopType' :: (Show a) => Type a -> (IsBoxed, Scheme Ty0)
desugarTopType' ty =
  let (boxity, ty') = desugarType' ty
      tyvars = tyVarsInType ty'
  in (boxity, ForAll tyvars ty')

-- Like 'desugarType' but understands boxity.
desugarType' :: (Show a) => Type a -> (IsBoxed, Ty0)
desugarType' ty =
  case ty of
    TyBang _ _ (NoUnpack _) (TyCon _ (UnQual _ (Ident _ con))) ->
      case con of
        "Int"  -> (True, IntTy)
        "Bool" -> (True, BoolTy)
        _      -> (True, PackedTy con [])
    _ -> (False, desugarType ty)

-- | A Haskell type of the form (a -> b -> c) gets desugared to nested 'ArrowTy's.
-- Convert all the input types to a tuple to match L0.
unCurryTopTy :: Scheme Ty0 -> Scheme Ty0
unCurryTopTy ty = ty

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

desugarExp :: Show a => Exp a -> L Exp0
desugarExp e = L NoLoc $
  case e of
    Paren _ e2 -> unLoc (desugarExp e2)
    H.Var _ qv -> VarE (toVar $ qnameToStr qv)

    Lit _ lit  -> LitE (litToInt lit)

    App _ e1 e2 ->
        case desugarExp e1 of
          L _ (VarE f) ->
            case M.lookup (fromVar f) primMap of
              Just p  -> PrimAppE p [desugarExp e2]
              Nothing -> AppE f [] (desugarExp e2)
          L _ (DataConE () c as) ->
            let e2' = desugarExp e2
            in (DataConE () c (as ++ [e2']))
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
      in unLoc $ foldr (generateBind funtys) rhs' decls

    If _ a b c ->
      let a' = desugarExp a
          b' = desugarExp b
          c' = desugarExp c
      in IfE a' b' c'

    Tuple _ Unboxed _ -> error $ "desugarExp: Only boxed tuples are allowed: " ++ show e
    Tuple _ Boxed es  -> MkProdE (map desugarExp es)

    Case _ scrt alts ->
        let scrt' = desugarExp scrt
        in CaseE scrt' (map desugarAlt alts)

    Con _ qname -> DataConE () (qnameToStr qname) []

    -- TODO: timeit: parsing it's type isn't straightforward.

    InfixApp _ e1 (QVarOp _ (UnQual _ (Symbol _ ".||."))) e2 ->
      ParE (desugarExp e1) (desugarExp e2)

    InfixApp _ e1 op e2 ->
      let e1' = desugarExp e1
          e2' = desugarExp e2
          op' = desugarOp  op
      in (PrimAppE op' [e1', e2'])

    _ -> error ("desugarExp: Unsupported expression: " ++ show e)
  where
    litToInt :: Show a => Literal a -> Int
    litToInt (Int _ i _) = (fromIntegral i) -- lossy conversion here
    litToInt lit         = error ("desugarExp: Literal not supported: " ++ show lit)

    qnameToStr :: Show a => H.QName a -> String
    qnameToStr qname =
      case qname of
        Qual _ mname n -> (mnameToStr mname ++ "." ++ nameToStr n)
        UnQual _ n     -> (nameToStr n)
        Special{}      -> error $ "desugarExp: Special identifiers not supported: " ++ show qname

    mnameToStr :: ModuleName a -> String
    mnameToStr (ModuleName _ s) = s

    desugarOp :: (Show a) => QOp a -> (Prim Ty0)
    desugarOp qop =
      case qop of
        QVarOp _ (UnQual _ (Symbol _ op)) ->
          case M.lookup op primMap of
            Just pr -> pr
            Nothing -> error $ "desugarExp: Unsupported binary op: " ++ show op
        op -> error $ "desugarExp: Unsupported op: " ++ show op

    desugarAlt :: (Show a) => Alt a -> (DataCon, [(Var,())], L Exp0)
    desugarAlt alt =
      case alt of
        Alt _ (PApp _ qname ps) (UnGuardedRhs _ rhs) Nothing ->
          let conName = qnameToStr qname
              ps' = map (\x -> case x of
                                 PVar _ v -> (toVar . nameToStr) v
                                 _        -> error "desugarExp: Non-variable pattern in case.")
                        ps
              rhs' = desugarExp rhs
          in (conName, [(v,()) | v <- ps'], rhs')
        Alt _ _ GuardedRhss{} _ -> error "desugarExp: Guarded RHS not supported in case."
        Alt _ _ _ Just{}        -> error "desugarExp: Where clauses not allowed in case."
        Alt _ pat _ _           -> error $ "desugarExp: Unsupported pattern in case: " ++ show pat

    generateBind :: (Show a) => TyEnv0 -> Decl a -> L Exp0 -> L Exp0
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
                                         ++ "(found: "++ show not_var ++ ")"
        oth -> error ("desugarExp: Only variable bindings are allowed in let. (found: " ++ show oth ++ ")")

collectTopTy :: (Show a) => Decl a -> TyEnv0 -> TyEnv0
collectTopTy d env =
  case d of
    TypeSig _ names ty ->
      let ty' = desugarTopType ty
      in foldr (\n acc -> M.insert (toVar $ nameToStr n) ty' acc) env names
    _ -> env

collectTopLevel :: (Show a) => TyEnv0 -> Decl a -> Maybe TopLevel
collectTopLevel env decl =
  case decl of
    -- 'collectTopTy' takes care of this.
    TypeSig{} -> Nothing

    DataDecl _ (DataType _) _ctx decl_head cons _deriving_binds ->
      let desugarConstr :: (Show a) => QualConDecl a -> (DataCon,[(IsBoxed,Scheme Ty0)])
          desugarConstr qdecl =
            case qdecl of
              QualConDecl _ _tyvars _ctx (ConDecl _ name arg_tys) ->
                ( nameToStr name , map desugarTopType' arg_tys )
              _ -> error ("desugarConstr: Unsupported data constructor: " ++ show qdecl)

          ty_name = case decl_head of
                      DHead _ name -> toVar (nameToStr name)
                      _ -> error ("collectTopLevel: Unsupported data declaration: " ++ show decl)
          cons' = map desugarConstr cons
      in Just $ HDDef (PDDef ty_name cons')

    PatBind _ (PVar _ (Ident _ "main")) (UnGuardedRhs _ bod) _binds ->
      Just $ HMain $ Just (desugarExp bod)

    FunBind _ [Match _ fname hargs (UnGuardedRhs _ bod) _where] ->
      let fname_str = nameToStr fname
          fname_var = toVar (fname_str)

          fnArg :: (Show a) => Pat a -> Var
          fnArg (PVar _ n) = toVar (nameToStr n)
          fnArg arg        = error ("collectTopLevel: Unsupported function arg: " ++ show arg)


      in case M.lookup fname_var env of
           Nothing -> error $ "collectTopLevel: Top-level function with no type signature: " ++ fname_str
           Just fun_ty ->
             let bod' = desugarExp bod
                 (arg,ty,bod'') = case hargs of
                                    []  -> (toVar "_", fun_ty, bod')
                                    [a] -> (fnArg a,fun_ty,bod')
                                    -- Here we directly desugar multiple arguments
                                    -- into a tuple argument.
                                    -- TODO(CSK): use gensym.
                                    _ -> let new_arg = toVar (fname_str ++ "_arg")
                                             args    = map fnArg hargs
                                             fun_ty' = unCurryTopTy fun_ty
                                         in (new_arg, fun_ty',
                                             tuplizeRefs new_arg args bod')
             in Just $ HFunDef $
                  PFDef { fName = fname_var
                        , fArg  = arg
                        , fTy   = ty
                        , fBody = bod'' }

    FunBind _ _ -> error $ "collectTopLevel: Found a function with multiple RHS."
    _ -> error (show decl)

nameToStr :: Name a -> String
nameToStr (Ident _ s)  = s
nameToStr (Symbol _ s) = s

parseFile :: FilePath -> IO (L0.PProg, Int)
parseFile path = do
  fmap parseModule (readFile path) >>= \case
    ParseOk hs -> do
        let prog = desugarModule hs
        print prog
        error "Disabled until the new frontend is ready"
    ParseFailed _ er -> do
      error ("haskell-src-exts failed: " ++ er)
