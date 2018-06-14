{-# LANGUAGE LambdaCase           #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Gibbon.HaskellFrontend
  ( parseFile
  -- * Everything else could remain internal:
  , desugarModule
  , desugarExp
  , desugarTopType
  , desugarType
  ) where

import Control.Monad (forM)
import Data.Either (partitionEithers)
import Data.Foldable (foldrM)
import Data.Loc
import Data.Maybe (catMaybes)
import Language.Haskell.Exts.Simple.Parser
import qualified Language.Haskell.Exts.Simple.Syntax as S
import qualified Data.Map as M
import qualified Data.List as L

import Gibbon.L1.Syntax as L1
import Gibbon.Common as C hiding (l)
import Prelude hiding (exp)

--------------------------------------------------------------------------------

type Ds a = Either String a

err :: String -> Ds a
err = Left

--------------------------------------------------------------------------------

desugarModule :: S.Module -> Ds Prog1
desugarModule (S.Module _ _ _ decls) = do
  -- since top-level function types and their types can't be declared in
  -- single top-level declaration we first collect types and then collect
  -- definition
  funTys <- (M.fromList . catMaybes) <$> mapM collectTopFunTy decls

  (dataDecls, fun_decls) <-
    (partitionEithers . catMaybes) <$> mapM (collectTopLevel funTys) decls

  let
    dataMap = M.fromList (map (\def -> (tyName def, def))  dataDecls)
    funMap  = M.fromList (map (\def -> (funName def, def)) fun_decls)

    (mainFn, funMapNoMain) =
      -- ugh, no alterF in this 'containers' version
      ( funBody <$> M.lookup (toVar "main") funMap
      , M.delete (toVar "main") funMap
      )
    -- Initialize the main expression with a void type. The typechecker will fix the type later.
    main = case mainFn of
             Just x  -> Just (x, ProdTy [])
             Nothing -> Nothing
  return (Prog dataMap funMapNoMain main)

collectTopFunTy :: S.Decl -> Ds (Maybe (Var, TopTy))
collectTopFunTy decl =
  case decl of
    S.TypeSig [n] ty -> Just <$> ((toVar . nameToStr) n ,) <$> desugarTopType ty
    ty@S.TypeSig{}   -> err ("Unsupported top-level type declaration: " ++ show ty)
    S.FunBind{}      -> return Nothing
    S.DataDecl{}     -> return Nothing
    S.PatBind{}      -> return Nothing
    unsupported      -> err ("collectTopFunTy: Unsupported top-level thing: " ++ show unsupported)


collectTopLevel :: M.Map Var TopTy -> S.Decl -> Ds (Maybe (Either (DDef Ty1) FunDef1))

-- This is the main expression. We're disguising it as a FunDef just for convenience.
-- We should probably create a sum type with these 3 things; ddefs, fundefs, and mainExp
-- and return that
collectTopLevel _ (S.PatBind (S.PVar name) (S.UnGuardedRhs rhs) _) = do
  let name' = toVar $ nameToStr name
  rhs' <- desugarExp rhs
  return $ Just $ Right $ FunDef name' "nothing" (ProdTy [],ProdTy []) rhs'

collectTopLevel _ S.TypeSig{} = return Nothing
collectTopLevel funTys (S.FunBind [S.Match fname args (S.UnGuardedRhs rhs) Nothing]) = do
    let fname'      = (toVar . nameToStr) fname
        fun_ty      = M.findWithDefault (error ("Can't find function in type env: " ++ (fromVar fname')))
                      fname' funTys
    [arg']   <- mapM collectArg args
    -- Limiting to one argument for now:
    [arg_ty] <- mapM (getArgTy fun_ty) [ 1 .. length [arg'] ]
    rhs'    <- desugarExp rhs
    return (Just (Right (FunDef fname' arg' (arg_ty, getRetTy fun_ty) rhs')))
  where
    collectArg :: S.Pat -> Ds Var
    collectArg (S.PVar n) = return $ (toVar . nameToStr) n
    collectArg arg      = err ("Unsupported function arg: " ++ show arg)

    getArgTy :: TopTy -> Int -> Ds Ty1
    getArgTy (Arrow ts) n = return (ts !! n)
    getArgTy ty         _ = err ("getArgTy: " ++ show ty)

    getRetTy :: TopTy -> Ty1
    getRetTy (Arrow ts) = last ts
    getRetTy (T1 t)     = t

collectTopLevel _ (S.DataDecl S.DataType Nothing decl_head cons _deriving_binds) = do
    let ty_name' = nameToStr ty_name
        ty_name = case decl_head of
                    S.DHead name -> name
                    _ -> error $ "collectTopLevel: unexpected type: " ++ show decl_head

    constrs <- mapM collectConstr cons
    return (Just (Left (DDef (toVar ty_name') constrs)))
  where
    collectConstr (S.QualConDecl Nothing Nothing (S.ConDecl conName arg_tys)) =
      ( nameToStr conName, ) <$>
      L.map ( False, ) <$>
      mapM desugarType arg_tys
    collectConstr unsupported =
      err ("Unsupported data constructor: " ++ show unsupported)

collectTopLevel _ unsupported = err ("collectTopLevel: Unsupported top-level thing: " ++ show unsupported)

--------------------------------------------------------------------------------

pattern FstVar :: forall t t1 (t2 :: * -> * -> *). L (PreExp t2 t1 t)
pattern FstVar <- L NoLoc (VarE (C.Var "fst"))
  where FstVar = L NoLoc (VarE (toVar "fst"))

pattern SndVar :: forall t t1 (t2 :: * -> * -> *). L (PreExp t2 t1 t)
pattern SndVar <- L NoLoc (VarE (C.Var "snd"))
  where SndVar = L NoLoc (VarE (toVar "snd"))

-- | Convert Haskell src-exts syntax to our syntax.  Handle infix operators, etc.
-- Disambiguate things that look like applications.
desugarExp :: S.Exp -> Ds (L L1.Exp1)
desugarExp e = L NoLoc <$>
    case e of
      S.Var qname -> VarE <$> toVar <$> qnameToStr qname

      S.Con qname -> DataConE () <$> qnameToStr qname <*> pure []

      S.Lit l   -> L1.LitE <$> litToInt l

      S.App e1 e2 ->
        desugarExp e1 >>= \case
          FstVar ->
            L1.ProjE 0 <$> desugarExp e2
          SndVar ->
            L1.ProjE 1 <$> desugarExp e2
          L _ (VarE f) ->
            L1.AppE f [] <$> desugarExp e2
          L _ (DataConE () c as) -> do
            e2' <- desugarExp e2
            return (L1.DataConE () c (as ++ [e2']))
          L _ (L1.AppE f [] l) -> do
            e2' <- desugarExp e2
            return (L1.AppE f [] (L NoLoc $ MkProdE [l,e2']))
          f ->
            err ("Only variables allowed in operator position in function applications. (found: " ++ show f ++ ")")

      S.Tuple S.Unboxed _ ->
        err "Only boxed tuples are allowed."
      S.Tuple S.Boxed [e1, e2] ->
        (\a b -> MkProdE [a,b]) <$> desugarExp e1 <*> desugarExp e2
      S.Tuple _ es ->
        err ("Tuples can only be pairs. (" ++ show es ++ ")")

      S.Let (S.BDecls decls) rhs -> do
        rhs' <- desugarExp rhs
        xs <- foldrM generateBind rhs' decls
        Right $ unLoc xs

      S.Case scrt alts -> do
        scrt' <- desugarExp scrt
        CaseE scrt' <$> mapM (desugarAlt ()) alts

      S.Paren e0 -> do
        e' <- desugarExp e0
        Right $ unLoc e'

      S.InfixApp e1 op e2 -> do
        e1' <- desugarExp e1
        e2' <- desugarExp e2
        op' <- desugarOp  op
        return (PrimAppE op' [e1', e2'])

      _ -> err ("desugarExp: Unsupported expression: " ++ show e)

-------------------------------------------------------------------------------

desugarOp :: S.QOp -> Ds (Prim Ty1)
desugarOp (S.QVarOp (S.UnQual (S.Symbol op))) =
  case op of
    "+" -> return AddP
    "-" -> return SubP
    "*" -> return MulP
    _   -> err $ "Unsupported binary op: " ++ show op

desugarOp op = err $ "Unsupported op: " ++ show op

--------------------------------------------------------------------------------

generateBind :: S.Decl -> L (L1.Exp1) -> Ds (L (L1.Exp1))
generateBind decl exp =
  case decl of
    S.PatBind _ _ Just{}          -> err "where clauses not allowed"
    S.PatBind _ S.GuardedRhss{} _ -> err "Guarded right hand side not supported."

    S.PatBind (S.PVar v) (S.UnGuardedRhs rhs) Nothing -> do
      rhs' <- desugarExp rhs
      return $ L NoLoc $ LetE ((toVar . nameToStr) v, [],
                              error "Haskell front end doesn't know type.  Must infer",
                              rhs')
                         exp

    S.PatBind not_var _ _ -> err $ "Only variable bindings are allowed in let."
                                   ++ "(found: "++ show not_var ++ ")"

    oth -> err ("Only variable bindings are allowed in let. (found: " ++ show oth ++ ")")


--------------------------------------------------------------------------------

desugarAlt :: l -> S.Alt -> Ds (DataCon, [(Var,l)], L (L1.Exp1))
desugarAlt dummyL alt =
  case alt of
    S.Alt (S.PApp qname ps) (S.UnGuardedRhs rhs) Nothing -> do
      conName <- qnameToStr qname
      ps' <- forM ps $ \case S.PVar v -> return $ (toVar . nameToStr) v
                             _        -> err "Non-variable pattern in case."
      rhs' <- desugarExp rhs
      return (conName, [(v,dummyL) | v <- ps'], rhs')

    S.Alt _ S.GuardedRhss{} _ -> err "Guarded RHS not supported in case."
    S.Alt _ _ Just{}          -> err "Where clauses not allowed in case."
    S.Alt pat _ _             -> err $ "Unsupported pattern in case: " ++ show pat

-------------------------------------------------------------------------------

-- | Top-level function definitions can have arrow in the types. Others can't.
data TopTy = Arrow [Ty1]
           | T1 Ty1
  deriving (Show)

desugarTopType :: S.Type -> Ds TopTy
desugarTopType ty =
  case ty of
    S.TyFun t1 t2 -> do
      t1' <- desugarType t1
      t2' <- desugarTopType t2
      return $ Arrow $
        case t2' of
          Arrow ts -> t1' : ts
          T1 t     -> [t1', t]

    _ -> T1 <$> desugarType ty


desugarType :: S.Type -> Ds Ty1
desugarType ty =
  case ty of
    S.TyCon (S.UnQual (S.Ident "Int")) -> return IntTy
    S.TyCon (S.UnQual (S.Ident con))   -> return (PackedTy con ())
    S.TyTuple S.Boxed [ty1, ty2]       -> (\a b-> ProdTy [a,b])
                                          <$> desugarType ty1
                                          <*> desugarType ty2

    S.TyApp (S.TyCon (S.UnQual (S.Ident "Dict"))) ty' -> SymDictTy <$> desugarType ty'

    S.TyApp ty1 _ty2 ->
      desugarType ty1 >>= \case
      PackedTy con dec -> return (PackedTy con dec)
      _ -> err ("Unsupported type: " ++ show ty)

    _ -> err $ "Unsupported type: " ++ show ty

--------------------------------------------------------------------------------

qnameToStr :: S.QName -> Ds String
qnameToStr qname =
  case qname of
    S.Qual mname n -> return (mnameToStr mname ++ "." ++ nameToStr n)
    S.UnQual n     -> return (nameToStr n)
    S.Special{}    -> err $ "Special identifiers not supported: " ++ show qname

mnameToStr :: S.ModuleName -> String
mnameToStr (S.ModuleName s) = s

nameToStr :: S.Name -> String
nameToStr (S.Ident s)  = s
nameToStr (S.Symbol s) = s

litToInt :: S.Literal -> Ds Int
litToInt (S.Int i) = return (fromIntegral i) -- lossy conversion here
litToInt l         = err ("Literal not supported: " ++ show l)

----------------------------------------

parseFile :: FilePath -> IO (L1.Prog1, Int)
parseFile path = do
    fmap parse (readFile path) >>= \case
      ParseOk hs -> do
        putStrLn "haskell-src-exts parsed OK. Desugaring..."
        case desugarModule hs of
          Right ast -> do
            putStrLn "Desugared AST:"
            print ast
            return (ast,0)
          Left er -> do
            error ("Desugaring failed: " ++ er)
      ParseFailed _ er -> do
        error ("haskell-src-exts failed: " ++ er)
