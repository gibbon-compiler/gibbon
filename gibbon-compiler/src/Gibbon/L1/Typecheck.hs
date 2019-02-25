{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Gibbon.L1.Typecheck
  ( -- * The two main typechecker functions
    tcProg, tcExp

    -- * Helpers
  , TCError(..)
  , extendEnv, lookupVar, tcProj, checkLen, ensureEqual, ensureEqualTy, TcM
  )
where


import Control.Monad.Except
import Data.Loc
import Data.Map as M
import Data.List as L
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L1.Syntax as L1
import Gibbon.DynFlags
import Prelude hiding (exp)

--------------------------------------------------------------------------------

-- | Typecheck a L1 expression
--
tcExp :: (Eq l, Out l, Out (e l (UrTy l)), FunctionTy (UrTy l)) =>
         DDefs (UrTy l) -> Env2 (UrTy l) -> (L (PreExp e l (UrTy l))) ->
         TcM (UrTy l) (L (PreExp e l (UrTy l)))
tcExp ddfs env exp@(L p ex) =
  case ex of
    VarE v    -> lookupVar env v exp
    LitE _    -> return IntTy
    LitSymE _ -> return IntTy

    AppE v locs e -> do
      let funty =
            case (M.lookup v (fEnv env)) of
              Just ty -> ty
              Nothing -> error $ "Function not found: " ++ sdoc v ++ " while checking " ++
                                 sdoc exp ++ "\nat " ++ sdoc p
      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp

      -- Check argument type
      argTy <- go e
      _     <- ensureEqualTy exp (inTy funty) argTy
      return (outTy funty)

    PrimAppE pr es -> do
      let len0 = checkLen exp pr 0 es
          len2 = checkLen exp pr 2 es
          len3 = checkLen exp pr 3 es

      tys <- mapM go es
      case pr of
        _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP]  -> do
          len2
          _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return IntTy

        _ | pr `elem` [MkTrue, MkFalse] -> do
          len0
          return BoolTy

        EqSymP -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return BoolTy

        _ | pr `elem` [EqIntP, LtP, GtP, LtEqP, GtEqP] -> do
          len2
          _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return BoolTy

        _ | pr `elem` [OrP, AndP] -> do
          len2
          _ <- ensureEqualTy (es !! 0) BoolTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) BoolTy (tys !! 1)
          return BoolTy

        RandP -> return IntTy

        SymAppend -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return SymTy

        DictEmptyP ty -> do
          len0
          return $ SymDictTy ty

        DictInsertP ty -> do
          len3
          let [d,k,v] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          _ <- ensureEqualTy exp ty v
          return d

        DictLookupP ty -> do
          len2
          let [d,k] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          return ty

        DictHasKeyP ty -> do
          len2
          let [d,k] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          return BoolTy

        ErrorP _str ty -> do
          len2
          return ty

        SizeParam -> do
          len0
          return IntTy

        ReadPackedFile _fp _tycon _reg ty -> do
          len0
          return ty

        PEndOf -> return CursorTy

        oth -> error $ "L1.tcExp : PrimAppE : TODO " ++ sdoc oth

    LetE (v,locs,ty,rhs) e -> do
      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp
      -- Check RHS
      tyRhs <- go rhs
      _ <- ensureEqualTy exp tyRhs ty
      let env' = extendEnv env [(v,ty)]
      -- Check body
      tcExp ddfs env' e

    IfE tst consq alt -> do
      -- Check if the test is a boolean
      tyTst <- go tst
      _ <- ensureEqualTy exp tyTst BoolTy

      -- Check if both branches match
      tyConsq <- go consq
      tyAlt   <- go alt

      -- _ <- ensureEqualTy exp tyConsq tyAlt
      if tyConsq == tyAlt
      then return tyConsq
      else throwError $ GenericTC ("If branches have mismatched types:"
                                   ++ sdoc tyConsq ++ ", " ++ sdoc tyAlt) exp


    MkProdE es -> do
      tys <- mapM go es
      return $ ProdTy tys

    ProjE i e -> do
      ty  <- go e
      tyi <- tcProj exp i ty
      return tyi

    CaseE e cs -> do
      tye  <- go e
      let tycons = L.map (getTyOfDataCon ddfs . (\(a,_,_) -> a)) cs
      case L.nub tycons of
        [one] -> do
          -- _ <- ensureEqualTy exp (PackedTy one ()) tye
          let (PackedTy t _l) = tye
          if one == t
          then return ()
          else error$ "Expected these to be the same: " ++ one ++ " & " ++ sdoc t
          tcCases ddfs env cs
        oth   -> throwError $ GenericTC ("Case branches have mismatched types: " ++ sdoc oth
                                         ++" , in " ++ sdoc exp) exp

    DataConE loc dc es -> do
      tys <- mapM go es
      let dcTy = getTyOfDataCon ddfs dc
          args = lookupDataCon ddfs dc
      if length args /= length es
      then throwError $ GenericTC ("Invalid argument length: " ++ sdoc es) exp
      else do
        -- Check if arguments match with expected datacon types
        sequence_ [ ensureEqualTy e ty1 ty2
                  | (ty1,ty2,e) <- zip3 args tys es]
        return $ PackedTy dcTy loc

    TimeIt e _ty _b -> do
      -- Before flatten, _ty is always (PackedTy "DUMMY_TY" ())
      -- enforce ty == _ty in strict mode ?
      ty <- go e
      return ty

    ParE a b -> do
      aty <- go a
      bty <- go b
      return (ProdTy [aty, bty])

    Ext{} -> error $ "L1.Typecheck: Unexpected " ++ sdoc ex
    MapE{} -> error $ "L1.Typecheck: TODO: " ++ sdoc ex
    FoldE{} -> error $ "L1.Typecheck: TODO: " ++ sdoc ex

  where
    go = tcExp ddfs env


-- | Typecheck a L1 program
--
tcProg :: Prog1 -> PassM Prog1
tcProg prg@Prog{ddefs,fundefs,mainExp} = do

  -- Get flags to check if we're in packed mode
  flags <- getDynFlags

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main expression.
  -- Run the typechecker on the expression, and update it's type in the program
  -- (the parser initializes the main expression with the void type).
  let mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (e,main_ty)  ->
                     let res = runExcept $ tcExp ddefs env e
                     in case res of
                         Left err -> error $ sdoc err
                         Right ty ->
                           -- The program was just parsed, the type of the
                           -- expression must be *inferred*.
                           -- Otherwise, fail if the types don't match.
                           if main_ty == voidTy
                           then Just (e, ty) 
                           else if main_ty == ty
                                -- Fail if the main expression is packed and we're in packed mode
                                then if (not $ hasPacked ty) || (not $ gopt Opt_Packed flags)
                                     then return (e, ty)
                                     else error $ "Main expression has type " ++ sdoc ty ++ ", but it must be a simple (non-packed) type, such as " ++ (sdoc (IntTy :: Ty1)) ++ "."
                                else error $ "Expected type " ++ sdoc main_ty ++ " but got " ++ sdoc ty

  return prg { mainExp = mainExp' }

  where
    env = L1.progToEnv prg

    -- fd :: forall e l . FunDef Ty1 Exp -> SyM ()
    fd FunDef{funArg,funTy,funBody} = do
      let (argTy,retty) = funTy
          env' = Env2 (M.singleton funArg argTy) (fEnv env)
          res = runExcept $ tcExp ddefs env' funBody
      case res of
        Left err -> error $ sdoc err
        Right ty -> if ty == retty
                    then return ()
                    else error $ "Expected type " ++ (sdoc retty)
                         ++ " and got type " ++ (sdoc ty)

      return ()

--------------------------------------------------------------------------------
-- Helpers

data TCError exp = GenericTC String  exp
                 | VarNotFoundTC Var exp
                 | UnsupportedExpTC  exp
  deriving (Show, Eq, Ord, Generic)


instance (Out exp, Out (L exp)) => Out (TCError (L exp)) where
  doc tce =
    case tce of
      GenericTC str (L p ex)    -> text str $$ doc p <+> colon <+> doc ex
      VarNotFoundTC v (L p ex)  -> text "Var" <+> doc v <+> text "not found. Checking: " $$
                                   doc p <+> colon <+> doc ex
      UnsupportedExpTC (L p ex) -> text "Unsupported expression:" $$
                                   doc p <+> colon <+> doc ex

type TcM a exp = Except (TCError exp) a


extendEnv :: Env2 (UrTy l) -> [(Var, (UrTy l))] -> Env2 (UrTy l)
extendEnv (Env2 vEnv fEnv) ((v,ty):rest) = extendEnv (Env2 (M.insert v ty vEnv) fEnv) rest
extendEnv env [] = env


lookupVar :: Env2 (UrTy l) -> Var -> L (PreExp e l (UrTy l)) ->
             TcM (UrTy l) (L (PreExp e l (UrTy l)))
lookupVar env var exp =
    case M.lookup var $ vEnv env of
      Nothing -> throwError $ VarNotFoundTC var exp
      Just ty -> return ty

tcProj :: (Out l) => (L (PreExp e l (UrTy l))) -> Int -> (UrTy l) ->
          TcM (UrTy l) (L (PreExp e l (UrTy l)))
tcProj _ i (ProdTy tys) = return $ tys !! i
tcProj e _i ty = throwError $ GenericTC ("Projection from non-tuple type " ++ (sdoc ty)) e


tcCases :: (Out l, Eq l, Out (e l (UrTy l)), FunctionTy (UrTy l))
        => DDefs (UrTy l) -> Env2 (UrTy l) ->
           [(DataCon, [(Var, l)], L (PreExp e l (UrTy l)))] ->
           TcM (UrTy l) (L (PreExp e l (UrTy l)))
tcCases ddfs env cs = do
  tys <- forM cs $ \(c,args',rhs) -> do
           let args  = L.map fst args'
               targs = lookupDataCon ddfs c
               env'  = extendEnv env (zip args targs)
           tcExp ddfs env' rhs
  foldM_ (\acc (ex,ty) ->
            if ty == acc
            then return acc
            else throwError $ GenericTC ("Case branches have mismatched types: "
                                         ++ sdoc acc ++ ", " ++ sdoc ty) ex)
         (head tys) (zipWith (\ty (_,_,ex) -> (ex,ty)) tys cs)
  return $ head tys


checkLen :: (Out op, Out arg) => (L (PreExp e l (UrTy l))) -> op -> Int -> [arg] ->
            TcM () (L (PreExp e l (UrTy l)))
checkLen expr pr n ls =
  if length ls == n
  then return ()
  else throwError $ GenericTC ("Wrong number of arguments to "++sdoc pr++
                               ".\nExpected "++sdoc n++", received "
                                ++sdoc (length ls)++":\n  "++sdoc ls)
                    expr

-- | Ensure that two things are equal.
-- Includes an expression for error reporting.
ensureEqual :: (Eq l) => (L (PreExp e l (UrTy l))) -> String -> (UrTy l) ->
               (UrTy l) -> TcM (UrTy l) (L (PreExp e l (UrTy l)))
ensureEqual exp str a b = if a == b
                          then return a
                          else throwError $ GenericTC str exp


-- | Ensure that two types are equal.
-- Includes an expression for error reporting.
ensureEqualTy :: (Eq l, Out l) => (L (PreExp e l (UrTy l))) -> (UrTy l) -> (UrTy l) ->
                 TcM (UrTy l) (L (PreExp e l (UrTy l)))
ensureEqualTy exp a b = ensureEqual exp ("Expected these types to be the same: "
                                         ++ (sdoc a) ++ ", " ++ (sdoc b)) a b
