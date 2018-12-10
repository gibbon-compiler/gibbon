{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Gibbon.L0.Typecheck where

import           Control.Monad.Except
import           Control.Monad.State ( MonadState )
import           Data.Loc
import qualified Data.Map as M
import qualified Data.Set as S
import           Text.PrettyPrint hiding ( (<>) )
import           Text.PrettyPrint.GenericPretty

import           Gibbon.L0.Syntax as L0
import           Gibbon.Common

--------------------------------------------------------------------------------

{-

N.B.

* Algorithm W
* Implements ScopedTypedVariables
* Lets are generalized
* No RankNTypes
* No MonoLocalBinds
* No polymorphic recursion

-}

--------------------------------------------------------------------------------

newtype TcM a = TcM (ExceptT Doc PassM a)
  deriving (Functor, Applicative, Monad, MonadError Doc, MonadState Int)

runTcM :: TcM a -> PassM (Either Doc a)
runTcM (TcM tc) = runExceptT tc

err :: Doc -> TcM a
err d = throwError ("L0.Typecheck: " $$ nest 4 d)

tcProg :: Prog0 -> PassM Prog0
tcProg prg@Prog{ddefs,fundefs,mainExp} = do
  let init_fenv = M.map funTy fundefs
  mapM_ (tcFun ddefs init_fenv) fundefs

  -- Run the typechecker on the expression, and update it's type in the program
  -- (the parser initializes the main expression with the void type).
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (e,main_ty) -> do
                  let tc = do (s1,ty1) <- tcExp ddefs emptySubst M.empty init_fenv e
                              s2 <- unify e main_ty ty1
                              pure (s1 <> s2, substTy s2 ty1)
                  res <- runTcM tc
                  case res of
                    Left er -> error (render er)
                    Right (_s, ty) -> pure $ Just (e, ty)
  pure prg { mainExp = mainExp' }

{- Note [Respecting foralls]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider this function:

    id :: forall a. a -> a
    id x = 10

This doesn't typecheck in Haskell, but does under this system.
Should we reject this program ? If we only use unification to match
the derived type with the given type, it succeeds, with ( a ~ IntTy ).
We need something stronger than unification but weaker than (==) to
match the types.

-}
checkForAlls :: Doc -> [TyVar] -> Subst -> TcM ()
-- HACK: FIXME
checkForAlls msg tyvars (Subst mp) = do
  -- The tyvars captured by this substitution.
  let capturedTyVars = filter isCaptured tyvars
  case capturedTyVars of
    [] -> pure ()
    ls -> err $ text "Couldn't satisfy these constraints: "
                  $$ hsep (map (\v -> case M.lookup v mp of
                                        Nothing -> empty
                                        Just t  -> doc v <+> text "~" <+> doc t) ls)
                  $$ msg
  where
    isCaptured x =
      case M.lookup x mp of
        Nothing        -> False
        Just (TyVar _) -> False
        Just _         -> True

tcFun :: DDefs0 -> Gamma -> FunDef0 -> PassM ()
tcFun ddefs fenv FunDef{funName,funArg,funTy,funBody} = do
  let arg_ty = inTy funTy
      s1 = Subst $ M.singleton funArg arg_ty
      venv = M.singleton funArg (generalize M.empty arg_ty)

  let tc = do (s2,ty2) <- tcExp ddefs s1 venv fenv funBody
              s3 <- unify funBody ty2 (outTy funTy)

              -- See Note [Respecting forall]
              let ForAll tyvars _ = funTy
                  s4 = s2 <> s3
                  msg = text "which is bound by:"
                          $$ text (fromVar funName)
                          <+> text "::" <+> doc funTy
              checkForAlls msg tyvars s4
              --

              pure (s4, substTy s3 ty2)

  res <- runTcM tc
  case res of
    Left er -> error $ render er
    Right _ -> pure ()

tcExps :: DDefs0 -> Subst -> Gamma -> Gamma -> [L Exp0] -> TcM (Subst, [Ty0])
tcExps ddefs sbst venv fenv ls = do
  (sbsts,tys) <- unzip <$> mapM go ls
  pure (foldl (<>) sbst sbsts, tys)
  where
    go = tcExp ddefs sbst venv fenv

-- | Algorithm W
tcExp :: DDefs0 -> Subst -> Gamma -> Gamma -> L Exp0 -> TcM (Subst, Ty0)
tcExp ddefs sbst venv fenv e@(L _ ex) =
  case ex of
    VarE x -> case M.lookup x venv of
                Nothing -> err $ text "Unbound variable " <> doc x
                Just ty -> (sbst,) <$> instantiate ty

    LitE{}    -> pure (sbst, IntTy)
    LitSymE{} -> pure (sbst, IntTy)

    AppE f _locs arg -> do
      case (M.lookup f venv, M.lookup f fenv) of
        (Just lam_ty, _) -> do t1 <- instantiate lam_ty
                               (s2,t2) <- go arg
                               tv <- freshTy
                               s3 <- unify e (substTy s2 t1) (ArrowTy t2 tv)
                               pure (s2 <> s3, substTy s3 tv)
        -- CHECKME
        (_, Just fn_ty)  -> do t1 <- instantiate fn_ty
                               (s2,t2) <- go arg
                               tv <- freshTy
                               s3 <- unify e (substTy s2 t1) (ArrowTy t2 tv)
                               pure (s2 <> s3, substTy s3 tv)
        _ -> err $ text "Unknown function:" <+> doc f

    PrimAppE pr args -> do
      (s1, _tys) <- tcExps ddefs sbst venv fenv args
      let checkLen :: Int -> TcM ()
          checkLen n =
            if length args == n
            then pure ()
            else err $ text "Wrong number of arguments to " <+> doc pr <+> text "."
                         $$ text "Expected " <+> doc n
                         <+> text ", received " <+> doc (length args)
                         $$ text "In the expression: " <+> doc ex
          len0 = checkLen 0
      case pr of
        _ | pr `elem` [MkTrue, MkFalse] -> do
            len0
            pure (s1, BoolTy)
        oth -> err $ text "PrimAppE : TODO " <+> doc oth

    LetE (v, _locs, ty, rhs) bod -> do
      (s1,t1) <- go rhs
      s2 <- unify rhs ty t1
      let venv' = substTyEnv s2 venv
          t1'   = generalize venv' t1

      -- See Note [Respecting forall]
      let s3  = s1 <> s2
          ty'@(ForAll tyvars _) = generalize venv' ty
          msg = text "which is bound by:"
                  $$ text (fromVar v)
                  <+> text "::" <+> doc ty'
      checkForAlls msg tyvars s3
      --

      (s4,t4) <- tcExp ddefs (s1 <> s2) (M.insert v t1' venv') fenv bod
      pure (s3 <> s4, t4)

    IfE a b c -> do
      (s1,t1) <- go a
      (s2,t2) <- go b
      (s3,t3) <- go c
      s4 <- unify a t1 BoolTy
      s5 <- unify e t2 t3
      pure (s1 <> s2 <> s3 <> s4 <> s5, substTy s5 t2)

    MkProdE es -> do
      (s1, tys) <- tcExps ddefs sbst venv fenv es
      pure (s1, ProdTy tys)

    ProjE i a -> do
     (s1,t1) <- go a
     case substTy s1 t1 of
       ProdTy tys -> pure (s1, tys !! i)
       t1' -> err $ "tcExp: Coulnd't match expected type: ProdTy [...]"
                      <+> "with actual type: " <+> doc t1'
                      $$ "In the expression: " <+> doc ex

    -- CaseE
    -- DataConE

    Ext (LambdaE (v,ty) bod) -> do
      t1 <- freshTy
      let venv' = M.insert v (ForAll [] t1) venv
      s2 <- unify (l$ VarE v) ty t1
      (s3, t3) <- tcExp ddefs s2 venv' fenv bod
      return (s3, substTy s3 (ArrowTy t1 t3))

    _ -> err $ "tcExp: TODO" <+> doc ex
  where
    go = tcExp ddefs sbst venv fenv

    freshTy :: TcM Ty0
    freshTy = TyVar <$> gensym "b"


instantiate :: TyScheme -> TcM Ty0
instantiate (ForAll as ty) = do
  bs <- mapM (fmap TyVar . gensym) as
  let s1 = Subst $ M.fromList (zip as bs)
  pure (substTy s1 ty)


generalize :: Gamma -> Ty0 -> TyScheme
generalize env ty =
  let tvs = S.toList (gFreeVars ty `S.difference` gFreeVars env)
  in ForAll tvs ty

--------------------------------------------------------------------------------
-- Type environment
--------------------------------------------------------------------------------

-- We can't directly use Env2 because of the way it's tied together with
-- PreExp and the Expression class. We want to annotate L0 expressions
-- with 'Ty0' but TEnv should store 'TyScheme's.
type Gamma = TyEnv TyScheme

instance FreeVars a => FreeVars (TyEnv a) where
  gFreeVars env = foldr (S.union . gFreeVars) S.empty (M.elems env)

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

newtype Subst = Subst (M.Map TyVar Ty0)
  deriving (Ord, Eq, Read, Show)

instance Semigroup Subst where
  -- s1 <> s2 == substTy s1 . substTy s2
  (Subst s1) <> (Subst s2) =
    let mp = M.map (substTy (Subst s1)) s2 `M.union` s1
    in Subst mp

emptySubst :: Subst
emptySubst = Subst (M.empty)

substTy :: Subst -> Ty0 -> Ty0
substTy (Subst mp) ty =
  case ty of
    IntTy   -> IntTy
    BoolTy  -> BoolTy
    TyVar v -> M.findWithDefault ty v mp
    ProdTy tys  -> ProdTy (map go tys)
    SymDictTy t -> SymDictTy (go t)
    ArrowTy a b -> ArrowTy (go a) (go b)
    PackedTy t tys -> PackedTy t (map go tys)
    ListTy t -> ListTy (go t)
  where
    go = substTy (Subst mp)

substTyScheme :: Subst -> TyScheme -> TyScheme
substTyScheme (Subst mp) (ForAll tvs ty) =
  ForAll tvs (substTy s2 ty)
    where s2 = Subst (foldr M.delete mp tvs)

substTyEnv :: Subst -> Gamma -> Gamma
substTyEnv s env = M.map (substTyScheme s) env

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

unify :: L Exp0 -> Ty0 -> Ty0 -> TcM Subst
unify ex ty1 ty2
  | ty1 == ty2 = pure emptySubst
  | otherwise  =
      case (ty1,ty2) of
        (IntTy, IntTy)   -> pure emptySubst
        (BoolTy, BoolTy) -> pure emptySubst
        (TyVar a, _) -> unifyTyVar ex a ty2
        (_, TyVar b) -> unifyTyVar ex b ty1
        (ProdTy as, ProdTy bs) -> unifyl ex (zip as bs)
        (ArrowTy a b, ArrowTy c d) -> do
          s1 <- unify ex a c
          s2 <- unify ex (substTy s1 b) (substTy s1 d)
          pure (s2 <> s1)
        (PackedTy tc1 tys1, PackedTy tc2 tys2) ->
          if tc1 == tc2
          then unifyl ex (zip tys1 tys2)
          else err fail_msg
        _ -> err fail_msg
  where fail_msg = text "Couldn't unify:" <+> doc ty1 <+> text "and" <+> doc ty2
                     $$ text "In the expression: "
                     $$ nest 2 (doc ex)


unifyl :: L Exp0 -> [(Ty0,Ty0)] -> TcM Subst
unifyl _ [] = pure emptySubst
unifyl e ((ty1,ty2):cs) = (<>) <$> unify e ty1 ty2 <*> unifyl e cs

unifyTyVar :: L Exp0 -> TyVar -> Ty0 -> TcM Subst
unifyTyVar ex a t
  | occursCheck a t = err $ text "Occurs check: cannot construct the inifinite type: "
                              $$ nest 2 (doc a <+> text " ~ " <+> doc t)
                              $$ text "In the expression: "
                              $$ nest 2 (doc ex)
  | otherwise       = pure $ Subst (M.singleton a t)

occursCheck :: TyVar -> Ty0 -> Bool
occursCheck a t = a `S.member` gFreeVars t

--------------------------------------------------------------------------------
-- Other helpers
--------------------------------------------------------------------------------

_ensureEqualTy :: Ty0 -> Ty0 -> TcM ()
_ensureEqualTy ty1 ty2
  | ty1 == ty2 = pure ()
  | otherwise  = err $ text "Couldn't match expected type:" <+> doc ty1
                         $$ "with actual type: " <+> doc ty2
