{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Gibbon.L0.Typecheck where

import           Control.Monad.Except
import           Control.Monad.State ( MonadState )
import           Data.Foldable ( foldlM )
import           Data.List
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
  fundefs_tc <- mapM (tcFun ddefs init_fenv) fundefs

  -- Run the typechecker on the expression, and update it's type in the program
  -- (the parser initializes the main expression with the void type).
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (e,main_ty) -> do
                  let tc = do (s1,ty1,e_tc) <- tcExp ddefs emptySubst M.empty init_fenv S.empty e
                              s2 <- unify e main_ty ty1
                              pure (s1 <> s2, substTy s2 ty1, e_tc)
                  res <- runTcM tc
                  case res of
                    Left er -> error (render er)
                    Right (_s, ty, e_tc) -> pure $ Just (e_tc, ty)
  pure prg { fundefs = fundefs_tc
           , mainExp = mainExp' }

tcFun :: DDefs0 -> Gamma -> FunDef0 -> PassM FunDef0
tcFun ddefs fenv fn@FunDef{funArg,funTy,funBody} = do
  res <- runTcM $ do
    let (ForAll tyvars (ArrowTy arg_ty _)) = funTy
        -- TODO, note.
        init_venv = M.singleton funArg (ForAll [] arg_ty)
        init_s    = Subst $ M.singleton funArg arg_ty
    (s1,ty1,funBody_tc) <- tcExp ddefs init_s init_venv fenv (S.fromList tyvars) funBody
    let ty1_gen = ForAll tyvars (ArrowTy arg_ty ty1)
    -- CSK: Disabled temporarily.
    -- s <- forallCheck funBody (S.fromList tyvars) ty1_gen funTy
    pure (s1, funBody_tc)
  case res of
    Left er -> error $ render er
    Right (_,bod) -> pure $ fn { funBody = bod }

tcExps :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar -> [L Exp0] -> TcM (Subst, [Ty0], [L Exp0])
tcExps ddefs sbst venv fenv bound_tyvars ls = do
  (sbsts,tys,exps) <- unzip3 <$> mapM go ls
  pure (foldl (<>) sbst sbsts, tys, exps)
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars

-- | Algorithm W
tcExp :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar -> L Exp0 -> TcM (Subst, Ty0, L Exp0)
tcExp ddefs sbst venv fenv bound_tyvars e@(L loc ex) = fmap (\(a,b,c) -> (a,b, L loc c)) $
  case ex of
    VarE x -> case M.lookup x venv of
                Nothing -> err $ text "Unbound variable " <> doc x
                Just ty -> do
                  ty_inst <- instantiate ty
                  pure (sbst, ty_inst, ex)

    LitE{}    -> pure (sbst, IntTy, ex)
    LitSymE{} -> pure (sbst, IntTy, ex)

    AppE f tyapps arg -> do
      case (M.lookup f venv, M.lookup f fenv) of
        (Just lam_ty, _) -> do (s2,t2,arg_tc) <- go arg
                               tv <- freshTy
                               lam_ty_inst <- instantiate lam_ty
                               s3 <- unify e (ArrowTy t2 tv) (substTy s2 lam_ty_inst)
                               pure (s2 <> s3, substTy s3 tv, AppE f tyapps arg_tc)
        -- CHECKME
        -- TODO: don't instantiate when typechecking top-level fns
        (_, Just fn_ty)  -> do fn_ty_inst <- instantiate fn_ty
                               (s2,t2, arg_tc) <- go arg
                               tv <- freshTy
                               s3 <- unify e (substTy s2 fn_ty_inst) (ArrowTy t2 tv)
                               -- Specialize this.
                               pure (s2 <> s3, substTy s3 tv, AppE f tyapps arg_tc)
        _ -> err $ text "Unknown function:" <+> doc f

    -- Arguments must have concrete types.
    PrimAppE pr args -> do
      (s1, tys, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars args

      let tys' = map (substTy s1) tys

          checkLen :: Int -> TcM ()
          checkLen n =
            if length args == n
            then pure ()
            else err $ text "Wrong number of arguments to " <+> doc pr <+> text "."
                         $$ text "Expected " <+> doc n
                         <+> text ", received " <+> doc (length args)
                         $$ exp_doc
          len0 = checkLen 0
          len2 = checkLen 2
      case pr of
        _ | pr `elem` [MkTrue, MkFalse] -> do
            len0
            pure (s1, BoolTy, PrimAppE pr args_tc)

        _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP] -> do
            len2
            _ <- ensureEqualTy (args !! 0) IntTy (tys' !! 0)
            _ <- ensureEqualTy (args !! 1) IntTy (tys' !! 1)
            pure (s1, IntTy, PrimAppE pr args_tc)
        oth -> err $ text "PrimAppE : TODO " <+> doc oth

    LetE (v, tyapps, ty, rhs) bod -> do
      (s1,t1,rhs_tc) <- go rhs
      s2 <- unify rhs ty t1
      let s3     = s1 <> s2
          venv'  = substTyEnv s3 venv
          t1_gen = generalize venv' bound_tyvars t1
          -- Generalized with old venv.
          ty_gen = generalize venv bound_tyvars ty
      -- CSK: Disabled temporarily.
      -- s4 <- forallCheck rhs bound_tyvars t1_gen ty_gen
      let s4 = s3
      -- TODO, note.
      let ForAll bind_rhs _ = ty_gen
      (s5,t5,bod_tc) <- tcExp ddefs (s3 <> s4) (M.insert v t1_gen venv') fenv
                          (bound_tyvars <> (S.fromList bind_rhs)) bod
      pure (s4 <> s5, t5, LetE (v, tyapps, ty, rhs_tc) bod_tc)

    IfE a b c -> do
      (s1,t1,a_tc) <- go a
      (s2,t2,b_tc) <- go b
      (s3,t3,c_tc) <- go c
      s4 <- unify a t1 BoolTy
      s5 <- unify e t2 t3
      pure (s1 <> s2 <> s3 <> s4 <> s5, substTy s5 t2, IfE a_tc b_tc c_tc)

    MkProdE es -> do
      (s1, tys, es_tc) <- tcExps ddefs sbst venv fenv bound_tyvars es
      pure (s1, ProdTy tys, MkProdE es_tc)

    ProjE i a -> do
     (s1,t1,a_tc) <- go a
     case substTy s1 t1 of
       ProdTy tys -> pure (s1, tys !! i, ProjE i a_tc)
       t1' -> err $ "tcExp: Coulnd't match expected type: ProdTy [...]"
                      <+> "with actual type: " <+> doc t1'
                      $$ exp_doc

    CaseE scrt brs -> do
      (s1,t1,scrt_tc) <- go scrt
      case t1 of
        (PackedTy tycon drvd_tyargs) -> do
          let tycons_brs = map (getTyOfDataCon ddefs . (\(a,_,_) -> a)) brs
          case nub tycons_brs of
            [one] -> if one == tycon
                     then do
                       let ddf = lookupDDef ddefs tycon
                       ddf' <- substDDef ddf drvd_tyargs
                       (s2,t2,brs_tc) <- tcCases ddefs s1 venv fenv bound_tyvars ddf' brs e
                       pure (s2, t2, CaseE scrt_tc brs_tc)
                     else err $ text "Couldn't match" <+> doc one
                                <+> "with:" <+> doc t1
                                $$ exp_doc
            oth -> err $ text "Case clause constructors have mismatched types:"
                          <+> doc oth
                          $$ exp_doc
        _ -> err $ text "Couldn't match" <+> doc t1
                     <+> "with a Packed type."
                     $$ exp_doc

    DataConE tyapps dcon args -> do
      let expected = lookupDataCon ddefs dcon
      (s1, actual, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars args
      s2 <- unifyl e expected actual
      ty <- instantiateDDef ddefs dcon actual
      -- Specialize this.
      pure (s1 <> s2, ty, DataConE tyapps dcon args_tc)

    Ext (LambdaE (v,ty) bod) -> do
      t1 <- freshTy
      let venv' = M.insert v (ForAll [] t1) venv
      s2 <- unify (l$ VarE v) ty t1
      (s3, t3, bod_tc) <- tcExp ddefs s2 venv' fenv bound_tyvars bod
      return (s3, substTy s3 (ArrowTy t1 t3), Ext (LambdaE (v,ty) bod_tc))

    _ -> err $ "tcExp: TODO" <+> doc ex
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars
    exp_doc = "In the expression: " <+> doc ex


tcCases :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar
        -> DDef0 -> [(DataCon, [(Var, l)], L Exp0)] -> L Exp0
        -> TcM (Subst, Ty0, [(DataCon, [(Var, l)], L Exp0)])
tcCases ddefs sbst venv fenv bound_tyvars ddf brs ex = do
  (s1,tys,exps) <-
    foldlM
      (\(s,acc,ex_acc) (con,vlocs,rhs) -> do
        let vars = map fst vlocs
            tys  = lookupDataCon' ddf con
            tys_gen = map (ForAll (tyArgs ddf \\ (S.toList bound_tyvars))) tys
            venv' = venv <> (M.fromList $ zip vars tys_gen)
        (s2,t2,rhs_tc) <- tcExp ddefs sbst venv' fenv bound_tyvars rhs
        pure (s <> s2, acc ++ [t2], ex_acc ++ [(con,vlocs,rhs_tc)]))
      (sbst, [], [])
      brs
  -- FINISHME (run on incorrect fmapMaybe's)
  let (as,bs) = unzip (pairs tys)
  s2 <- unifyl ex as bs
  let s3 = s1 <> s2
      tys' = map (substTy s3) tys
  -- dbgTraceIt (sdoc (tys,tys')) (pure())
  mapM_ (\(a,b) -> ensureEqualTy ex a b) (pairs tys')
  pure (s3, head tys',exps)
  where
    -- pairs [1,2,3,4,5] = [(1,2), (2,3) (4,5)]
    pairs :: [a] -> [(a,a)]
    pairs []  = []
    pairs [_] = []
    pairs (x:y:xs) = (x,y) : pairs (y:xs)

freshTy :: TcM Ty0
freshTy = TyVar <$> gensym "x"

instantiate :: TyScheme -> TcM Ty0
instantiate (ForAll as ty) = do
  bs <- mapM (fmap TyVar . gensym) as
  let s1 = Subst $ M.fromList (zip as bs)
  pure (substTy s1 ty)

generalize :: Gamma -> S.Set TyVar -> Ty0 -> TyScheme
generalize env bound_tyvars ty =
  let tvs = S.toList $ (gFreeVars ty S.\\ gFreeVars env) S.\\ bound_tyvars
  in ForAll tvs ty

-- Makes (Nothing :: Maybe a), (Right 10 :: Either a Int) etc. happen
instantiateDDef :: DDefs0 -> DataCon -> [Ty0] -> TcM Ty0
instantiateDDef ddefs dcon infrd_tys = do
  let tycon        = getTyOfDataCon ddefs dcon
      DDef{tyArgs} = lookupDDef ddefs tycon

      -- Types with which constructor was defined
      gvn_tys = lookupDataCon ddefs dcon

  -- Given a datatype;
  --
  --     data Either a b = Left a | Right b
  --
  -- and some constructor, build a substituion;
  --
  --     Left  [c] => [ a -> c    , b -> fresh ]
  --     Right [c] => [ a -> fresh, b -> c     ]
  --
  mp <- M.fromList <$> mapM
          (\tyarg -> (tyarg,) <$>
            case elemIndex (TyVar tyarg) gvn_tys of
              Just ix -> pure (infrd_tys !! ix)
              Nothing -> freshTy)
          tyArgs
  let tys = map (mp #) tyArgs
  pure (PackedTy tycon tys)


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
  deriving (Ord, Eq, Read, Show, Generic, Out)

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

-- Substitute tyvars with types in a ddef.
substDDef :: DDef0 -> [Ty0] -> TcM DDef0
substDDef d@DDef{tyArgs,dataCons} tys =
  if length tyArgs /= length tys
  then err $ text "substDDef error."
  else do
    let mp = M.fromList (zip tyArgs tys)
        s  = Subst mp
        dcons' = map
                   (\(dcon,btys) ->
                      let (boxity, tys1) = unzip btys
                          tys1' = map (substTy s) tys1
                      in (dcon, zip boxity tys1'))
                   dataCons
        free_tyvars = concatMap tyVarsInType (M.elems mp)
    pure d { tyArgs   = free_tyvars
           , dataCons = dcons' }


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
        (ProdTy as, ProdTy bs) -> unifyl ex as bs
        (ArrowTy a b, ArrowTy c d) -> do
          s1 <- unify ex a c
          s2 <- unify ex (substTy s1 b) (substTy s1 d)
          pure (s2 <> s1)
        (PackedTy tc1 tys1, PackedTy tc2 tys2) ->
          if tc1 == tc2
          then unifyl ex tys1 tys2
          else err fail_msg
        _ -> err fail_msg
  where fail_msg = text "Couldn't unify:" <+> doc ty1 <+> text "and" <+> doc ty2
                     $$ text "In the expression: "
                     $$ nest 2 (doc ex)


unifyl :: L Exp0 -> [Ty0] -> [Ty0] -> TcM Subst
unifyl _ [] [] = pure emptySubst
unifyl e (a:as) (b:bs) = do
    -- N.B. We must apply s1 over the rest of the list before unifying it, i.e.
    --
    --     (<>) <$> unify e a b <*> unifyl e as bs
    --
    -- doesn't work!
    s1 <- unify e a b
    s2 <- unifyl e (map (substTy s1) as) (map (substTy s1) bs)
    pure (s1 <> s2)
unifyl e as bs = err $ text "Couldn't unify:" <+> doc as <+> text "and" <+> doc bs
                         $$ text "In the expression: "
                         $$ nest 2 (doc e)

unifyTyVar :: L Exp0 -> TyVar -> Ty0 -> TcM Subst
unifyTyVar ex a t
  | occursCheck a t = err $ text "Occurs check: cannot construct the inifinite type: "
                              $$ nest 2 (doc a <+> text " ~ " <+> doc t)
                              $$ text "In the expression: "
                              $$ nest 2 (doc ex)
  | otherwise       = pure $ Subst (M.singleton a t)


{- Note [Unifying type schemes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider this function:

    id :: forall a. a -> a
    id x = 10

This doesn't typecheck in Haskell, but does under this system.
Should we reject this program ? If we only use unification to match
the derived type with the given type, it succeeds, with ( a ~ IntTy ).
We need something stronger than unification but weaker than (==) to
match the types.


Semantics:

    (forall as. t1) ~ (forall bs. t2) under S = { ..., (a -> ty) ,... } iff
    for each (a -> ty) in S, if a is universally quantified then ty must be
    a universally quantified tyvar.

-}
forallCheck :: L Exp0 -> S.Set TyVar -> TyScheme -> TyScheme -> TcM Subst
forallCheck e bound_tyvars x@(ForAll as t1) y@(ForAll bs t2) = do
  s@(Subst mp) <- unify e t1 t2
  let msg :: TyVar -> Ty0 -> TcM ()
      msg a b = err $ text "Couldn't unify:" <+> doc a <+> text "and" <+> doc b
                        $$ text "In the expression: "
                        $$ nest 2 (doc e)
                        $$ text "Which are bound by:"
                        $$ nest 2 (vcat [doc x, doc y])
  forM_ (M.toList mp) $ \(a,ty) ->
    if not (elem a as || elem a bs || elem a bound_tyvars)
    then pure ()
    else do
      case ty of
        TyVar b -> if (elem a as && not (elem b as)) ||
                      (elem a bs && not (elem b bs)) ||
                      (a `S.member` bound_tyvars && not (b `S.member` bound_tyvars))
                   then pure ()
                   else msg a ty
        _ -> msg a ty
  pure s

occursCheck :: TyVar -> Ty0 -> Bool
occursCheck a t = a `S.member` gFreeVars t

--------------------------------------------------------------------------------
-- Other helpers
--------------------------------------------------------------------------------

ensureEqualTy :: L Exp0 -> Ty0 -> Ty0 -> TcM ()
ensureEqualTy ex ty1 ty2
  | ty1 == ty2 = pure ()
  | otherwise  = err $ text "Couldn't match expected type:" <+> doc ty1
                         $$ text "with actual type: " <+> doc ty2
                         $$ text "In the expression: "
                         $$ nest 2 (doc ex)
