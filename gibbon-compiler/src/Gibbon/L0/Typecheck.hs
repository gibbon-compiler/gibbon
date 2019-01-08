{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

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

#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup
#endif

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
                Just (e,gvn_main_ty) -> do
                  let tc = do (s1, drvd_main_ty, e_tc) <-
                                tcExp ddefs emptySubst M.empty init_fenv S.empty AfterLetrec e
                              s2 <- unify e gvn_main_ty drvd_main_ty
                              let e_tc' = fixTyApps s1 e_tc
                              pure (s1 <> s2, substTy s2 drvd_main_ty, e_tc')
                  res <- runTcM tc
                  case res of
                    Left er -> error (render er)
                    Right (_s, ty, e_tc) -> pure $ Just (e_tc, ty)
  pure prg { fundefs = fundefs_tc
           , mainExp = mainExp' }

{-

Consider this program:

    f :: forall a b. a -> b
    f = ... g ...

    g = forall c d. c -> d
    g = ... f ...

    main = ... f ... g ...

All the top-level functions are like a giant letrec, which may later
be used in the 'main' expression too. When typechecking main, we set the
type of f to some instance of it's principal type, i.e the type of f is,

    f :: forall fresh1 fresh2. fresh1 -> fresh2

However, while typechecking the letrec (fns), all occurences of f within the
RHS must have the same type. 'TcPhase' allows us to identify which phase of
the typechecking process we're in. We don't worry about shadowing
type variables; assume that 'Freshen' has already done it's job.

-}
data TcPhase = DuringLetrec | AfterLetrec
  deriving Eq

shouldInstantiate :: TcPhase -> Bool
shouldInstantiate DuringLetrec = False
shouldInstantiate AfterLetrec  = True

tcFun :: DDefs0 -> Gamma -> FunDef0 -> PassM FunDef0
tcFun ddefs fenv fn@FunDef{funArg,funTy,funBody} = do
  res <- runTcM $ do
    let (ForAll tyvars (ArrowTy gvn_arg_ty gvn_retty)) = funTy
        --
        --    ($) :: forall a b. ((a -> b), a) -> b
        --    ($) arg = let f :: (a -> b)
        --                  f = fst arg
        --              in ...
        --
        -- In this program, we wan't a and b to be bound in the body.
        -- We do 2 things to achieve this - (1) initialize Gamma with
        -- (arg :: forall []. a -> b), and, (2) add {a,b} to the bound set.
        -- Also see Note [Let generalization].
        init_venv = M.singleton funArg (ForAll [] gvn_arg_ty)
        init_s    = Subst $ M.singleton funArg gvn_arg_ty
        bound_tyvars = S.fromList tyvars
    (s1, drvd_funBody_ty, funBody_tc) <-
      tcExp ddefs init_s init_venv fenv bound_tyvars DuringLetrec funBody
    s2 <- unify funBody drvd_funBody_ty gvn_retty

    -- Forall check is disabled.
    --
    -- TL;DR - doesn't work properly with ADTs.
    --
    -- Right now, Nothing has a type (Nothing :: forall fresh. Maybe fresh).
    -- We want to be able to typecheck an expression (Nothing :: Maybe Int).
    -- But the forallCheck won't allow it. FIXME.
    --
    -- Also see Note [Forall check].
    let _ty1_gen = ForAll tyvars (ArrowTy gvn_arg_ty drvd_funBody_ty)
    -- s <- forallCheck funBody (S.fromList tyvars) ty1_gen funTy
    --
    let funBody_tc' = fixTyApps (s1 <> s2) funBody_tc
    pure (s1 <> s2, funBody_tc')
  case res of
    Left er -> error $ render er
    Right (_,bod) -> pure $ fn { funBody = bod }

tcExps :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar -> TcPhase
       -> [L Exp0] -> TcM (Subst, [Ty0], [L Exp0])
tcExps ddefs sbst venv fenv bound_tyvars phase ls = do
  (sbsts,tys,exps) <- unzip3 <$> mapM go ls
  pure (foldl (<>) sbst sbsts, tys, exps)
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars phase

-- | Algorithm W
tcExp :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar -> TcPhase
      -> L Exp0 -> TcM (Subst, Ty0, L Exp0)
tcExp ddefs sbst venv fenv bound_tyvars phase e@(L loc ex) = (\(a,b,c) -> (a,b, L loc c)) <$>
  case ex of
    VarE x -> case (M.lookup x venv, M.lookup x fenv) of
                (Nothing, Nothing) -> err $ text "Unbound variable " <> doc x
                (Just ty, _) -> (sbst, ,ex) <$> instantiate ty
                (_, Just ty) -> (sbst, ,ex) <$> instantiate ty

    LitE{}    -> pure (sbst, IntTy, ex)
    LitSymE{} -> pure (sbst, IntTy, ex)

    AppE f _tyapps arg -> do
      -- (fn_ty_inst) :: (TyScheme, Ty0)
      fn_ty_inst <- case (M.lookup f venv, M.lookup f fenv) of
                      (Just lam_ty, _) -> do
                        lam_ty_inst <- instantiate lam_ty
                        pure lam_ty_inst
                      (_, Just fn_ty)  -> do
                        fn_ty_inst <- if shouldInstantiate phase
                                      then instantiate fn_ty         -- freshen tyvars
                                      else pure (tyFromScheme fn_ty) -- return as is
                        pure fn_ty_inst
                      _ -> err $ text "Unknown function:" <+> doc f
      (s2, arg_ty, arg_tc) <- go arg
      fresh <- freshTy
      s3 <- unify e (ArrowTy arg_ty fresh) (substTy s2 fn_ty_inst)

      -- Fill in type applications for specialization...
      --     id 10 ===> id [Int] 10
      s4@(Subst specs) <- unify arg (arrIn' fn_ty_inst) arg_ty
      -- 'tyVarsInType' has to be used to compute the list of type variables again.
      -- We can't get it via 'let (ForAll tyvars _) = fn_ty', as this list might be
      -- empty if f is a lambda. See Note [Let generalization].
      let tyvars  = tyVarsInType fn_ty_inst
          tyapps1 = map (\tv -> M.findWithDefault (TyVar tv) tv specs) tyvars

      pure (s2 <> s4 <> s3, substTy (s2 <> s3) fresh, AppE f tyapps1 arg_tc)

    -- Arguments must have concrete types.
    PrimAppE pr args -> do
      (s1, arg_tys, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars phase args

      let arg_tys' = map (substTy s1) arg_tys

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
            _ <- ensureEqualTy (args !! 0) IntTy (arg_tys' !! 0)
            _ <- ensureEqualTy (args !! 1) IntTy (arg_tys' !! 1)
            pure (s1, IntTy, PrimAppE pr args_tc)
        oth -> err $ text "PrimAppE : TODO " <+> doc oth

    -- tyapps == [], always.
    LetE (v, tyapps, gvn_rhs_ty, rhs) bod -> do
      (s1, drvd_rhs_ty, rhs_tc) <- go rhs
      s2 <- unify rhs gvn_rhs_ty drvd_rhs_ty
      let s3         = s1 <> s2
          venv'      = substTyEnv s3 venv
          rhs_ty_gen = generalize venv' bound_tyvars drvd_rhs_ty
          venv''     = M.insert v rhs_ty_gen venv'

      -- Disabled temporarily, see comments in tcFun.
      -- let ty_gen = generalize venv' bound_tyvars ty
      -- s4 <- forallCheck rhs bound_tyvars rhs_ty_gen ty_gen

      (s5, bod_ty, bod_tc) <- tcExp ddefs s3 venv'' fenv bound_tyvars phase bod
      pure (s3 <> s5, bod_ty, LetE (v, tyapps, gvn_rhs_ty, rhs_tc) bod_tc)

    IfE a b c -> do
      (s1, t1, a_tc) <- go a
      (s2, t2, b_tc) <- go b
      (s3, t3, c_tc) <- go c
      s4 <- unify a t1 BoolTy
      s5 <- unify e t2 t3
      pure (s1 <> s2 <> s3 <> s4 <> s5, substTy s5 t2, IfE a_tc b_tc c_tc)

    MkProdE es -> do
      (s1, es_tys, es_tc) <- tcExps ddefs sbst venv fenv bound_tyvars phase es
      pure (s1, ProdTy es_tys, MkProdE es_tc)

    ProjE i a -> do
     (s1, a_ty, a_tc) <- go a
     case substTy s1 a_ty of
       ProdTy tys -> pure (s1, tys !! i, ProjE i a_tc)
       a_ty' -> err $ "tcExp: Coulnd't match expected type: ProdTy [...]"
                      <+> "with actual type: " <+> doc a_ty'
                      $$ exp_doc

    CaseE scrt brs -> do
      (s1, scrt_ty, scrt_tc) <- go scrt
      case scrt_ty of
        (PackedTy tycon drvd_tyargs) -> do
          let tycons_brs = map (getTyOfDataCon ddefs . (\(a,_,_) -> a)) brs
          case nub tycons_brs of
            [one] -> if one == tycon
                     then do
                       let ddf = lookupDDef ddefs tycon
                       ddf' <- substDDef ddf drvd_tyargs
                       (s2,t2,brs_tc) <- tcCases ddefs s1 venv fenv bound_tyvars phase ddf' brs e
                       pure (s2, t2, CaseE scrt_tc brs_tc)
                     else err $ text "Couldn't match" <+> doc one
                                <+> "with:" <+> doc scrt_ty
                                $$ exp_doc
            oth -> err $ text "Case clause constructors have mismatched types:"
                          <+> doc oth
                          $$ exp_doc
        _ -> err $ text "Couldn't match" <+> doc scrt_ty
                     <+> "with a Packed type."
                     $$ exp_doc

    DataConE _tyapps dcon args -> do
      let expected_tys = lookupDataCon ddefs dcon
      (s1, actual_tys, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars phase args
      s2 <- unifyl e expected_tys actual_tys
      (tyapps1, ty) <- dataconTyApps ddefs dcon actual_tys
      -- DataConE is defined to take a single tyapp (or a loc really),
      -- but we want a list of tyapps here; so we use ProdTy.
      let s3 = s1 <> s2
          tyapps2 = ProdTy (map (substTy s3) tyapps1)
      pure (s3, ty, DataConE tyapps2 dcon args_tc)

    Ext (LambdaE (v,ty) bod) -> do
      fresh <- freshTy
      let venv' = M.insert v (ForAll [] fresh) venv
      s2 <- unify (l$ VarE v) ty fresh
      (s3, bod_ty, bod_tc) <- tcExp ddefs s2 venv' fenv bound_tyvars phase bod
      return (s3, substTy s3 (ArrowTy fresh bod_ty), Ext (LambdaE (v,ty) bod_tc))

    _ -> err $ "tcExp: TODO" <+> doc ex
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars phase
    exp_doc = "In the expression: " <+> doc ex


tcCases :: DDefs0 -> Subst -> Gamma -> Gamma -> S.Set TyVar -> TcPhase
        -> DDef0 -> [(DataCon, [(Var, l)], L Exp0)] -> L Exp0
        -> TcM (Subst, Ty0, [(DataCon, [(Var, Ty0)], L Exp0)])
tcCases ddefs sbst venv fenv bound_tyvars phase ddf brs ex = do
  (s1,tys,exps) <-
    foldlM
      (\(s,acc,ex_acc) (con,vtys,rhs) -> do
        let vars = map fst vtys
            tys  = lookupDataCon' ddf con
            tys_gen = map (ForAll (tyArgs ddf \\ (S.toList bound_tyvars))) tys
            venv' = venv <> (M.fromList $ zip vars tys_gen)
            vtys' = zip vars tys
        (s2, t2, rhs_tc) <- tcExp ddefs sbst venv' fenv bound_tyvars phase rhs
        pure (s <> s2, acc ++ [t2], ex_acc ++ [(con,vtys',rhs_tc)]))
      (sbst, [], [])
      brs
  -- CHECKME (run on incorrect fmapMaybe's)
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
freshTy = TyVar <$> gensym "fresh"

instantiate :: TyScheme -> TcM Ty0
instantiate (ForAll as ty) = do
  bs <- mapM (fmap TyVar . gensym) as
  let s1 = Subst $ M.fromList (zip as bs)
  pure (substTy s1 ty)


{- Note [Let generalization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Similar to the usual HM style generalization, but doesn't quantify any
type variables already in scope.

    ($) :: forall a b. ((a -> b), a) -> b
    ($) arg = let f :: (a -> b)
                  f = fst arg
              in ...

f will be generalized as (f :: forall []. a -> b), since a and b are bound by
the top-level signature.

-}
generalize :: Gamma -> S.Set TyVar -> Ty0 -> TyScheme
generalize env bound_tyvars ty =
  let tvs = S.toList $ (gFreeVars ty S.\\ gFreeVars env) S.\\ bound_tyvars
  in ForAll tvs ty

-- Makes (Nothing :: Maybe a), (Right 10 :: Either a Int) etc. happen
dataconTyApps :: DDefs0 -> DataCon -> [Ty0] -> TcM ([Ty0], Ty0)
dataconTyApps ddefs dcon inferred_tys = do
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
              Just ix -> pure (inferred_tys !! ix)
              Nothing -> freshTy)
          tyArgs
  -- Type applications for specialization...
  let tys = map (mp #) tyArgs
  pure (tys, PackedTy tycon tys)


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

--
fixTyApps :: Subst -> L Exp0 -> L Exp0
fixTyApps s (L p ex) = L p $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f tyapps arg -> let tyapps1 = map (substTy s) tyapps
                         in AppE f tyapps1 (go arg)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    -- Let doesn't store any tyapps.
    LetE (v,tyapps,ty,rhs) bod -> LetE (v, tyapps,ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map (\(dcon,vtys,rhs) -> (dcon, vtys, go rhs)) brs)
    DataConE (ProdTy tyapps) dcon args ->
      DataConE (ProdTy (map (substTy s) tyapps)) dcon (map go args)
    TimeIt e ty b -> TimeIt (go e) ty b
    Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v,ty) (go bod))
    _ -> error $ "fixTyApps: TODO, " ++ sdoc ex
  where
    go = fixTyApps s

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


{- Note [Forall check]
~~~~~~~~~~~~~~~~~~~~~~

Consider this function:

    id :: forall a. a -> a
    id x = 10

This doesn't typecheck in Haskell, but does under this system.
Should we reject this program ? If we only use unification,
( (a -> a) ~ (a -> IntTy) ), it succeeds, with ( a ~ IntTy ).
We need something stronger than unification but weaker than (==) to
reject such programs.

Semantics:

    (forall as. t1) ~ (forall bs. t2) under S = { ..., (a -> ty) ,... } iff
    for each (a -> ty) in S, if a is universally quantified then ty must be
    a universally quantified tyvar.

FIXME: This is probably not the proper way to do it.
It causes some problems with ADTs, see some comments in tcFun.

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
