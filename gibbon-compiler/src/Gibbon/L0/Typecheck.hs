{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

module Gibbon.L0.Typecheck where

import           Control.Monad.State ( MonadState )
import           Control.Monad.Except
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
                                tcExp ddefs emptySubst M.empty init_fenv [] e
                              s2 <- unify e gvn_main_ty drvd_main_ty
                              -- let e_tc' = fixTyApps s1 e_tc
                              pure (s1 <> s2, zonkTy s2 drvd_main_ty, e_tc)
                  res <- runTcM tc
                  case res of
                    Left er -> error (render er)
                    Right (_s, ty, e_tc) -> pure $ Just (e_tc, ty)
  pure prg { fundefs = fundefs_tc
           , mainExp = mainExp' }

tcFun :: DDefs0 -> Gamma -> FunDef0 -> PassM FunDef0
tcFun ddefs fenv fn@FunDef{funArg,funTy,funBody} = do
  res <- runTcM $ do
    let (ForAll tyvars (ArrowTy gvn_arg_ty gvn_retty)) = funTy
        init_venv = M.singleton funArg (ForAll [] gvn_arg_ty)
        init_s = emptySubst
    (s1, drvd_funBody_ty, funBody_tc) <-
      tcExp ddefs init_s init_venv fenv tyvars funBody
    s2 <- unify funBody drvd_funBody_ty gvn_retty
    pure $ fn { funTy   = zonkTyScheme (s1 <> s2) funTy
              , funBody = zonkExp (s1 <> s2) funBody_tc }
  case res of
    Left er   -> error $ render er
    Right fn1 -> pure fn1

tcExps :: DDefs0 -> Subst -> Gamma -> Gamma -> [TyVar]
       -> [L Exp0] -> TcM (Subst, [Ty0], [L Exp0])
tcExps ddefs sbst venv fenv bound_tyvars ls = do
  (sbsts,tys,exps) <- unzip3 <$> mapM go ls
  pure (foldl (<>) sbst sbsts, tys, exps)
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars

--
tcExp :: DDefs0 -> Subst -> Gamma -> Gamma -> [TyVar]
      -> L Exp0 -> TcM (Subst, Ty0, L Exp0)
tcExp ddefs sbst venv fenv bound_tyvars e@(L loc ex) = (\(a,b,c) -> (a,b, L loc c)) <$>
  case ex of
    VarE x -> case (M.lookup x venv, M.lookup x fenv) of
                (Nothing, Nothing) -> err $ text "Unbound variable " <> doc x
                (Just ty, _) -> (sbst, ,ex) <$> snd <$> instantiate ty
                (_, Just ty) -> (sbst, ,ex) <$> snd <$> instantiate ty

    LitE{}    -> pure (sbst, IntTy, ex)
    LitSymE{} -> pure (sbst, IntTy, ex)

    AppE f _tyapps arg -> do
      (metas, fn_ty_inst) <-
        case (M.lookup f venv, M.lookup f fenv) of
          (Just lam_ty, _) -> instantiate lam_ty
          (_, Just fn_ty)  -> instantiate fn_ty
          _ -> err $ text "Unknown function:" <+> doc f
      (s2, arg_ty, arg_tc) <- go arg
      let fn_ty_inst' = zonkTy s2 fn_ty_inst
      s3 <- unify arg (arrIn' fn_ty_inst') arg_ty
      fresh <- newMetaTy
      s4 <- unify e (ArrowTy arg_ty fresh) fn_ty_inst'
      -- Fill in type applications for specialization...
      --     id 10 ===> id [Int] 10
      let tyapps = map (zonkTy s3) metas
          s5 = s2 <> s3 <> s4
      pure (s5, zonkTy s5 fresh, AppE f tyapps (zonkExp s5 arg_tc))

    PrimAppE pr args -> do
      (s1, arg_tys, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars args

      let arg_tys' = map (zonkTy s1) arg_tys
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
            s2 <- unify (args !! 0) IntTy (arg_tys' !! 0)
            s3 <- unify (args !! 1) IntTy (arg_tys' !! 1)
            pure (s1 <> s2 <> s3, IntTy, PrimAppE pr args_tc)

        _ | pr `elem` [EqIntP, LtP, GtP, LtEqP, GtEqP, OrP, AndP] -> do
          len2
          s2 <- unify (args !! 0) IntTy (arg_tys' !! 0)
          s3 <- unify (args !! 1) IntTy (arg_tys' !! 1)
          pure (s1 <> s2 <> s3, BoolTy, PrimAppE pr args_tc)

        oth -> err $ text "PrimAppE : TODO " <+> doc oth

    LetE (v, [], gvn_rhs_ty, rhs) bod -> do
      (s1, drvd_rhs_ty, rhs_tc) <- go rhs
      --dbgTraceIt (sdoc (s1, gvn_rhs_ty, drvd_rhs_ty)) (pure ())
      s2 <- unify rhs gvn_rhs_ty drvd_rhs_ty
      let s3         = s1 <> s2
          venv'      = zonkTyEnv s3 venv
          -- Added b/c Nothing :: Just Int
          drvd_rhs_ty' = zonkTy s3 drvd_rhs_ty
      (s4, rhs_ty_gen) <- generalize venv' s3 drvd_rhs_ty'
      let venv''     = M.insert v rhs_ty_gen venv'
      (s5, bod_ty, bod_tc) <- tcExp ddefs s4 venv'' fenv bound_tyvars bod
      pure (s5, bod_ty,
            LetE (v, [], zonkTy s4 gvn_rhs_ty, zonkExp s4 rhs_tc) (zonkExp s5 bod_tc))

    IfE a b c -> do
      (s1, t1, a_tc) <- go a
      (s2, t2, b_tc) <- tcExp ddefs s1 venv fenv bound_tyvars b
      (s3, t3, c_tc) <- tcExp ddefs s2 venv fenv bound_tyvars c
      s4 <- unify a t1 BoolTy
      s5 <- unify e t2 t3
      let s6 = s3 <> s4 <> s5
      pure (s6, zonkTy s6 t2,
            IfE (zonkExp s6 a_tc) (zonkExp s6 b_tc) (zonkExp s6 c_tc))

    MkProdE es -> do
      (s1, es_tys, es_tc) <- tcExps ddefs sbst venv fenv bound_tyvars es
      pure (s1, ProdTy es_tys, MkProdE es_tc)

    ProjE i a -> do
     (s1, a_ty, a_tc) <- go a
     case zonkTy s1 a_ty of
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
                       ddf' <- substTyVarDDef ddf drvd_tyargs
                       (s2,t2,brs_tc) <- tcCases ddefs s1 venv fenv bound_tyvars ddf' brs e
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
      (metas, arg_tys_inst, ret_ty_inst) <- instDataConTy ddefs dcon
      (s1, arg_tys, args_tc) <- tcExps ddefs sbst venv fenv bound_tyvars args
      s2 <- unifyl e arg_tys_inst arg_tys
      let s3 = s1 <> s2
          tyapps = ProdTy (map (zonkTy s3) metas)
      pure (s3, zonkTy s3 ret_ty_inst,
            DataConE tyapps dcon (map (zonkExp s3) args_tc))

    Ext (LambdaE (v,ty) bod) -> do
      fresh <- newMetaTy
      let venv' = M.insert v (ForAll [] fresh) venv
      s2 <- unify (l$ VarE v) ty fresh
      let s3 = sbst <> s2
      (s4, bod_ty, bod_tc) <- tcExp ddefs s3 venv' fenv bound_tyvars bod
      return (s4, zonkTy s4 (ArrowTy fresh bod_ty),
              Ext (LambdaE (v, zonkTy s4 ty) (zonkExp s4 bod_tc)))

    _ -> err $ "tcExp: TODO" <+> doc ex
  where
    go = tcExp ddefs sbst venv fenv bound_tyvars
    exp_doc = "In the expression: " <+> doc ex


tcCases :: DDefs0 -> Subst -> Gamma -> Gamma -> [TyVar]
        -> DDef0 -> [(DataCon, [(Var, Ty0)], L Exp0)] -> L Exp0
        -> TcM (Subst, Ty0, [(DataCon, [(Var, Ty0)], L Exp0)])
tcCases ddefs sbst venv fenv bound_tyvars ddf brs ex = do
  (s1,tys,exps) <-
    foldlM
      (\(s,acc,ex_acc) (con,vtys,rhs) -> do
        let vars = map fst vtys
            tys  = lookupDataCon' ddf con
            tys_gen = map (ForAll (tyArgs ddf \\ bound_tyvars)) tys
            venv' = venv <> (M.fromList $ zip vars tys_gen)
            vtys' = zip vars tys
        (s', rhs_ty, rhs_tc) <- tcExp ddefs s venv' fenv bound_tyvars rhs
        let rhs_ty' = zonkTy s' rhs_ty
            rhs_tc' = zonkExp s' rhs_tc
        pure (s', acc ++ [rhs_ty'], ex_acc ++ [(con,vtys',rhs_tc')]))
      (sbst, [], [])
      brs
  let (as,bs) = unzip (pairs tys)
  s2 <- unifyl ex as bs
  let s3 = s1 <> s2
      tys' = map (zonkTy s3) tys
  mapM_ (\(a,b) -> ensureEqualTy ex a b) (pairs tys')
  pure (s3, head tys',exps)
  where
    -- pairs [1,2,3,4,5] = [(1,2), (2,3) (4,5)]
    pairs :: [a] -> [(a,a)]
    pairs []  = []
    pairs [_] = []
    pairs (x:y:xs) = (x,y) : pairs (y:xs)

-- | Instantiate the topmost for-alls of the argument type with meta
-- type variables.
instantiate :: TyScheme -> TcM ([Ty0], Ty0)
instantiate (ForAll tvs ty) = do
  tvs' <- mapM (\_ -> newMetaTy) tvs
  let ty' = substTyVar (M.fromList $ zip tvs tvs') ty
  pure (tvs', ty')

-- TODO: ScopedTypeVariables.
generalize :: Gamma -> Subst -> Ty0 -> TcM (Subst, TyScheme)
generalize env s ty = do
  new_bndrs <- mapM
                 (\(Meta i) -> do
                       v' <- varAppend <$> genLetter <*> pure (toVar $ "_" ++ show i)
                       pure $ BoundTv v')
                 meta_tvs
  let s2 = Subst $ M.fromList (zip meta_tvs (map TyVar new_bndrs))
      ty' = zonkTy (s <> s2) ty
  pure (s <> s2, ForAll new_bndrs ty')
  where
    env_tvs = metaTvsInTySchemes (M.elems env)
    res_tvs = metaTvsInTy ty

    meta_tvs :: [MetaTv]
    meta_tvs = res_tvs \\ env_tvs

--
instDataConTy :: DDefs0 -> DataCon -> TcM ([Ty0], [Ty0], Ty0)
instDataConTy ddefs dcon = do
  let tycon = getTyOfDataCon ddefs dcon
      ddf   = lookupDDef ddefs tycon
      arg_tys = lookupDataCon ddefs dcon
  -- Given a datatype;
  --
  --     data Either a b = Left a | Right b
  --
  -- and some constructor, build a substituion;
  --
  --     Left  [c] => [ a -> c    , b -> fresh ]
  --     Right [c] => [ a -> fresh, b -> c     ]
  --
  tyArgs' <- mapM (\tyarg ->
                if (TyVar tyarg) `elem` arg_tys
                then pure (TyVar tyarg)
                else newMetaTy)
             (tyArgs ddf)
  (env1, tyArgs'') <- tyVarToMetaTyl tyArgs'
  (_env2, arg_tys_inst) <- tyVarToMetaTyl (map (substTyVar env1) arg_tys)
  let ret_ty_inst = PackedTy tycon tyArgs''
  pure (tyArgs'', arg_tys_inst, ret_ty_inst)


--------------------------------------------------------------------------------
-- Type environment
--------------------------------------------------------------------------------

-- We can't directly use Env2 because of the way it's tied together with
-- PreExp and the Expression class. We want to annotate L0 expressions
-- with 'Ty0' but Gamma should store 'TyScheme's.
type Gamma = TyEnv TyScheme

instance FreeVars a => FreeVars (TyEnv a) where
  gFreeVars env = foldr (S.union . gFreeVars) S.empty (M.elems env)

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

newtype Subst = Subst (M.Map MetaTv Ty0)
  deriving (Ord, Eq, Read, Show, Generic, Out)

instance Semigroup Subst where
  -- s1 <> s2 == zonkTy s1 . zonkTy s2
  (Subst s1) <> (Subst s2) =
    let mp = M.map (zonkTy (Subst s1)) s2 `M.union` s1
    in Subst mp

emptySubst :: Subst
emptySubst = Subst (M.empty)

-- | Perform substitutions in the type.
zonkTy :: Subst -> Ty0 -> Ty0
zonkTy s@(Subst mp) ty =
  case ty of
    IntTy   -> ty
    BoolTy  -> ty
    TyVar{} -> ty
    MetaTv v -> case M.lookup v mp of
                  Nothing -> MetaTv v
                  Just t  -> zonkTy s t
    ProdTy tys  -> ProdTy (map go tys)
    SymDictTy t -> SymDictTy (go t)
    ArrowTy a b -> ArrowTy (go a) (go b)
    PackedTy t tys -> PackedTy t (map go tys)
    ListTy t -> ListTy (go t)
  where
    go = zonkTy s

zonkTyScheme :: Subst -> TyScheme -> TyScheme
zonkTyScheme s (ForAll tvs ty) = ForAll tvs (zonkTy s ty)

zonkTyEnv :: Subst -> Gamma -> Gamma
zonkTyEnv s env = M.map (zonkTyScheme s) env

-- Apply a substitution to an expression i.e substitue all types in it.
zonkExp :: Subst -> L Exp0 -> L Exp0
zonkExp s (L p ex) = L p $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f tyapps arg -> let tyapps1 = map (zonkTy s) tyapps
                         in AppE f tyapps1 (go arg)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    -- Let doesn't store any tyapps.
    LetE (v,tyapps,ty,rhs) bod -> LetE (v, tyapps, zonkTy s ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map
                        (\(dcon,vtys,rhs) -> let (vars,tys) = unzip vtys
                                                 vtys' = zip vars $ map (zonkTy s) tys
                                             in (dcon, vtys', go rhs))
                        brs)
    DataConE (ProdTy tyapps) dcon args ->
      DataConE (ProdTy (map (zonkTy s) tyapps)) dcon (map go args)
    TimeIt e ty b -> TimeIt (go e) (zonkTy s ty) b
    Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v, zonkTy s ty) (go bod))
    _ -> error $ "zonkExp: TODO, " ++ sdoc ex
  where
    go = zonkExp s

-- Substitute tyvars with types in a ddef.
substTyVarDDef :: DDef0 -> [Ty0] -> TcM DDef0
substTyVarDDef d@DDef{tyArgs,dataCons} tys =
  if length tyArgs /= length tys
  then err $ text "substTyVarDDef: tyArgs don't match the tyapps, in "
               <+> doc tyArgs <+> text ", " <+> doc tys
  else do
    let mp = M.fromList (zip tyArgs tys)
        dcons' = map
                   (\(dcon,btys) ->
                      let (boxity, tys1) = unzip btys
                          tys1' = map (substTyVar mp) tys1
                      in (dcon, zip boxity tys1'))
                   dataCons
        free_tyvars =  concatMap tyVarsInTy (M.elems mp)
    pure d { tyArgs   = free_tyvars
           , dataCons = dcons' }

-- Substitue all tyvars in an expression.
substTyVarExp :: M.Map TyVar Ty0 -> L Exp0 -> L Exp0
substTyVarExp s (L p ex) = L p $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f tyapps arg -> let tyapps1 = map (substTyVar s) tyapps
                         in AppE f tyapps1 (go arg)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    -- Let doesn't store any tyapps.
    LetE (v,tyapps,ty,rhs) bod -> LetE (v, tyapps, substTyVar s ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map
                        (\(dcon,vtys,rhs) -> let (vars,tys) = unzip vtys
                                                 vtys' = zip vars $ map (substTyVar s) tys
                                             in (dcon, vtys', go rhs))
                        brs)
    DataConE (ProdTy tyapps) dcon args ->
      DataConE (ProdTy (map (substTyVar s) tyapps)) dcon (map go args)
    TimeIt e ty b -> TimeIt (go e) (substTyVar s ty) b
    Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v, substTyVar s ty) (go bod))
    _ -> error $ "substTyVarExp: TODO, " ++ sdoc ex
  where
    go = substTyVarExp s

-- | Replace the specified quantified type variables by
-- given meta type variables.
substTyVar :: M.Map TyVar Ty0 -> Ty0 -> Ty0
substTyVar mp ty =
  case ty of
    IntTy    -> ty
    BoolTy   -> ty
    TyVar v  -> M.findWithDefault ty v mp
    MetaTv{} -> ty
    ProdTy tys  -> ProdTy (map go tys)
    SymDictTy t -> SymDictTy (go t)
    ArrowTy a b -> ArrowTy (go a) (go b)
    PackedTy t tys -> PackedTy t (map go tys)
    ListTy t -> ListTy (go t)
  where
    go = substTyVar mp

tyVarToMetaTyl :: [Ty0] -> TcM (M.Map TyVar Ty0, [Ty0])
tyVarToMetaTyl tys =
  foldlM
    (\(env', acc) ty -> do
            (env'', ty') <- tyVarToMetaTy ty
            pure (env' <> env'', acc ++ [ty']))
    (M.empty, [])
    tys

-- | Replace the specified quantified type variables by
-- given meta type variables.
tyVarToMetaTy :: Ty0 -> TcM (M.Map TyVar Ty0, Ty0)
tyVarToMetaTy = go M.empty
  where
    go :: M.Map TyVar Ty0 -> Ty0 -> TcM (M.Map TyVar Ty0, Ty0)
    go env ty =
     case ty of
       IntTy    -> pure (env, ty)
       BoolTy   -> pure (env, ty)
       TyVar v  -> do mty <- newMetaTy
                      pure (M.insert v mty env, mty)
       MetaTv{} -> pure (env, ty)
       ProdTy tys -> do (env', tys') <- gol env tys
                        pure (env', ProdTy tys')
       SymDictTy t -> do (env', t') <- go env t
                         pure (env', SymDictTy t')
       ArrowTy a b -> do (env', [a',b']) <- gol env [a,b]
                         pure (env', ArrowTy a' b')
       PackedTy t tys -> do (env', tys') <- gol env tys
                            pure (env', PackedTy t tys')
       ListTy t -> do (env', t') <- go env t
                      pure (env', ListTy t')

    gol :: M.Map TyVar Ty0 -> [Ty0] -> TcM (M.Map TyVar Ty0, [Ty0])
    gol env tys = foldlM
                     (\(env', acc) ty -> do
                         (env'', ty') <- go env' ty
                         pure (env'', acc ++ [ty']))
                     (env, [])
                     tys

-- --
-- fixTyApps :: Subst -> L Exp0 -> L Exp0
-- fixTyApps s (L p ex) = L p $
--   case ex of
--     VarE{}    -> ex
--     LitE{}    -> ex
--     LitSymE{} -> ex
--     AppE f tyapps arg -> let tyapps1 = map (zonkTy s) tyapps
--                          in AppE f tyapps1 (go arg)
--     PrimAppE pr args  -> PrimAppE pr (map go args)
--     -- Let doesn't store any tyapps.
--     LetE (v,tyapps,ty,rhs) bod -> LetE (v, tyapps,ty, go rhs) (go bod)
--     IfE a b c  -> IfE (go a) (go b) (go c)
--     MkProdE ls -> MkProdE (map go ls)
--     ProjE i e  -> ProjE i (go e)
--     CaseE scrt brs ->
--       CaseE (go scrt) (map (\(dcon,vtys,rhs) -> (dcon, vtys, go rhs)) brs)
--     DataConE (ProdTy tyapps) dcon args ->
--       DataConE (ProdTy (map (zonkTy s) tyapps)) dcon (map go args)
--     TimeIt e ty b -> TimeIt (go e) ty b
--     Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v,ty) (go bod))
--     _ -> error $ "fixTyApps: TODO, " ++ sdoc ex
--   where
--     go = fixTyApps s

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

unify :: L Exp0 -> Ty0 -> Ty0 -> TcM Subst
unify ex ty1 ty2
  | ty1 == ty2 = --dbgTraceIt (sdoc ty1 ++ "/" ++ sdoc ty2) $
                 pure emptySubst
  | otherwise  = -- dbgTraceIt (sdoc ty1 ++ "/" ++ sdoc ty2) $
      case (ty1,ty2) of
        (IntTy, IntTy)     -> pure emptySubst
        (BoolTy, BoolTy)   -> pure emptySubst
        (TyVar _, TyVar _)   -> fail_
        -- CHECKME:
        -- (MetaTv _, MetaTv _) -> fail_
        (MetaTv a, _) -> unifyVar ex a ty2
        (_, MetaTv b) -> unifyVar ex b ty1
        (ProdTy as, ProdTy bs) -> unifyl ex as bs
        (ArrowTy a b, ArrowTy c d) -> do
          s1 <- unify ex a c
          s2 <- unify ex (zonkTy s1 b) (zonkTy s1 d)
          pure (s2 <> s1)
        (PackedTy tc1 tys1, PackedTy tc2 tys2) ->
          if tc1 == tc2
          then unifyl ex tys1 tys2
          else fail_
        _ -> fail_
  where fail_ = err $  text "Couldn't match type" <+> quotes (doc ty2)
                    <+> text "with" <+> quotes (doc ty1)
                    $$ text "Expected type:" <+> doc ty1
                    $$ text "Actual type:" <+> doc ty2
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
    s2 <- unifyl e (map (zonkTy s1) as) (map (zonkTy s1) bs)
    pure (s1 <> s2)
unifyl e as bs = err $ text "Couldn't unify:" <+> doc as <+> text "and" <+> doc bs
                         $$ text "In the expression: "
                         $$ nest 2 (doc e)

unifyVar :: L Exp0 -> MetaTv -> Ty0 -> TcM Subst
unifyVar ex a t
  | occursCheck a t = err $ text "Occurs check: cannot construct the inifinite type: "
                              $$ nest 2 (doc a <+> text " ~ " <+> doc t)
                              $$ text "In the expression: "
                              $$ nest 2 (doc ex)
  | otherwise       = pure $ Subst (M.singleton a t)


occursCheck :: MetaTv -> Ty0 -> Bool
occursCheck a t = a `elem` metaTvsInTy t

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
