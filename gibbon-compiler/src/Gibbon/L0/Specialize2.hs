{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE CPP #-}

{- L0 Specializer (part 2):
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Paulette worked on a specializer which lives in 'Gibbon.L0.Specialize'
and specializes functions on curried calls. Now we need a driver which
takes these different pieces, and puts them together in order to
transform a fully polymorphic L0 program, into a monomorphic L1 program.
This module is the first attempt to do that.

-}

module Gibbon.L0.Specialize2 where

import           Data.Loc
import           Data.Foldable ( foldlM )
import qualified Data.Map as M
import qualified Data.Set as S
import           Text.PrettyPrint.GenericPretty

#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup
#endif

import           Gibbon.Common
import           Gibbon.L0.Syntax
import           Gibbon.L0.Typecheck

--------------------------------------------------------------------------------

{- Transforming L0 to L1 a.k.a. monomorphization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Things that can be polymorphic, and therefore should be specialized:
- top-level fn calls
- lamda functions
- datacons

Here's a rough plan:

(1) Start with main: walk over it, and collect all specialization obligations:

        { [((fn_name, [tyapp]), newname)] , [((lam_name, [tyapp]), newname)] , [((tycon, [tyapp]), newname)] }

    i.e fn_name should be specialized at [tyapp], and it should be named newname.

    While collecting these obligations, just replace all polymorphic things with their
    corresponding new names. It seems like we'll have to traverse an expression twice to
    specialize lambdas; first to collect the required specializations, and one more
    time to define them.

(2) Start specializing toplevel functions, and collect any new obligations
    that may be generated. Repeat (2) until there are no more obls.

(3) Create specialized versions of all datatypes.

(4) Delete all polymorphic fns and datatypes, which should all just be dead code now.

(5) Typecheck monomorphic L0 once more.

(6) Lift lambdas.

(7) Convert to L1, which should be pretty straightforward at this point.

-}

--------------------------------------------------------------------------------

-- Do we need a specialized version of f at [ty1, ty2] ?
data SpecState = SpecState
  { funs_todo :: M.Map (Var, [Ty0]) Var
  , funs_done :: M.Map (Var, [Ty0]) Var
  , lambdas   :: M.Map (Var, [Ty0]) Var
  , datacons  :: M.Map (TyCon, [Ty0]) Var -- suffix
  }
  deriving (Show, Read, Ord, Eq, Generic, Out)

instance Semigroup SpecState where
  (SpecState f1 fd1 l1 d1) <> (SpecState f2 fd2 l2 d2) =
    SpecState  (f1 `M.union` f2) (l1 `M.union` l2) (fd1 `M.union` fd2) (d1 `M.union` d2)

emptySpecState :: SpecState
emptySpecState = SpecState
  { funs_todo = M.empty, funs_done = M.empty
  , lambdas = M.empty, datacons = M.empty }

extendFuns :: (Var,[Ty0]) -> Var -> SpecState -> SpecState
extendFuns k v specs@SpecState{funs_todo} =
  specs { funs_todo = M.insert k v funs_todo }

extendLambdas :: (Var,[Ty0]) -> Var -> SpecState -> SpecState
extendLambdas k v specs@SpecState{lambdas} =
  specs { lambdas = M.insert k v lambdas }

extendDatacons :: (TyCon,[Ty0]) -> Var -> SpecState -> SpecState
extendDatacons k v specs@SpecState{datacons} =
  specs { datacons = M.insert k v datacons }


-- We need this wrapper because of the way these maps are defined.
--
-- getLambdaSpecs id { lambdas = [ ((id,[IntTy]), id1), ((id,[BoolTy]), id2) ] }
--   = [ (id2, [IntTy]), (id2, [BoolTy]) ]
getLambdaSpecs :: Var -> SpecState -> (M.Map Var [Ty0])
getLambdaSpecs f SpecState{lambdas} =
  M.fromList $ map (\((_,tys), w) -> (w, tys)) f_specs
  where
    f_specs = filter (\((v,_), _) -> v == f) (M.toList lambdas)


-- Layering multiple State monads is no fun. Do it by hand instead.
--
-- newtype SpecM a = SpecM (StateT SpecState PassM a)
--   deriving (Functor, Applicative, Monad, MonadState SpecState)

--------------------------------------------------------------------------------

specialize :: Prog0 -> PassM Prog0
specialize p@Prog{ddefs,fundefs,mainExp} = do
  let env2 = Env2 M.empty (M.map funTy fundefs)
  -- Step (1)
  (specs, mainExp') <-
    case mainExp of
      Nothing -> pure (emptySpecState, Nothing)
      Just (e,ty) -> do
        (specs', mainExp')  <- collectSpecs ddefs env2 toplevel emptySpecState e
        (specs'',mainExp'') <- specLambdas specs' mainExp'
        assertLambdasSpecialized specs''
        pure (specs'', Just (mainExp'', ty))
  -- Step (2)
  (specs', fundefs') <- fixpoint specs fundefs
  -- Step (3)
  ddefs' <- specDDefs (M.toList (datacons specs')) ddefs
  pure $ p { ddefs = ddefs', fundefs = fundefs', mainExp =  mainExp' }
  where
    toplevel = M.keysSet fundefs

    -- Specialize functions
    fixpoint :: SpecState -> FunDefs0 -> PassM (SpecState, FunDefs0)
    fixpoint specs fundefs1 =
      if M.null (funs_todo specs)
      then pure (specs, fundefs1)
      else do
        let env21 = Env2 M.empty (M.map funTy fundefs1)
            (((fun_name, tyapps), new_fun_name):rst) = M.toList (funs_todo specs)
            fn@FunDef{funName, funBody} = fundefs # fun_name
            tyvars = tyVarsFromScheme (funTy fn)
        assertSameLength ("While specializing the function: " ++ sdoc funName) tyvars tyapps
        let sbst = Subst $ M.fromList $ zip tyvars tyapps
            funTy' = ForAll [] (substTy sbst (tyFromScheme (funTy fn)))
            funBody' = substExp sbst funBody
            -- Move this obligation from todo to done.
            specs' = specs { funs_done = M.insert (fun_name, tyapps) new_fun_name (funs_done specs)
                           , funs_todo = M.fromList rst }
        -- Collect any more obligations generated due to the specialization
        (specs'', funBody'') <- collectSpecs ddefs env21 toplevel specs' funBody'
        dbgTraceIt (sdoc specs'') (pure ())
        (specs''',funBody''') <- specLambdas specs'' funBody''
        let fn' = fn { funName = new_fun_name, funTy = funTy', funBody = funBody''' }
        fixpoint specs''' (M.insert new_fun_name fn' fundefs1)

    specDDefs :: [((TyCon, [Ty0]), Var)] -> DDefs0 -> PassM DDefs0
    specDDefs [] ddefs1 = pure ddefs1
    specDDefs (((tycon, tyapps), suffix):rst) ddefs1 = do
      let ddf@DDef{tyName,tyArgs,dataCons} = lookupDDef ddefs tycon
      assertSameLength ("In the datacon: " ++ sdoc tyName) tyArgs tyapps
      let tyName' = varAppend tyName suffix
          dataCons' = map
                        (\(dcon,vtys) ->
                          let (vars,tys) = unzip vtys
                              sbst = Subst $ M.fromList (zip tyArgs tyapps)
                              tys' = map (substTy sbst) tys
                              vtys' = zip vars tys'
                          in (dcon ++ fromVar suffix, vtys'))
                        dataCons
          ddefs1' = M.insert tyName' (ddf { tyName = tyName', tyArgs = [], dataCons = dataCons' })  ddefs1
      specDDefs rst ddefs1'

-- After 'specLambdas' runs, (lambdas SpecState) must be empty
assertLambdasSpecialized :: SpecState -> PassM ()
assertLambdasSpecialized SpecState{lambdas} =
  if M.null lambdas
  then pure ()
  else error $ "Expected 0 lambda specialization obligations. Got " ++ sdoc lambdas

assertSameLength :: (Out a, Out b) => String -> [a] -> [b] -> PassM ()
assertSameLength msg as bs =
  if length as /= length bs
  then error $ "assertSameLength: Type applications " ++ sdoc bs ++ " incompatible with the type variables: " ++
               sdoc as ++ msg
  else pure ()

-- | Collect the specializations required to monomorphize this expression.
collectSpecs :: DDefs0 -> Env2 Ty0 -> S.Set Var -> SpecState -> L Exp0 -> PassM (SpecState, L Exp0)
collectSpecs ddefs env2 toplevel specs (L p ex) = fmap (L p) <$>
  case ex of
    VarE{}    -> pure (specs, ex)
    LitE{}    -> pure (specs, ex)
    LitSymE{} -> pure (specs, ex)
    AppE f [] arg -> do
      (specs', arg') <- go specs arg
      pure (specs', AppE f [] arg')
    AppE f tyapps arg -> do
      (specs', arg') <- go specs arg
      if f `S.member` toplevel
      then case (M.lookup (f,tyapps) (funs_done specs), M.lookup (f,tyapps) (funs_todo specs)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let specs'' = extendFuns (f,tyapps) new_name specs'
               pure (specs'', AppE new_name [] arg')
             (Just fn_name, _) -> pure (specs', AppE fn_name [] arg')
             (_, Just fn_name) -> pure (specs', AppE fn_name [] arg')

      -- Why (f,[])? See the special case for let below.
      else case (M.lookup (f,[]) (lambdas specs), M.lookup (f,tyapps) (lambdas specs)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let specs'' = extendLambdas (f,tyapps) new_name specs'
               pure (specs'', AppE new_name [] arg')
             (_,Just lam_name) -> pure (specs', AppE lam_name [] arg')
             (Just lam_name,_) -> pure (specs', AppE lam_name [] arg')
    PrimAppE pr args -> do
      (specs', args') <- collectSpecsl ddefs env2 toplevel specs args
      pure (specs', PrimAppE pr args')
    -- A lambda function that's been passed as an argument --
    -- we don't want to specialize it here. It'll be specialized when
    -- the the outer fn is specialized.
    -- To ensure that (AppE v ...) uses the same name, we add it into specs
    -- s.t. it's new name is same as it's old name.
    LetE (v, [], ty@ArrowTy{}, rhs) bod ->do
      let env2' = (extendVEnv v ty env2)
      case unLoc rhs of
        Ext (LambdaE{}) -> do
          (srhs, rhs') <- go specs rhs
          (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v,[],ty,rhs') bod')
        _ -> do
          let specs' = extendLambdas (v,[]) v specs
          (srhs, rhs') <- go specs' rhs
          (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v, [], ty, rhs') bod')
    LetE (v,[],ty,rhs) bod -> do
      let env2' = (extendVEnv v ty env2)
      (srhs, rhs') <- go specs rhs
      (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
      pure (sbod, LetE (v,[],ty,rhs') bod')
    IfE a b c -> do
      (sa, a') <- go specs a
      (sb, b') <- go sa b
      (sc, c') <- go sb c
      pure (sc, IfE a' b' c')
    MkProdE args -> do
      (sp, args') <- collectSpecsl ddefs env2 toplevel specs args
      pure (sp, MkProdE args')
    ProjE i e -> do
      (sp, e') <- go specs e
      pure (sp, ProjE i e')
    CaseE scrt brs -> do
      case recoverType ddefs env2 scrt of
        PackedTy tycon tyapps -> do
          (suffix, specs'') <-
            case M.lookup (tycon, tyapps) (datacons specs) of
              Nothing -> do
                let DDef{tyArgs} = lookupDDef ddefs tycon
                assertSameLength ("In the expression: " ++ sdoc ex) tyArgs tyapps
                suffix <- gensym "_v"
                let specs' = extendDatacons (tycon, tyapps) suffix specs
                pure (suffix, specs')
              Just suffix -> pure (suffix, specs)
          (sscrt, scrt') <- go specs'' scrt
          (sbrs, brs') <-
            foldlM
              (\(sp, acc) (dcon,vtys,bod) -> do
                (sbod, bod') <- go sp bod
                pure (sbod, acc ++ [(dcon ++ fromVar suffix,vtys,bod')]))
              (sscrt, []) brs
          pure (sbrs, CaseE scrt' brs')

        ty -> error $ "collectSpecs: Unexpected type for the scrutinee, " ++ sdoc ty ++
                      ". In the expression: " ++ sdoc ex
    DataConE (ProdTy tyapps) dcon args -> do
      (sargs, args') <- collectSpecsl ddefs env2 toplevel specs args
      -- Collect datacon instances here.
      let tycon = getTyOfDataCon ddefs dcon
      case M.lookup (tycon, tyapps) (datacons specs) of
        Nothing -> do
          let DDef{tyArgs} = lookupDDef ddefs tycon
          assertSameLength ("In the expression: " ++ sdoc ex) tyArgs tyapps
          suffix <- gensym "_v"
          let specs' = extendDatacons (tycon, tyapps) suffix sargs
              dcon' = dcon ++ (fromVar suffix)
          pure (specs', DataConE (ProdTy []) dcon' args')
        Just suffix -> do
          let dcon' = dcon ++ (fromVar suffix)
          pure (sargs, DataConE (ProdTy []) dcon' args')
    TimeIt e ty b -> do
      (se, e') <- go specs e
      pure (se, TimeIt e' ty b)
    Ext ext ->
      case ext of
        LambdaE (v,ty) bod -> do
          (sbod, bod') <- go specs bod
          pure (sbod, Ext $ LambdaE (v,ty) bod')
        _ -> error ("collectSpecs: TODO, "++ sdoc ext)
    _ -> error ("collectSpecs: TODO, " ++ sdoc ex)
  where
    go = collectSpecs ddefs env2 toplevel

collectSpecsl :: DDefs0 -> Env2 Ty0 -> S.Set Var -> SpecState -> [L Exp0] -> PassM (SpecState, [L Exp0])
collectSpecsl ddefs env2 toplevel specs es = do
  foldlM
    (\(sp, acc) e -> do
          (s,e') <- collectSpecs ddefs env2 toplevel sp e
          pure (s, acc ++ [e']))
    (specs, []) es


-- | Create specialized versions of lambdas bound in this expression.
specLambdas :: SpecState -> L Exp0 -> PassM (SpecState, L Exp0)
-- Assummption: lambdas only appear as RHS in a let.
specLambdas specs (L p ex) = fmap (L p) <$>
  case ex of
    VarE{}    -> pure (specs, ex)
    LitE{}    -> pure (specs, ex)
    LitSymE{} -> pure (specs, ex)
    AppE f tyapps arg ->
      case tyapps of
        [] -> do (specs1, arg') <- go arg
                 pure (specs1, AppE f [] arg')
        _  -> error $ "specLambdas: Expression probably not processed by collectSpecs: " ++ sdoc ex
    PrimAppE pr args -> do (specs1, args') <- specLambdasl specs args
                           pure (specs1, PrimAppE pr args')
    LetE (v,[],vty, rhs@(L p1 (Ext (LambdaE (x,xty) lam_bod)))) bod -> do
      let lam_specs = getLambdaSpecs v specs
      if M.null lam_specs
      -- This lambda is not polymorphic, don't specialize.
      then do
        (specs1, bod') <- go bod
        (specs2, lam_bod') <- specLambdas specs1 lam_bod
        pure (specs2, LetE (v, [], vty, L p1 (Ext (LambdaE (x,xty) lam_bod'))) bod')
      -- Specialize and only bind those, drop the polymorphic defn.
      -- Also drop the specialized already applied from SpecState.
      -- So after 'specLambdas' is done, (lambdas SpecState) should be [].
      else do
        -- new_lam_specs = old_lam_specs - applied_lam_specs
        let new_lam_specs = (lambdas specs) `M.difference`
                              (M.fromList $ map (\(w,wtyapps) -> ((v,wtyapps), w)) (M.toList lam_specs))
            specs' = specs { lambdas =  new_lam_specs }
        (specs1, bod') <- specLambdas specs' bod
        specialized <- specializedLamBinds (M.toList lam_specs) (vty, rhs)
        pure (specs1, unLoc $ foldl (\acc bind -> l$ LetE bind acc) bod' specialized)
    LetE (v,[],ty,rhs) bod -> do
      (specs1, rhs') <- go rhs
      (specs2, bod') <- specLambdas specs1 bod
      pure (specs2, LetE (v, [], ty, rhs') bod')
    IfE a b c -> do
      (specs1, a') <- go a
      (specs2, b') <- specLambdas specs1 b
      (specs3, c') <- specLambdas specs2 c
      pure (specs3, IfE a' b' c')
    MkProdE ls -> do
      (specs1, ls') <- specLambdasl specs ls
      pure (specs1, MkProdE ls')
    ProjE i a  -> do
      (specs1, a') <- go a
      pure (specs1, ProjE i a')
    CaseE scrt brs -> do
      (specs1, scrt') <- go scrt
      (specs2, brs') <-
        foldlM
          (\(sp, acc) (dcon,vlocs,bod) -> do
            (sbod, bod') <- specLambdas sp bod
            pure (sbod, acc ++ [(dcon,vlocs,bod')]))
          (specs1, []) brs
      pure (specs2, CaseE scrt' brs')
    DataConE tyapp dcon args -> do
      (specs1, args') <- specLambdasl specs args
      pure (specs1, DataConE tyapp dcon args')
    TimeIt e ty b -> do
      (specs1, e') <- go e
      pure (specs1, TimeIt e' ty b)
    Ext (LambdaE (v,ty) bod) -> do
      (specs1, bod') <- go bod
      pure (specs1, Ext (LambdaE (v,ty) bod'))
    _ -> error $ "specLambdas: TODO " ++ sdoc ex
  where go = specLambdas specs

        specializedLamBinds :: [(Var,[Ty0])] -> (Ty0, L Exp0) -> PassM [(Var, [Ty0], Ty0, L Exp0)]
        specializedLamBinds [] _ = pure []
        specializedLamBinds ((w, tyapps):rst) (ty,ex1) = do
          let tyvars = tyVarsInType ty
          assertSameLength ("In the expression: " ++ sdoc ex1) tyvars tyapps
          let sbst = Subst $ M.fromList $ zip tyvars tyapps
              ty'  = substTy sbst ty
              ex'  = substExp sbst ex1
          (++ [(w, [], ty', ex')]) <$> specializedLamBinds rst (ty,ex1)

specLambdasl :: SpecState -> [L Exp0] -> PassM (SpecState, [L Exp0])
specLambdasl specs es = do
  foldlM
    (\(sp, acc) e -> do
          (s,e') <- specLambdas sp e
          pure (s, acc ++ [e']))
    (specs, []) es

--------------------------------------------------------------------------------

-- Apply a substitution to an expression i.e substitue all types in it.
substExp :: Subst -> L Exp0 -> L Exp0
substExp s (L p ex) = L p $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f tyapps arg -> let tyapps1 = map (substTy s) tyapps
                         in AppE f tyapps1 (go arg)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    -- Let doesn't store any tyapps.
    LetE (v,tyapps,ty,rhs) bod -> LetE (v, tyapps, substTy s ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map
                        (\(dcon,vtys,rhs) -> let (vars,tys) = unzip vtys
                                                 vtys' = zip vars $ map (substTy s) tys
                                             in (dcon, vtys', go rhs))
                        brs)
    DataConE (ProdTy tyapps) dcon args ->
      DataConE (ProdTy (map (substTy s) tyapps)) dcon (map go args)
    TimeIt e ty b -> TimeIt (go e) (substTy s ty) b
    Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v, substTy s ty) (go bod))
    _ -> error $ "substExp: TODO, " ++ sdoc ex
  where
    go = substExp s
