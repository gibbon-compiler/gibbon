{-# LANGUAGE DeriveAnyClass #-}

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
import           Data.List
import           Data.Foldable ( foldlM )
import qualified Data.Map as M
import qualified Data.Set as S
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.L0.Syntax
import           Gibbon.L0.Typecheck
import qualified Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

{-

Transforming L0 to L1
~~~~~~~~~~~~~~~~~~~~~

(A) Monomorphize
(B) Lift lambdas
(C) Convert to L1, which should be pretty straightforward at this point.



Monomorphization
~~~~~~~~~~~~~~~~

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

(4) After we have all the specialized datatypes, we need to fix TYPEs in (Packed TYPE ..) to
    have the correct suffix. Actually, this could be done in 'collectSpecs', but we do
    it in a separate pass for now.

(5) Delete all polymorphic fns and datatypes, which should all just be dead code now.

(6) Typecheck monomorphic L0 once more.



Lambda lifting
~~~~~~~~~~~~~~

Assume that the input program is monomorphic.

(a) Traverse all expressions in the program (main and functions), and
    float out all lambda definitions to the top-level.

(b) Collect all functions passed in as arguments to other functions.
    E.g.

        foo :: (A -> B) -> A -> B
        main = ... (foo fn1 thing1) ... (foo fn2 thing2) ...

     => [ ((foo, [fn1]), foo_1), ((foo, [fn2]), foo_2), ... ]


(c) (foo fn1) and (foo fn2) would now be separate top-level first order functions:

        foo_1 :: A -> B
        foo_1 thing = ... fn1 thing ...

        foo_2 :: A -> B
        foo_2 thing = ... fn2 thing ...

    Create these functions, drop the lambdas from it's type, arguments etc.

-}

l0ToL1 :: Prog0 -> PassM L1.Prog1
l0ToL1 p = do
  p1 <- monomorphize p
  p2 <- liftLam p1
  pure $ toL1 p2


-- Just a mechanical transformation ..
toL1 :: Prog0 -> L1.Prog1
toL1 Prog{ddefs, fundefs, mainExp} =
   Prog (M.map toL1DDef ddefs) (M.map toL1FunDef fundefs) mainExp'
  where
    mainExp' = case mainExp of
                 Nothing -> Nothing
                 Just (e,ty) -> Just (toL1Exp e, toL1Ty ty)

    toL1DDef :: DDef0 -> L1.DDef1
    toL1DDef ddf@DDef{dataCons} =
      ddf { dataCons = map (\(dcon, btys) -> (dcon, map (\(a,b) -> (a, toL1Ty b)) btys)) dataCons }

    toL1FunDef :: FunDef0 -> L1.FunDef1
    toL1FunDef fn@FunDef{funTy, funBody} =
      fn { funTy = toL1TyS funTy
         , funBody = toL1Exp funBody }

    toL1Exp :: L Exp0 -> L L1.Exp1
    toL1Exp (L p ex) = L p $
      case ex of
        VarE v    -> L1.VarE v
        LitE n    -> L1.LitE n
        LitSymE v -> L1.LitSymE v
        AppE f [] arg    -> AppE f [] (toL1Exp arg)
        PrimAppE pr args -> PrimAppE (toL1Prim pr) (map toL1Exp args)
        LetE (v,[],ty,rhs) bod -> LetE (v,[], toL1Ty ty, toL1Exp rhs) (toL1Exp bod)
        IfE a b c  -> IfE (toL1Exp a) (toL1Exp b) (toL1Exp c)
        MkProdE ls -> MkProdE (map toL1Exp ls)
        ProjE i a  -> ProjE i (toL1Exp a)
        CaseE scrt brs -> CaseE (toL1Exp scrt) (map (\(a,b,c) -> (a,
                                                                  map (\(x,_) -> (x,())) b,
                                                                  toL1Exp c) )
                                                    brs)
        DataConE _ dcon ls -> DataConE () dcon (map toL1Exp ls)
        TimeIt e ty b -> TimeIt (toL1Exp e) (toL1Ty ty) b
        ParE a b      -> ParE (toL1Exp a) (toL1Exp b)
        Ext{} -> err1 (sdoc ex)
        _ -> error $ "toL1Exp: TODO" ++ sdoc ex

    toL1Prim :: Prim Ty0 -> Prim L1.Ty1
    toL1Prim = fmap toL1Ty

    toL1Ty :: Ty0 -> L1.Ty1
    toL1Ty ty =
      case ty of
        IntTy   -> L1.IntTy
        BoolTy  -> L1.BoolTy
        TyVar{} -> err1 (sdoc ty)
        MetaTv{} -> err1 (sdoc ty)
        ProdTy tys  -> L1.ProdTy $ map toL1Ty tys
        SymDictTy a -> L1.SymDictTy $ toL1Ty a
        ArrowTy{} -> err1 (sdoc ty)
        PackedTy tycon tyapps | tyapps == [] -> L1.PackedTy tycon ()
                              | otherwise    -> err1 (sdoc ty)
        ListTy{} -> error $ "toL1Ty: No ListTy in L1."

    toL1TyS :: ArrowTy Ty0 -> ArrowTy L1.Ty1
    toL1TyS t@(ForAll tyvars (ArrowTy a b))
      | tyvars == [] = (toL1Ty a, toL1Ty b)
      | otherwise    = err1 (sdoc t)
    toL1TyS (ForAll _ t) = error $ "toL1: Not a function type: " ++ sdoc t

    err1 msg = error $ "toL1: Program was not fully monomorphized. Encountered" ++ msg

--------------------------------------------------------------------------------

data SpecState = SpecState
  { sp_funs_todo :: M.Map (Var, [Ty0]) Var
  , sp_funs_done :: M.Map (Var, [Ty0]) Var
  , sp_lams      :: M.Map (Var, [Ty0]) Var
  , sp_dcons     :: M.Map (TyCon, [Ty0]) Var -- suffix
  }
  deriving (Show, Read, Ord, Eq, Generic, Out)

emptySpecState :: SpecState
emptySpecState = SpecState
  { sp_funs_todo = M.empty, sp_funs_done = M.empty
  , sp_lams = M.empty, sp_dcons = M.empty }

extendFuns :: (Var,[Ty0]) -> Var -> SpecState -> SpecState
extendFuns k v specs@SpecState{sp_funs_todo} =
  specs { sp_funs_todo = M.insert k v sp_funs_todo }

extendLambdas :: (Var,[Ty0]) -> Var -> SpecState -> SpecState
extendLambdas k v specs@SpecState{sp_lams} =
  specs { sp_lams = M.insert k v sp_lams }

extendDatacons :: (TyCon,[Ty0]) -> Var -> SpecState -> SpecState
extendDatacons k v specs@SpecState{sp_dcons} =
  specs { sp_dcons = M.insert k v sp_dcons }


-- We need this wrapper because of the way these maps are defined.
--
-- getLambdaSpecs id { sp_lams = [ ((id,[IntTy]), id1), ((id,[BoolTy]), id2) ] }
--   = [ (id2, [IntTy]), (id2, [BoolTy]) ]
getLambdaSpecs :: Var -> SpecState -> (M.Map Var [Ty0])
getLambdaSpecs f SpecState{sp_lams} =
  M.fromList $ map (\((_,tys), w) -> (w, tys)) f_specs
  where
    f_specs = filter (\((v,_), _) -> v == f) (M.toList sp_lams)


-- Layering multiple State monads is no fun. Do it by hand instead.
--
-- newtype SpecM a = SpecM (StateT SpecState PassM a)
--   deriving (Functor, Applicative, Monad, MonadState SpecState)

--------------------------------------------------------------------------------

monomorphize :: Prog0 -> PassM Prog0
monomorphize p@Prog{ddefs,fundefs,mainExp} = do
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
  (specs', fundefs') <- specFunDefs specs fundefs
  -- Step (3)
  ddefs' <- specDDefs specs' ddefs
  let p1 = p { ddefs = ddefs', fundefs = fundefs', mainExp =  mainExp' }
  -- Step (4)
  let p2 = purgePolyFuns p1
      p3 = updateTyCons specs' p2
  -- Step (5)
  let p4 = purgePolyDDefs p3
  -- Step (6)
  p5 <- tcProg p4
  pure p5
  where
    toplevel = M.keysSet fundefs

    specFunDefs :: SpecState -> FunDefs0 -> PassM (SpecState, FunDefs0)
    specFunDefs specs fundefs1 =
      if M.null (sp_funs_todo specs)
      then pure (specs, fundefs1)
      else do
        let env21 = Env2 M.empty (M.map funTy fundefs1)
            (((fun_name, tyapps), new_fun_name):rst) = M.toList (sp_funs_todo specs)
            fn@FunDef{funName, funBody} = fundefs # fun_name
            tyvars = tyVarsFromScheme (funTy fn)
        assertSameLength ("While specializing the function: " ++ sdoc funName) tyvars tyapps
        let mp = M.fromList $ zip tyvars tyapps
            funTy' = ForAll [] (substTyVar mp (tyFromScheme (funTy fn)))
            funBody' = substTyVarExp mp funBody
            -- Move this obligation from todo to done.
            specs' = specs { sp_funs_done = M.insert (fun_name, tyapps) new_fun_name (sp_funs_done specs)
                           , sp_funs_todo = M.fromList rst }
        -- Collect any more obligations generated due to the specialization
        (specs'', funBody'') <- collectSpecs ddefs env21 toplevel specs' funBody'
        (specs''',funBody''') <- specLambdas specs'' funBody''
        let fn' = fn { funName = new_fun_name, funTy = funTy', funBody = funBody''' }
        specFunDefs specs''' (M.insert new_fun_name fn' fundefs1)

    specDDefs :: SpecState -> DDefs0 -> PassM DDefs0
    specDDefs specs ddefs1 =
      if M.null (sp_dcons specs)
      then pure ddefs1
      else do
        let (((tycon, tyapps), suffix):rst) = M.toList (sp_dcons specs)
            ddf@DDef{tyName,tyArgs,dataCons} = lookupDDef ddefs tycon
        assertSameLength ("In the datacon: " ++ sdoc tyName) tyArgs tyapps
        let tyName' = varAppend tyName suffix
            dataCons' = map
                          (\(dcon,vtys) ->
                            let (vars,tys) = unzip vtys
                                sbst = M.fromList (zip tyArgs tyapps)
                                tys' = map (substTyVar sbst) tys
                                tys'' = map (updateTyConsTy ddefs1 specs) tys'
                                vtys' = zip vars tys''
                            in (dcon ++ fromVar suffix, vtys'))
                          dataCons
            ddefs1' = M.insert tyName' (ddf { tyName = tyName', tyArgs = [], dataCons = dataCons' })  ddefs1
            specs'  = specs { sp_dcons = M.fromList rst }
        specDDefs specs' ddefs1'

-- After 'specLambdas' runs, (sp_lams SpecState) must be empty
assertLambdasSpecialized :: SpecState -> PassM ()
assertLambdasSpecialized SpecState{sp_lams} =
  if M.null sp_lams
  then pure ()
  else error $ "Expected 0 lambda specialization obligations. Got " ++ sdoc sp_lams

assertSameLength :: (Out a, Out b, Monad m) => String -> [a] -> [b] -> m ()
assertSameLength msg as bs =
  if length as /= length bs
  then error $ "assertSameLength: Type applications " ++ sdoc bs ++ " incompatible with the type variables: " ++
               sdoc as ++ ".\n " ++ msg
  else pure ()

-- | Collect the specializations required to monomorphize this expression.
collectSpecs :: DDefs0 -> Env2 Ty0 -> S.Set Var -> SpecState -> L Exp0 -> PassM (SpecState, L Exp0)
collectSpecs ddefs env2 toplevel specs (L p ex) = fmap (L p) <$>
  case ex of
    AppE f [] arg -> do
      (specs', arg') <- go specs arg
      pure (specs', AppE f [] arg')
    AppE f tyapps arg -> do
      (specs', arg') <- go specs arg
      if f `S.member` toplevel
      then case (M.lookup (f,tyapps) (sp_funs_done specs), M.lookup (f,tyapps) (sp_funs_todo specs)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let specs'' = extendFuns (f,tyapps) new_name specs'
               pure (specs'', AppE new_name [] arg')
             (Just fn_name, _) -> pure (specs', AppE fn_name [] arg')
             (_, Just fn_name) -> pure (specs', AppE fn_name [] arg')

      -- Why (f,[])? See the special case for let below.
      else case (M.lookup (f,[]) (sp_lams specs), M.lookup (f,tyapps) (sp_lams specs)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let specs'' = extendLambdas (f,tyapps) new_name specs'
               pure (specs'', AppE new_name [] arg')
             (_,Just lam_name) -> pure (specs', AppE lam_name [] arg')
             (Just lam_name,_) -> pure (specs', AppE lam_name [] arg')

    LetE (v, [], ty@ArrowTy{}, rhs) bod ->do
      let env2' = (extendVEnv v ty env2)
      case unLoc rhs of
        Ext (LambdaE{}) -> do
          (srhs, rhs') <- go specs rhs
          (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v,[],ty,rhs') bod')
        _ -> do
          -- If it's not a lambda defn, it's been passed as an argument --
          -- we don't want to specialize it here. It'll be specialized when
          -- the the outer fn is specialized.
          -- To ensure that (AppE v ...) uses the same name, we add it into
          -- specs s.t. it's new name is same as it's old name.
          let specs' = extendLambdas (v,[]) v specs
          (srhs, rhs') <- go specs' rhs
          (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v, [], ty, rhs') bod')

    LetE (v,[],ty,rhs) bod -> do
      let env2' = (extendVEnv v ty env2)
      (srhs, rhs') <- go specs rhs
      (sbod, bod') <- collectSpecs ddefs env2' toplevel srhs bod
      pure (sbod, LetE (v,[],ty,rhs') bod')

    CaseE scrt brs -> do
      case recoverTy ddefs env2 scrt of
        PackedTy tycon tyapps -> do
          (suffix, specs'') <-
            case M.lookup (tycon, tyapps) (sp_dcons specs) of
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
      case M.lookup (tycon, tyapps) (sp_dcons sargs) of
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

    PrimAppE pr args -> do
      (specs', args') <- collectSpecsl ddefs env2 toplevel specs args
      pure (specs', PrimAppE pr args')

    -- Straightforward recursion
    VarE{}    -> pure (specs, ex)
    LitE{}    -> pure (specs, ex)
    LitSymE{} -> pure (specs, ex)
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
      -- So after 'specLambdas' is done, (sp_lams SpecState) should be [].
      else do
        -- new_lam_specs = old_lam_specs - applied_lam_specs
        let new_lam_specs = (sp_lams specs) `M.difference`
                              (M.fromList $ map (\(w,wtyapps) -> ((v,wtyapps), w)) (M.toList lam_specs))
            specs' = specs { sp_lams =  new_lam_specs }
        (specs1, bod') <- specLambdas specs' bod
        specialized <- specializedLamBinds (M.toList lam_specs) (vty, rhs)
        pure (specs1, unLoc $ foldl (\acc bind -> l$ LetE bind acc) bod' specialized)

    -- Straightforward recursion
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
          let tyvars = tyVarsInTy ty
          assertSameLength ("In the expression: " ++ sdoc ex1) tyvars tyapps
          let mp = M.fromList $ zip tyvars tyapps
              ty'  = substTyVar mp ty
              ex'  = substTyVarExp mp ex1
          (++ [(w, [], ty', ex')]) <$> specializedLamBinds rst (ty,ex1)

specLambdasl :: SpecState -> [L Exp0] -> PassM (SpecState, [L Exp0])
specLambdasl specs es = do
  foldlM
    (\(sp, acc) e -> do
          (s,e') <- specLambdas sp e
          pure (s, acc ++ [e']))
    (specs, []) es


-- | Remove all polymorphic functions and datatypes from a program. 'specLambdas'
-- already gets rid of polymorphic sp_lams.
purgePolyFuns :: Prog0 -> Prog0
purgePolyFuns p@Prog{fundefs} =
  p { fundefs = M.filter isMonoFun fundefs }
  where
    isMonoFun FunDef{funTy} = (tyVarsFromScheme funTy) == []

purgePolyDDefs :: Prog0 -> Prog0
purgePolyDDefs p@Prog{ddefs} =
  p { ddefs = M.filter isMonoDDef ddefs }
  where
    isMonoDDef DDef{tyArgs} = tyArgs == []

-- See Step (4) in the big note. Lot of code duplication :(
updateTyCons :: SpecState -> Prog0 -> Prog0
updateTyCons specs p@Prog{ddefs, fundefs,mainExp}=
  let fundefs' = M.map fixFunDef fundefs
      mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (e,ty) -> Just (updateTyConsExp ddefs specs e, updateTyConsTy ddefs specs ty)
  in p { fundefs = fundefs', mainExp = mainExp' }
  where
    fixFunDef :: FunDef0 -> FunDef0
    fixFunDef fn@FunDef{funTy, funBody} =
      let funTy' = ForAll (tyVarsFromScheme funTy) (updateTyConsTy ddefs specs (tyFromScheme funTy))
          funBody' = updateTyConsExp ddefs specs funBody
      in fn { funTy = funTy', funBody = funBody' }

-- |
updateTyConsExp :: DDefs0 ->  SpecState -> L Exp0 -> L Exp0
updateTyConsExp ddefs specs (L loc ex) = L loc $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f [] arg -> AppE f [] (go arg)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    LetE (v,[],ty,rhs) bod -> LetE (v, [], updateTyConsTy ddefs specs ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map
                        (\(dcon,vtys,rhs) -> let (vars,tys) = unzip vtys
                                                 vtys' = zip vars $ map (updateTyConsTy ddefs specs) tys
                                             in (dcon, vtys', go rhs))
                        brs)
    DataConE (ProdTy tyapps) dcon args ->
      let tyapps' = map (updateTyConsTy ddefs specs) tyapps
          tycon   = getTyOfDataCon ddefs dcon
          dcon' = case M.lookup (tycon,tyapps') (sp_dcons specs) of
                    Nothing     -> dcon
                    Just suffix -> dcon ++ fromVar suffix
      -- Why [] ? The type arguments aren't required as the DDef is monomorphic.
      in DataConE (ProdTy []) dcon' (map go args)
    TimeIt e ty b -> TimeIt (go e) (updateTyConsTy ddefs specs ty) b
    Ext (LambdaE (v,ty) bod) -> Ext (LambdaE (v, updateTyConsTy ddefs specs ty) (go bod))
    _ -> error $ "updateTyConsExp: TODO, " ++ sdoc ex
  where
    go = updateTyConsExp ddefs specs

-- | Update TyCons if an appropriate specialization obligation exists.
updateTyConsTy :: DDefs0 -> SpecState -> Ty0 -> Ty0
updateTyConsTy ddefs specs ty =
  case ty of
    IntTy   -> IntTy
    BoolTy  -> BoolTy
    TyVar{} ->  error $ "updateTyConsTy: " ++ sdoc ty ++ " shouldn't be here."
    MetaTv{} -> error $ "updateTyConsTy: " ++ sdoc ty ++ " shouldn't be here."
    ProdTy tys  -> ProdTy (map go tys)
    SymDictTy t -> SymDictTy (go t)
    ArrowTy a b -> ArrowTy (go a) (go b)
    PackedTy t tys ->
      let tys' = map go tys
      in case M.lookup (t,tys') (sp_dcons specs) of
           Nothing     -> PackedTy t tys'
           -- Why [] ? The type arguments aren't required as the DDef is monomorphic.
           Just suffix -> PackedTy (t ++ fromVar suffix) []
    ListTy t -> ListTy (go t)
  where
    go = updateTyConsTy ddefs specs

--------------------------------------------------------------------------------

data LowerState = LowerState
  { lo_funs_todo :: M.Map (Var, [Var]) Var
  , lo_fundefs   :: FunDefs0 }
  deriving (Show, Eq)


-- We track references when we bind variables to account for programs like:
--
--     foo :: ((a -> b), a) -> a ; foo = ...
--     main = ... arg = (fn, thing) ... foo arg ...
--
-- type FnRefsEnv = M.Map Var FnRefs
--

type FnRefs    = [Var]


liftLam :: Prog0 -> PassM Prog0
liftLam prg@Prog{ddefs,fundefs,mainExp} = do
  let env2 = progToEnv prg
  (low, mainExp') <-
    case mainExp of
      Nothing -> pure (emptyLowerState, Nothing)
      Just (e, ty) -> do
        (low', e') <- liftLamExp ddefs env2 emptyLowerState e
        pure (low', Just (e', ty))
  low' <- fixpoint low
  -- Get rid of all higher order functions.
  let fundefs' = purgeHO (lo_fundefs low')
      prg' = prg { mainExp = mainExp', fundefs = fundefs' }
  -- Typecheck again.
  tcProg prg'
  where
    emptyLowerState :: LowerState
    emptyLowerState = LowerState M.empty fundefs

    -- Lower functions
    fixpoint :: LowerState -> PassM LowerState
    fixpoint low = do
      if M.null (lo_funs_todo low)
      then pure low
      else do
        let fns = lo_fundefs low
            fn = fns # fn_name
            ((fn_name, refs), new_fn_name) = M.elemAt 0 (lo_funs_todo low)
        low' <- elimLamFun ddefs low (progToEnv prg) new_fn_name refs fn
        let low'' = low' { lo_funs_todo = M.deleteAt 0 (lo_funs_todo low') }
        fixpoint low''

    purgeHO :: FunDefs0 -> FunDefs0
    purgeHO fns = M.filter isHOFun fns

    isHOFun :: FunDef0 -> Bool
    isHOFun FunDef{funTy} =
      let ForAll _ (ArrowTy arg_ty ret_ty) = funTy
      in arrowTysInTy arg_ty == [] &&
         arrowTysInTy ret_ty == []

-- Eliminate all lambdas passed in as arguments to a function.
elimLamFun :: DDefs0 -> LowerState -> Env2 Ty0 -> Var -> FnRefs -> FunDef0 -> PassM LowerState
elimLamFun ddefs low env2 new_fn_name refs fn@FunDef{funArg, funTy} = do
  let fn' = fn { funName = new_fn_name
               , funBody = elimExp drop_projs update_projs (funBody fn) }
  (low', funBody') <- liftLamExp ddefs env2 low (funBody fn')
  let fn''  = fn' { funBody = funBody'
                  -- Only update the type after 'liftLamExp' runs!
                  , funTy   = funTy' }
      low'' = low' { lo_fundefs = M.insert new_fn_name fn'' (lo_fundefs low') }
  pure low''
  where
    ForAll tyvars (ArrowTy arg_ty ret_ty) = funTy
    -- First order type
    funTy' = ForAll tyvars (ArrowTy (first_order_ty arg_ty) (first_order_ty ret_ty))

    first_order_ty :: Ty0 -> Ty0
    first_order_ty t =
      case t of
        -- we only hit this case in a function which takes a single lambda argument:
        --
        --    foo :: (a -> b)
        --    foo f = _
        --
        -- Since functions must take atleast one argument, we make it an int.
        -- The type we use here must match the expression used in 'dropFunRefs'.
        ArrowTy{} -> IntTy
        -- We just drop all ArrowTy's.
        ProdTy tys -> ProdTy $ filter (not . isFunTy) tys
        _ -> t

    (drop_projs, update_projs, _) =
      splitProjs (l$ VarE funArg) (l$ VarE funArg) (inTy funTy)

    -- Some tuple surgery code.
    -- Assume flat tuples. TODO: Write a L0 pass that ensures this.
    --
    -- ( projections_to_eliminate, projection_substitutions )
    --
    --     splitProjs arg (a, fn_ty, a)
    -- ==> ([arg !! 1], [(arg !! 0, arg !! 0), (arg !! 2, arg !! 1)])
    splitProjs :: L Exp0 -> L Exp0 -> Ty0 -> ([L Exp0], [(L Exp0, L Exp0)], Int)
    splitProjs = go ([], [], 0)
      where
        go (elim, sbst, offset) e1 e2 ty =
         -- TODO, docs.
         -- e2 always trails behind e1 by offset.
          case ty of
            ArrowTy{} -> (elim ++ [e1], sbst, offset-1)
            ProdTy tys ->
              foldl
                (\(elim', sbst', offset') (ty',n) ->
                   go (elim', sbst', offset') (mkProj n e1) (mkProj (n+offset') e2) ty')
                (elim, sbst, offset)
                (zip tys [0..])
            _ -> (elim, sbst ++ [(e1, e2)], offset)

    elimExp :: [L Exp0] -> [(L Exp0, L Exp0)] -> L Exp0 -> L Exp0
    elimExp drop_projs1 update_projs1 (L p ex) = L p $
      case ex of
        LetE (v, [], ty, rhs) bod ->
          case rhs `elemIndex` drop_projs1 of
            Nothing ->
              case lookup rhs update_projs1 of
                 Nothing   -> LetE (v, [], ty, go rhs) (go bod)
                 -- Update RHS.
                 Just rhs' -> LetE (v, [], ty, rhs') (go bod)
            -- Drop this let binding.
            Just ix -> let bod' = subst' v (refs !! ix) bod
                       in unLoc (go bod')

        -- straightforward recursion.
        VarE{}    -> ex
        LitE{}    -> ex
        LitSymE{} -> ex
        AppE f [] arg -> AppE f [] (go arg)
        PrimAppE pr args -> PrimAppE pr $ map go args
        IfE a b c  -> IfE (go a) (go b) (go c)
        MkProdE ls -> MkProdE $ map go ls
        ProjE i a  -> ProjE i (go a)
        CaseE scrt brs -> CaseE (go scrt) (map (\(a,b,c) -> (a,b,) $ go c) brs)
        DataConE tyapp dcon args -> DataConE tyapp dcon $ map go args
        TimeIt e ty b -> TimeIt (go e) ty b
        _ -> error $ "eliminate: TODO " ++ sdoc ex
      where
        go = elimExp drop_projs1 update_projs1

    -- | Update a function name.
    subst' :: Var -> Var -> L Exp0 -> L Exp0
    subst' old new (L p0 ex) = L p0 $
      let go = subst' old new in
      case ex of
        VarE v | v == old  -> VarE new
               | otherwise -> VarE v
        AppE f [] e | f == old  -> AppE new [] (go e)
                     | otherwise -> AppE f [] (go e)
        LitE _             -> ex
        LitSymE _          -> ex
        PrimAppE p ls      -> PrimAppE p $ map go ls
        LetE (v,[],t,rhs) bod | v == old  -> LetE (v,[],t,go rhs) bod
                               | otherwise -> LetE (v,[],t,go rhs) (go bod)
        ProjE i e  -> ProjE i (go e)
        CaseE e ls -> CaseE (go e) (map f ls)
                          where f (c,vs,er) = if elem old (map fst vs)
                                              then (c,vs,er)
                                              else (c,vs,go er)
        MkProdE ls        -> MkProdE $ map go ls
        DataConE loc k ls -> DataConE loc k $ map go ls
        TimeIt e t b      -> TimeIt (go e) t b
        IfE a b c         -> IfE (go a) (go b) (go c)
        ParE a b          -> ParE (go a) (go b)
        _ -> error $ "subst': TODO " ++ sdoc ex


liftLamExp :: DDefs0 -> Env2 Ty0 -> LowerState -> L Exp0
           -> PassM (LowerState, L Exp0)
liftLamExp ddefs env2 low (L p ex) = fmap (L p) <$>
  case ex of
    -- TODO, docs.
    AppE f [] arg -> do
      (low', arg') <- go arg
      let arg'' = dropFunRefs f arg'
      case collectFunRefs arg [] of
        []   -> pure (low, AppE f [] arg')
        refs -> do
          case M.lookup (f,refs) (lo_funs_todo low') of
            Nothing -> do
              f' <- gensym f
              let ForAll _ (ArrowTy a _) = lookupFEnv f env2
                  arrow_tys = arrowTysInTy a
              -- Check that the # of refs we collected actually matches the #
              -- of functions 'f' expects.
              assertSameLength ("While lowering the expression " ++ sdoc ex) refs arrow_tys
              -- We have a new lowering obligation.
              let low'' = low' { lo_funs_todo = M.insert (f,refs) f' (lo_funs_todo low') }
              pure (low'', AppE f' [] arg'')
            Just f' -> pure (low', AppE f' [] arg'')

    -- Float out a lambda fun to the top-level.
    LetE (v, [], ty, L _ (Ext (LambdaE (arg, _arg_ty) lam_bod))) bod -> do
      let captured_vars = gFreeVars lam_bod `S.difference` (S.singleton arg)
      if not (S.null captured_vars)
      then error $ "liftLamExp: LamdaE captures variables: "
                   ++ show captured_vars
                   ++ ". TODO: these can become additional arguments."
      else do
        (low', lam_bod') <- go lam_bod
        let fn_refs = collectFunRefs lam_bod []
            fn = FunDef { funName = v
                        , funArg  = arg
                        , funTy   = ForAll [] ty
                        , funBody = lam_bod' }
            env2' = extendFEnv v (ForAll [] ty) env2
            low'' = low' { lo_fundefs = M.insert v fn (lo_fundefs low') }
        fmap unLoc <$> liftLamExp ddefs env2' low'' bod

    LetE (v, [], ty, rhs) bod -> do
      let fn_refs = collectFunRefs rhs []
          env2' = (extendVEnv v ty env2)
      (low', rhs') <- go rhs
      (low'', bod') <- liftLamExp ddefs env2' low' bod
      pure (low'', LetE (v, [], ty, rhs') bod')

    -- Straightforward recursion
    VarE{}    -> pure (low, ex)
    LitE{}    -> pure (low, ex)
    LitSymE{} -> pure (low, ex)
    PrimAppE pr args -> do
      (low', args') <- gol args
      pure (low', PrimAppE pr args')
    IfE a b c -> do
      (low', [a',b',c']) <- gol [a,b,c]
      pure (low', IfE a' b' c')
    MkProdE ls -> do
      (low', ls') <- gol ls
      pure (low', MkProdE ls')
    ProjE i a -> do
      (low',a') <- go a
      pure (low', ProjE i a')
    CaseE scrt brs -> do
      let es = map (\(_,_,c) -> c) brs
      (low', scrt') <- go scrt
      (low'', es') <- liftLamExpl ddefs env2 low' es
      pure (low'', CaseE scrt' $ map (\((a,b,_), c) -> (a,b,c)) (zip brs es'))
    DataConE tyapp dcon args -> do
      (low', args') <- gol args
      pure (low', DataConE tyapp dcon args')
    TimeIt e ty b -> do
       (low', e') <- go e
       pure (low', TimeIt e' ty b)
    _ -> error $ "liftLamExp: TODO " ++ sdoc ex
  where
    go = liftLamExp ddefs env2 low
    gol = liftLamExpl ddefs env2 low

    isFunRef e =
      case e of
        VarE v -> M.member v (fEnv env2)
        _ -> False

    -- fn_0 (fn_1, thing, fn_2) => fn_0 (thing)
    dropFunRefs :: Var -> L Exp0 -> L Exp0
    dropFunRefs fn_name (L p1 arg) = L p1 $
      case arg_ty of
        ProdTy tys ->
          case arg of
            -- The simple case.
            MkProdE ls -> if length ls == length tys
                          then MkProdE $ foldr
                                           (\(a,t) acc ->
                                             if isFunTy t
                                             then acc
                                             else a : acc)
                                           [] (zip ls tys)
                          else error $ "dropFunRefs: " ++ sdoc arg
                                       ++ " does not match " ++ sdoc arg_ty
            _ -> error $ "dropFunRefs: TODO " ++ sdoc arg
        -- See 'first_order_ty' for details.
        ArrowTy{} -> LitE 1
        _ -> arg
      where
        ForAll _ (ArrowTy arg_ty _) = lookupFEnv fn_name env2

    collectFunRefs :: L Exp0 -> [Var] -> [Var]
    collectFunRefs (L _ e) acc =
      case e of
        VarE v -> if isFunRef e
                  then v : acc
                  else acc
        LitE{}     -> acc
        LitSymE{}  -> acc
        AppE _ _ a -> collectFunRefs a acc
        PrimAppE _ args -> foldr collectFunRefs acc args
        LetE (_,_,_, rhs) bod -> foldr collectFunRefs acc [bod, rhs]
        IfE a b c  -> foldr collectFunRefs acc [c, b, a]
        MkProdE ls -> foldr collectFunRefs acc ls
        ProjE _ a  -> collectFunRefs a acc
        DataConE _ _ ls -> foldr collectFunRefs acc ls
        TimeIt a _ _ -> collectFunRefs a acc
        _ -> error $ "collectFunRefs: TODO " ++ sdoc e

liftLamExpl :: DDefs0 -> Env2 Ty0 -> LowerState -> [L Exp0]
            -> PassM (LowerState, [L Exp0])
liftLamExpl ddefs env2 low exs =
  foldlM
    (\(st, acc) e ->
       do (st', e') <- go st e
          pure (st', acc ++ [e']))
    (low, [])
    exs
  where
    go = liftLamExp ddefs env2
