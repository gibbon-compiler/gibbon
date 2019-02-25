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
import           Data.Foldable ( foldlM )
import qualified Data.Map as M
import qualified Data.Set as S
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.Pretty
import           Gibbon.L0.Syntax
import           Gibbon.L0.Typecheck
import qualified Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

{-

Transforming L0 to L1
~~~~~~~~~~~~~~~~~~~~~

(A) Monomorphization
(B) Lambda lifting
(C) Convert to L1, which should be pretty straightforward at this point.



Monomorphization
~~~~~~~~~~~~~~~~

Things that can be polymorphic, and therefore should be monormorphized:
- top-level fn calls
- lamda functions
- datacons

Here's a rough plan:

(1) Start with main: walk over it, and collect all monomorphization obligations:

        { [((fn_name, [tyapp]), newname)] , [((lam_name, [tyapp]), newname)] , [((tycon, [tyapp]), newname)] }

    i.e fn_name should be monomorphized at [tyapp], and it should be named newname.

    While collecting these obligations, just replace all polymorphic things with their
    corresponding new names.

(1.2) Also, collect any obligations from all monomorphic functions in the program.
      Why? ... TODO, e.g. sumTree, and mkTree.

(2) Start monormorphizing toplevel functions, and collect any new obligations
    that may be generated. Repeat (2) until there are no more obls.

(3) Create monomorphic versions of all datatypes.

(4) After we have all the monomorphic datatypes, we need to fix TYPEs in (Packed TYPE ..) to
    have the correct suffix. Actually, this could be done in 'collectMonoObls', but we do
    it in a separate pass for now.

(5) Delete all polymorphic fns and datatypes, which should all just be dead code now.

(6) Typecheck monomorphic L0 once more.

TODOs:

(*) Curried functions are not supported atm (not even by the typechecker):
    they're a bit tricky to get right as Gibbon functions can only accept 1 argument.
(*) Support minimal 'import's in 'Gibbon.HaskellFronted'.
(*) Anonymous lambdas


Lambda lifting
~~~~~~~~~~~~~~

Assume that the input program is monomorphic.

(a) Traverse all expressions in the program (main and functions), and
    float out all lambda definitions to the top-level.

(b) Collect all function references passed in as arguments to other functions.
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
  dbgTrace 5 ("\n\nMonomorphized:\n" ++ (render $ pprint p1)) (pure ())
  p2 <- spec p1
  dbgTrace 5 ("\n\nSpecialized:\n" ++ (render $ pprint p2)) (pure ())
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
        AppE f [] args   -> AppE f [] (map toL1Exp args)
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
        SymTy0  -> L1.SymTy
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
    toL1TyS t@(ForAll tyvars (ArrowTy as b))
      | tyvars == [] = (map toL1Ty as, toL1Ty b)
      | otherwise    = err1 (sdoc t)
    toL1TyS (ForAll _ t) = error $ "toL1: Not a function type: " ++ sdoc t

    err1 msg = error $ "toL1: Program was not fully monomorphized. Encountered" ++ msg

--------------------------------------------------------------------------------

data MonoState = MonoState
  { mono_funs_todo :: M.Map (Var, [Ty0]) Var
  , mono_funs_done :: M.Map (Var, [Ty0]) Var
  , mono_lams      :: M.Map (Var, [Ty0]) Var
  , mono_dcons     :: M.Map (TyCon, [Ty0]) Var -- suffix
  }
  deriving (Show, Read, Ord, Eq, Generic, Out)

emptyMonoState :: MonoState
emptyMonoState = MonoState
  { mono_funs_todo = M.empty, mono_funs_done = M.empty
  , mono_lams = M.empty, mono_dcons = M.empty }

extendFuns :: (Var,[Ty0]) -> Var -> MonoState -> MonoState
extendFuns k v mono_st@MonoState{mono_funs_todo} =
  mono_st { mono_funs_todo = M.insert k v mono_funs_todo }

extendLambdas :: (Var,[Ty0]) -> Var -> MonoState -> MonoState
extendLambdas k v mono_st@MonoState{mono_lams} =
  mono_st { mono_lams = M.insert k v mono_lams }

extendDatacons :: (TyCon,[Ty0]) -> Var -> MonoState -> MonoState
extendDatacons k v mono_st@MonoState{mono_dcons} =
  mono_st { mono_dcons = M.insert k v mono_dcons }

-- We need this wrapper because of the way these maps are defined.
--
-- getLambdaObls id { mono_lams = [ ((id,[IntTy]), id1), ((id,[BoolTy]), id2) ] }
--   = [ (id2, [IntTy]), (id2, [BoolTy]) ]
getLambdaObls :: Var -> MonoState -> (M.Map Var [Ty0])
getLambdaObls f MonoState{mono_lams} =
  M.fromList $ map (\((_,tys), w) -> (w, tys)) f_mono_st
  where
    f_mono_st = filter (\((v,_), _) -> v == f) (M.toList mono_lams)


--------------------------------------------------------------------------------

monomorphize :: Prog0 -> PassM Prog0
monomorphize p@Prog{ddefs,fundefs,mainExp} = do
  let env2 = Env2 M.empty (M.map funTy fundefs)
  -- Step (1)
  (mono_st, mainExp') <-
    case mainExp of
      Nothing -> pure (emptyMonoState, Nothing)
      Just (e,ty) -> do
        (mono_st', mainExp')  <- collectMonoObls ddefs env2 toplevel emptyMonoState e
        (mono_st'',mainExp'') <- monoLambdas mono_st' mainExp'
        assertLambdasMonomorphized mono_st''
        pure (mono_st'', Just (mainExp'', ty))
  -- Step (1.2)
  let mono_funs = M.filter isMonoFun fundefs
  (mono_st', mono_funs') <-
    foldlM
      (\(sp, funs) fn@FunDef{funArgs,funName,funBody,funTy} -> do
            let env2' = extendsVEnv (M.fromList $ zip funArgs (inTys funTy)) env2
            (sp', funBody')  <- collectMonoObls ddefs env2' toplevel sp funBody
            (sp'',funBody'') <- monoLambdas sp' funBody'
            assertLambdasMonomorphized sp''
            let fn' = fn { funBody = funBody'' }
            pure (sp'', M.insert funName fn' funs)
          )
      (mono_st, mono_funs)
      (M.elems mono_funs)
  let fundefs' = mono_funs' `M.union` fundefs
  -- Step (2)
  (mono_st'', fundefs'') <- monoFunDefs mono_st' fundefs'
  -- Step (3)
  ddefs' <- monoDDefs mono_st'' ddefs
  let p1 = p { ddefs = ddefs', fundefs = fundefs'', mainExp =  mainExp' }
  -- Step (4)
  let p2 = purgePolyFuns p1
      p3 = updateTyCons mono_st'' p2
  -- Step (5)
  let p4 = purgePolyDDefs p3
  -- Step (6)
  p5 <- tcProg p4
  pure p5
  where
    toplevel = M.keysSet fundefs

    monoFunDefs :: MonoState -> FunDefs0 -> PassM (MonoState, FunDefs0)
    monoFunDefs mono_st fundefs1 =
      if M.null (mono_funs_todo mono_st)
      then pure (mono_st, fundefs1)
      else do
        let (((fun_name, tyapps), new_fun_name):rst) = M.toList (mono_funs_todo mono_st)
            fn@FunDef{funArgs, funName, funBody} = fundefs # fun_name
            tyvars = tyVarsFromScheme (funTy fn)
        assertSameLength ("While monormorphizing the function: " ++ sdoc funName) tyvars tyapps
        let mp = M.fromList $ zip tyvars tyapps
            funTy' = ForAll [] (substTyVar mp (tyFromScheme (funTy fn)))
            funBody' = substTyVarExp mp funBody
            -- Move this obligation from todo to done.
            mono_st' = mono_st { mono_funs_done = M.insert (fun_name, tyapps) new_fun_name (mono_funs_done mono_st)
                           , mono_funs_todo = M.fromList rst }
        -- Collect any more obligations generated due to the monormorphization
        let env21 = Env2 (M.fromList $ zip funArgs (inTys funTy')) (M.map funTy fundefs1)
        (mono_st'', funBody'') <- collectMonoObls ddefs env21 toplevel mono_st' funBody'
        (mono_st''',funBody''') <- monoLambdas mono_st'' funBody''
        let fn' = fn { funName = new_fun_name, funTy = funTy', funBody = funBody''' }
        monoFunDefs mono_st''' (M.insert new_fun_name fn' fundefs1)

    monoDDefs :: MonoState -> DDefs0 -> PassM DDefs0
    monoDDefs mono_st ddefs1 =
      if M.null (mono_dcons mono_st)
      then pure ddefs1
      else do
        let (((tycon, tyapps), suffix):rst) = M.toList (mono_dcons mono_st)
            ddf@DDef{tyName,tyArgs,dataCons} = lookupDDef ddefs tycon
        assertSameLength ("In the datacon: " ++ sdoc tyName) tyArgs tyapps
        let tyName' = varAppend tyName suffix
            dataCons' = map
                          (\(dcon,vtys) ->
                            let (vars,tys) = unzip vtys
                                sbst = M.fromList (zip tyArgs tyapps)
                                tys' = map (substTyVar sbst) tys
                                tys'' = map (updateTyConsTy ddefs1 mono_st) tys'
                                vtys' = zip vars tys''
                            in (dcon ++ fromVar suffix, vtys'))
                          dataCons
            ddefs1' = M.insert tyName' (ddf { tyName = tyName', tyArgs = [], dataCons = dataCons' })  ddefs1
            mono_st'  = mono_st { mono_dcons = M.fromList rst }
        monoDDefs mono_st' ddefs1'

-- After 'monoLambdas' runs, (mono_lams MonoState) must be empty
assertLambdasMonomorphized :: MonoState -> PassM ()
assertLambdasMonomorphized MonoState{mono_lams} =
  if M.null mono_lams
  then pure ()
  else error $ "Expected 0 lambda monormorphization obligations. Got " ++ sdoc mono_lams

assertSameLength :: (Out a, Out b, Monad m) => String -> [a] -> [b] -> m ()
assertSameLength msg as bs =
  if length as /= length bs
  then error $ "assertSameLength: Type applications " ++ sdoc bs ++ " incompatible with the type variables: " ++
               sdoc as ++ ".\n " ++ msg
  else pure ()

-- | Collect monomorphization obligations.
collectMonoObls :: DDefs0 -> Env2 Ty0 -> S.Set Var -> MonoState -> L Exp0 -> PassM (MonoState, L Exp0)
collectMonoObls ddefs env2 toplevel mono_st (L p ex) = fmap (L p) <$>
  case ex of
    AppE f [] args -> do
      (mono_st', args') <- collectMonoOblsl ddefs env2 toplevel mono_st args
      pure (mono_st', AppE f [] args')
    AppE f tyapps args -> do
      (mono_st', args') <- collectMonoOblsl ddefs env2 toplevel mono_st args
      if f `S.member` toplevel
      then case (M.lookup (f,tyapps) (mono_funs_done mono_st), M.lookup (f,tyapps) (mono_funs_todo mono_st)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let mono_st'' = extendFuns (f,tyapps) new_name mono_st'
               pure (mono_st'', AppE new_name [] args')
             (Just fn_name, _) -> pure (mono_st', AppE fn_name [] args')
             (_, Just fn_name) -> pure (mono_st', AppE fn_name [] args')

      -- Why (f,[])? See the special case for let below.
      else case (M.lookup (f,[]) (mono_lams mono_st), M.lookup (f,tyapps) (mono_lams mono_st)) of
             (Nothing, Nothing) -> do
               new_name <- gensym f
               let mono_st'' = extendLambdas (f,tyapps) new_name mono_st'
               pure (mono_st'', AppE new_name [] args')
             (_,Just lam_name) -> pure (mono_st', AppE lam_name [] args')
             (Just lam_name,_) -> pure (mono_st', AppE lam_name [] args')

    LetE (v, [], ty@ArrowTy{}, rhs) bod ->do
      let env2' = (extendVEnv v ty env2)
      case unLoc rhs of
        Ext (LambdaE{}) -> do
          (srhs, rhs') <- go mono_st rhs
          (sbod, bod') <- collectMonoObls ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v,[],ty,rhs') bod')
        _ -> do
          -- If it's not a lambda defn, it's been passed as an argument --
          -- we don't want to monormorphize it here. It'll be handled when
          -- the the outer fn is processed.
          -- To ensure that (AppE v ...) uses the same name, we add it into
          -- mono_st s.t. it's new name is same as it's old name.
          let mono_st' = extendLambdas (v,[]) v mono_st
          (srhs, rhs') <- go mono_st' rhs
          (sbod, bod') <- collectMonoObls ddefs env2' toplevel srhs bod
          pure (sbod, LetE (v, [], ty, rhs') bod')

    LetE (v,[],ty,rhs) bod -> do
      let env2' = (extendVEnv v ty env2)
      (srhs, rhs') <- go mono_st rhs
      (sbod, bod') <- collectMonoObls ddefs env2' toplevel srhs bod
      pure (sbod, LetE (v,[],ty,rhs') bod')

    CaseE scrt brs -> do
      case recoverType ddefs env2 scrt of
        PackedTy tycon tyapps -> do
          (suffix, mono_st'') <-
            case tyapps of
              -- It's a monomorphic datatype.
              [] -> pure ("", mono_st)
              _  -> do
                case M.lookup (tycon, tyapps) (mono_dcons mono_st) of
                  Nothing -> do
                    let DDef{tyArgs} = lookupDDef ddefs tycon
                    assertSameLength ("In the expression: " ++ sdoc ex) tyArgs tyapps
                    suffix <- gensym "_v"
                    let mono_st' = extendDatacons (tycon, tyapps) suffix mono_st
                    pure (suffix, mono_st')
                  Just suffix -> pure (suffix, mono_st)
          (sscrt, scrt') <- go mono_st'' scrt
          (sbrs, brs') <-
            foldlM
              (\(sp, acc) (dcon,vtys,bod) -> do
                let env2' = extendsVEnv (M.fromList vtys) env2
                (sbod, bod') <- collectMonoObls ddefs env2' toplevel sp bod
                pure (sbod, acc ++ [(dcon ++ fromVar suffix,vtys,bod')]))
              (sscrt, []) brs
          pure (sbrs, CaseE scrt' brs')

        ty -> error $ "collectMonoObls: Unexpected type for the scrutinee, " ++ sdoc ty ++
                      ". In the expression: " ++ sdoc ex

    DataConE (ProdTy tyapps) dcon args -> do
      (sargs, args') <- collectMonoOblsl ddefs env2 toplevel mono_st args
      case tyapps of
        -- It's a monomorphic datatype.
        [] -> pure (sargs, DataConE (ProdTy []) dcon args')
        _  -> do
          -- Collect datacon instances here.
          let tycon = getTyOfDataCon ddefs dcon
          case M.lookup (tycon, tyapps) (mono_dcons sargs) of
            Nothing -> do
              let DDef{tyArgs} = lookupDDef ddefs tycon
              assertSameLength ("In the expression: " ++ sdoc ex) tyArgs tyapps
              suffix <- gensym "_v"
              let mono_st' = extendDatacons (tycon, tyapps) suffix sargs
                  dcon' = dcon ++ (fromVar suffix)
              pure (mono_st', DataConE (ProdTy []) dcon' args')
            Just suffix -> do
              let dcon' = dcon ++ (fromVar suffix)
              pure (sargs, DataConE (ProdTy []) dcon' args')

    PrimAppE pr args -> do
      (mono_st', args') <- collectMonoOblsl ddefs env2 toplevel mono_st args
      pure (mono_st', PrimAppE pr args')

    -- Straightforward recursion
    VarE{}    -> pure (mono_st, ex)
    LitE{}    -> pure (mono_st, ex)
    LitSymE{} -> pure (mono_st, ex)
    IfE a b c -> do
      (sa, a') <- go mono_st a
      (sb, b') <- go sa b
      (sc, c') <- go sb c
      pure (sc, IfE a' b' c')
    MkProdE args -> do
      (sp, args') <- collectMonoOblsl ddefs env2 toplevel mono_st args
      pure (sp, MkProdE args')
    ProjE i e -> do
      (sp, e') <- go mono_st e
      pure (sp, ProjE i e')
    TimeIt e ty b -> do
      (se, e') <- go mono_st e
      pure (se, TimeIt e' ty b)
    Ext ext ->
      case ext of
        LambdaE args bod -> do
          (sbod, bod') <- go mono_st bod
          pure (sbod, Ext $ LambdaE args bod')
        _ -> error ("collectMonoObls: TODO, "++ sdoc ext)
    _ -> error ("collectMonoObls: TODO, " ++ sdoc ex)
  where
    go = collectMonoObls ddefs env2 toplevel

collectMonoOblsl :: DDefs0 -> Env2 Ty0 -> S.Set Var -> MonoState -> [L Exp0] -> PassM (MonoState, [L Exp0])
collectMonoOblsl ddefs env2 toplevel mono_st es = do
  foldlM
    (\(sp, acc) e -> do
          (s,e') <- collectMonoObls ddefs env2 toplevel sp e
          pure (s, acc ++ [e']))
    (mono_st, []) es


-- | Create monomorphic versions of lambdas bound in this expression.
-- This does not float out the lambda definitions.
monoLambdas :: MonoState -> L Exp0 -> PassM (MonoState, L Exp0)
-- Assummption: lambdas only appear as RHS in a let.
monoLambdas mono_st (L p ex) = fmap (L p) <$>
  case ex of
    LetE (v,[],vty, rhs@(L p1 (Ext (LambdaE args lam_bod)))) bod -> do
      let lam_mono_st = getLambdaObls v mono_st
      if M.null lam_mono_st
      -- This lambda is not polymorphic, don't monomorphize.
      then do
        (mono_st1, bod') <- go bod
        (mono_st2, lam_bod') <- monoLambdas mono_st1 lam_bod
        pure (mono_st2, LetE (v, [], vty, L p1 (Ext (LambdaE args lam_bod'))) bod')
      -- Monomorphize and only bind those, drop the polymorphic defn.
      -- Also drop the obligation that we applied from MonoState.
      -- So after 'monoLambdas' is done, (mono_lams MonoState) should be [].
      else do
        -- new_lam_mono_st = old_lam_mono_st - applied_lam_mono_st
        let new_lam_mono_st = (mono_lams mono_st) `M.difference`
                              (M.fromList $ map (\(w,wtyapps) -> ((v,wtyapps), w)) (M.toList lam_mono_st))
            mono_st' = mono_st { mono_lams =  new_lam_mono_st }
        (mono_st1, bod') <- monoLambdas mono_st' bod
        monomorphized <- monoLamBinds (M.toList lam_mono_st) (vty, rhs)
        pure (mono_st1, unLoc $ foldl (\acc bind -> l$ LetE bind acc) bod' monomorphized)

    -- Straightforward recursion
    VarE{}    -> pure (mono_st, ex)
    LitE{}    -> pure (mono_st, ex)
    LitSymE{} -> pure (mono_st, ex)
    AppE f tyapps args ->
      case tyapps of
        [] -> do (mono_st1, args') <- monoLambdasl mono_st args
                 pure (mono_st1, AppE f [] args')
        _  -> error $ "monoLambdas: Expression probably not processed by collectMonoObls: " ++ sdoc ex
    PrimAppE pr args -> do (mono_st1, args') <- monoLambdasl mono_st args
                           pure (mono_st1, PrimAppE pr args')
    LetE (v,[],ty,rhs) bod -> do
      (mono_st1, rhs') <- go rhs
      (mono_st2, bod') <- monoLambdas mono_st1 bod
      pure (mono_st2, LetE (v, [], ty, rhs') bod')
    IfE a b c -> do
      (mono_st1, a') <- go a
      (mono_st2, b') <- monoLambdas mono_st1 b
      (mono_st3, c') <- monoLambdas mono_st2 c
      pure (mono_st3, IfE a' b' c')
    MkProdE ls -> do
      (mono_st1, ls') <- monoLambdasl mono_st ls
      pure (mono_st1, MkProdE ls')
    ProjE i a  -> do
      (mono_st1, a') <- go a
      pure (mono_st1, ProjE i a')
    CaseE scrt brs -> do
      (mono_st1, scrt') <- go scrt
      (mono_st2, brs') <-
        foldlM
          (\(sp, acc) (dcon,vlocs,bod) -> do
            (sbod, bod') <- monoLambdas sp bod
            pure (sbod, acc ++ [(dcon,vlocs,bod')]))
          (mono_st1, []) brs
      pure (mono_st2, CaseE scrt' brs')
    DataConE tyapp dcon args -> do
      (mono_st1, args') <- monoLambdasl mono_st args
      pure (mono_st1, DataConE tyapp dcon args')
    TimeIt e ty b -> do
      (mono_st1, e') <- go e
      pure (mono_st1, TimeIt e' ty b)
    Ext (LambdaE args bod) -> do
      (mono_st1, bod') <- go bod
      pure (mono_st1, Ext (LambdaE args bod'))
    _ -> error $ "monoLambdas: TODO " ++ sdoc ex
  where go = monoLambdas mono_st

        monoLamBinds :: [(Var,[Ty0])] -> (Ty0, L Exp0) -> PassM [(Var, [Ty0], Ty0, L Exp0)]
        monoLamBinds [] _ = pure []
        monoLamBinds ((w, tyapps):rst) (ty,ex1) = do
          let tyvars = tyVarsInTy ty
          assertSameLength ("In the expression: " ++ sdoc ex1) tyvars tyapps
          let mp = M.fromList $ zip tyvars tyapps
              ty'  = substTyVar mp ty
              ex'  = substTyVarExp mp ex1
          (++ [(w, [], ty', ex')]) <$> monoLamBinds rst (ty,ex1)

monoLambdasl :: MonoState -> [L Exp0] -> PassM (MonoState, [L Exp0])
monoLambdasl mono_st es = do
  foldlM
    (\(sp, acc) e -> do
          (s,e') <- monoLambdas sp e
          pure (s, acc ++ [e']))
    (mono_st, []) es


-- | Remove all polymorphic functions and datatypes from a program. 'monoLambdas'
-- already gets rid of polymorphic mono_lams.
purgePolyFuns :: Prog0 -> Prog0
purgePolyFuns p@Prog{fundefs} =
  p { fundefs = M.filter isMonoFun fundefs }

isMonoFun :: FunDef0 -> Bool
isMonoFun FunDef{funTy} = (tyVarsFromScheme funTy) == []

purgePolyDDefs :: Prog0 -> Prog0
purgePolyDDefs p@Prog{ddefs} =
  p { ddefs = M.filter isMonoDDef ddefs }
  where
    isMonoDDef DDef{tyArgs} = tyArgs == []

-- See Step (4) in the big note. Lot of code duplication :(
updateTyCons :: MonoState -> Prog0 -> Prog0
updateTyCons mono_st p@Prog{ddefs, fundefs,mainExp}=
  let fundefs' = M.map fixFunDef fundefs
      mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (e,ty) -> Just (updateTyConsExp ddefs mono_st e, updateTyConsTy ddefs mono_st ty)
  in p { fundefs = fundefs', mainExp = mainExp' }
  where
    fixFunDef :: FunDef0 -> FunDef0
    fixFunDef fn@FunDef{funTy, funBody} =
      let funTy' = ForAll (tyVarsFromScheme funTy) (updateTyConsTy ddefs mono_st (tyFromScheme funTy))
          funBody' = updateTyConsExp ddefs mono_st funBody
      in fn { funTy = funTy', funBody = funBody' }

-- |
updateTyConsExp :: DDefs0 ->  MonoState -> L Exp0 -> L Exp0
updateTyConsExp ddefs mono_st (L loc ex) = L loc $
  case ex of
    VarE{}    -> ex
    LitE{}    -> ex
    LitSymE{} -> ex
    AppE f [] args    -> AppE f [] (map go args)
    PrimAppE pr args  -> PrimAppE pr (map go args)
    LetE (v,[],ty,rhs) bod -> LetE (v, [], updateTyConsTy ddefs mono_st ty, go rhs) (go bod)
    IfE a b c  -> IfE (go a) (go b) (go c)
    MkProdE ls -> MkProdE (map go ls)
    ProjE i e  -> ProjE i (go e)
    CaseE scrt brs ->
      CaseE (go scrt) (map
                        (\(dcon,vtys,rhs) -> let (vars,tys) = unzip vtys
                                                 vtys' = zip vars $ map (updateTyConsTy ddefs mono_st) tys
                                             in (dcon, vtys', go rhs))
                        brs)
    DataConE (ProdTy tyapps) dcon args ->
      let tyapps' = map (updateTyConsTy ddefs mono_st) tyapps
          tycon   = getTyOfDataCon ddefs dcon
          dcon' = case M.lookup (tycon,tyapps') (mono_dcons mono_st) of
                    Nothing     -> dcon
                    Just suffix -> dcon ++ fromVar suffix
      -- Why [] ? The type arguments aren't required as the DDef is monomorphic.
      in DataConE (ProdTy []) dcon' (map go args)
    TimeIt e ty b -> TimeIt (go e) (updateTyConsTy ddefs mono_st ty) b
    Ext (LambdaE args bod) -> Ext (LambdaE (map (\(v,ty) -> (v, updateTyConsTy ddefs mono_st ty)) args) (go bod))
    _ -> error $ "updateTyConsExp: TODO, " ++ sdoc ex
  where
    go = updateTyConsExp ddefs mono_st

-- | Update TyCons if an appropriate monomorphization obligation exists.
updateTyConsTy :: DDefs0 -> MonoState -> Ty0 -> Ty0
updateTyConsTy ddefs mono_st ty =
  case ty of
    IntTy   -> IntTy
    SymTy0  -> SymTy0
    BoolTy  -> BoolTy
    TyVar{} ->  error $ "updateTyConsTy: " ++ sdoc ty ++ " shouldn't be here."
    MetaTv{} -> error $ "updateTyConsTy: " ++ sdoc ty ++ " shouldn't be here."
    ProdTy tys  -> ProdTy (map go tys)
    SymDictTy t -> SymDictTy (go t)
    ArrowTy as b   -> ArrowTy (map go as) (go b)
    PackedTy t tys ->
      let tys' = map go tys
      in case M.lookup (t,tys') (mono_dcons mono_st) of
           Nothing     -> PackedTy t tys'
           -- Why [] ? The type arguments aren't required as the DDef is monomorphic.
           Just suffix -> PackedTy (t ++ fromVar suffix) []
    ListTy t -> ListTy (go t)
  where
    go = updateTyConsTy ddefs mono_st

--------------------------------------------------------------------------------

data LowerState = LowerState
  { lo_funs_todo :: M.Map (Var, [Var]) Var
  , lo_fundefs   :: FunDefs0 }
  deriving (Show, Eq, Generic, Out)


-- We track references when we bind variables to account for programs like:
--
--     foo :: ((a -> b), a) -> a ; foo = ...
--     main = ... arg = (fn, thing) ... foo arg ...
--
-- type FnRefsEnv = M.Map Var FnRefs
--

type FnRefs    = [Var]

newtype Spec = Spec { lams :: [(Var,Var)] }
  deriving (Show, Eq, Generic, Out)

spec :: Prog0 -> PassM Prog0
spec prg@Prog{ddefs,fundefs,mainExp} = do
  let env2 = progToEnv prg
  (low, mainExp') <-
    case mainExp of
      Nothing -> pure (emptyLowerState, Nothing)
      Just (e, ty) -> do
        (low', e') <- specExp ddefs env2 emptyLowerState e
        pure (low', Just (e', ty))

  -- Same reason as Step (1.2) in monomorphization.
  let fo_funs = M.filter isFOFun fundefs
  low' <-
    foldlM
      (\low1 fn@FunDef{funName,funBody} -> do
            (low1', funBody') <- specExp ddefs env2 low1 funBody
            let funs   = lo_fundefs low1'
                fn'    = fn { funBody = funBody' }
                funs'  = M.insert funName fn' funs
                low1'' = low1' { lo_fundefs = funs' }
            pure low1'')
      low
      (M.elems fo_funs)

  low'' <- fixpoint low'
  -- Get rid of all higher order functions.
  let fundefs' = purgeHO (lo_fundefs low'')
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
        low' <- specFun ddefs low (progToEnv prg) new_fn_name refs fn
        let low'' = low' { lo_funs_todo = M.deleteAt 0 (lo_funs_todo low') }
        fixpoint low''

    purgeHO :: FunDefs0 -> FunDefs0
    purgeHO fns = M.filter isFOFun fns

    isFOFun :: FunDef0 -> Bool
    isFOFun FunDef{funTy} =
      let ForAll _ (ArrowTy arg_tys ret_ty) = funTy
      in all (null . arrowTysInTy) arg_tys &&
         arrowTysInTy ret_ty == []

-- Eliminate all functions passed in as arguments to this function.
specFun :: DDefs0 -> LowerState -> Env2 Ty0 -> Var -> FnRefs -> FunDef0 -> PassM LowerState
specFun ddefs low env2 new_fn_name refs fn@FunDef{funArgs, funTy} = do
  let
      -- lamda args
      funArgs'  = map fst $ filter (isFunTy . snd) $ zip funArgs (inTys funTy)
      specs     = Spec (fragileZip funArgs' refs)
      -- non-lambda args
      funArgs'' = map fst $ filter (not . isFunTy . snd) $ zip funArgs (inTys funTy)
      fn' = fn { funName = new_fn_name
               , funBody = do_spec specs (funBody fn) }
  (low', funBody') <- specExp ddefs env2 low (funBody fn')
  let fn''  = fn' { funBody = funBody'
                  , funArgs = funArgs''
                  -- N.B. Only update the type after 'specExp' runs.
                  , funTy   = funTy' }
      low'' = low' { lo_fundefs = M.insert new_fn_name fn'' (lo_fundefs low') }
  pure low''
  where
    ForAll tyvars (ArrowTy arg_tys ret_ty) = funTy

    -- TODO: What if the function returns another function ? Not handled yet.
    -- First order type
    funTy' = ForAll tyvars (ArrowTy (filter (not . isFunTy) arg_tys) ret_ty)

{-

Specialization, only lambdas for now. E.g.

    foo :: (a -> b) -> a -> b
    foo f1 a = f1 a

    ... foo top1 x ...

becomes

    foo f1 a = ...

    foo2 :: a -> b
    foo2 a = top1 a

    ... foo2 x ...

-}
    do_spec :: Spec -> L Exp0 -> L Exp0
    do_spec Spec{lams} e = foldr (uncurry subst') e lams


    -- | Update a function name.
    subst' :: Var -> Var -> L Exp0 -> L Exp0
    subst' old new (L p0 ex) = L p0 $
      let go = subst' old new in
      case ex of
        VarE v | v == old  -> VarE new
               | otherwise -> VarE v
        AppE f [] ls | f == old  -> AppE new [] (map go ls)
                     | otherwise -> AppE f [] (map go ls)
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


specExp :: DDefs0 -> Env2 Ty0 -> LowerState -> L Exp0 -> PassM (LowerState, L Exp0)
specExp ddefs env2 low (L p ex) = fmap (L p) <$>
  case ex of
    -- TODO, docs.
    AppE f [] args -> do
      (low', args') <- specExpl ddefs env2 low args
      let args'' = dropFunRefs f args'
          refs   = foldr collectFunRefs [] args
      case refs of
        [] -> pure (low, AppE f [] args')
        _  -> do
          case M.lookup (f,refs) (lo_funs_todo low') of
            Nothing -> do
              f' <- gensym f
              let ForAll _ (ArrowTy as _) = lookupFEnv f env2
                  arrow_tys = concatMap arrowTysInTy as
              -- Check that the # of refs we collected actually matches the #
              -- of functions 'f' expects.
              assertSameLength ("While lowering the expression " ++ sdoc ex) refs arrow_tys
              -- We have a new lowering obligation.
              let low'' = low' { lo_funs_todo = M.insert (f,refs) f' (lo_funs_todo low') }
              pure (low'', AppE f' [] args'')
            Just f' -> pure (low', AppE f' [] args'')

    -- Float out a lambda fun to the top-level.
    LetE (v, [], ty, L _ (Ext (LambdaE args lam_bod))) bod -> do
      let arg_vars = map fst args
          captured_vars = gFreeVars lam_bod `S.difference` (S.fromList arg_vars)
      if not (S.null captured_vars)
      then error $ "specExp: LamdaE captures variables: "
                   ++ show captured_vars
                   ++ ". TODO: these can become additional arguments."
      else do
        (low', lam_bod') <- go lam_bod
        let _fn_refs = collectFunRefs lam_bod []
            fn = FunDef { funName = v
                        , funArgs = arg_vars
                        , funTy   = ForAll [] ty
                        , funBody = lam_bod' }
            env2' = extendFEnv v (ForAll [] ty) env2
            low'' = low' { lo_fundefs = M.insert v fn (lo_fundefs low') }
        fmap unLoc <$> specExp ddefs env2' low'' bod

    LetE (v, [], ty, rhs) bod -> do
      let _fn_refs = collectFunRefs rhs []
          env2' = (extendVEnv v ty env2)
      (low', rhs') <- go rhs
      (low'', bod') <- specExp ddefs env2' low' bod
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
      (low', scrt') <- go scrt
      (low'', brs') <- foldlM
                        (\(lo, acc) (dcon,vtys,rhs) -> do
                          let env2' = extendsVEnv (M.fromList vtys) env2
                          (lo', e') <- specExp ddefs env2' lo rhs
                          pure (lo', acc ++ [(dcon,vtys,e')]))
                        (low', [])
                        brs
      pure (low'', CaseE scrt' brs')
    DataConE tyapp dcon args -> do
      (low', args') <- gol args
      pure (low', DataConE tyapp dcon args')
    TimeIt e ty b -> do
       (low', e') <- go e
       pure (low', TimeIt e' ty b)
    _ -> error $ "specExp: TODO " ++ sdoc ex
  where
    go = specExp ddefs env2 low
    gol = specExpl ddefs env2 low

    isFunRef e =
      case e of
        VarE v -> M.member v (fEnv env2)
        _ -> False

    -- fn_0 (fn_1, thing, fn_2) => fn_0 (thing)
    dropFunRefs :: Var -> [L Exp0] -> [L Exp0]
    dropFunRefs fn_name args =
      foldr (\(a,t) acc -> if isFunTy t then acc else a:acc) [] (zip args arg_tys)
      where
        ForAll _ (ArrowTy arg_tys _) = lookupFEnv fn_name env2

    collectFunRefs :: L Exp0 -> [Var] -> [Var]
    collectFunRefs (L _ e) acc =
      case e of
        VarE v -> if isFunRef e
                  then v : acc
                  else acc
        LitE{}     -> acc
        LitSymE{}  -> acc
        AppE _ _ args   -> foldr collectFunRefs acc args
        PrimAppE _ args -> foldr collectFunRefs acc args
        LetE (_,_,_, rhs) bod -> foldr collectFunRefs acc [bod, rhs]
        IfE a b c  -> foldr collectFunRefs acc [c, b, a]
        MkProdE ls -> foldr collectFunRefs acc ls
        ProjE _ a  -> collectFunRefs a acc
        DataConE _ _ ls -> foldr collectFunRefs acc ls
        TimeIt a _ _ -> collectFunRefs a acc
        _ -> error $ "collectFunRefs: TODO " ++ sdoc e

specExpl :: DDefs0 -> Env2 Ty0 -> LowerState -> [L Exp0]
            -> PassM (LowerState, [L Exp0])
specExpl ddefs env2 low exs =
  foldlM
    (\(st, acc) e ->
       do (st', e') <- go st e
          pure (st', acc ++ [e']))
    (low, [])
    exs
  where
    go = specExp ddefs env2
