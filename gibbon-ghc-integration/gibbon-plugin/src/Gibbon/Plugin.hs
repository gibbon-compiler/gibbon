{-# LANGUAGE DeriveDataTypeable #-}

module Gibbon.Plugin where

import           Data.String
import qualified GHC.Types.TyThing as GHC
import qualified GHC.Unit.External as GHC
import qualified GHC.Utils.Trace as GHC
import qualified GHC.Plugins as GHC
import qualified GHC.Utils.Outputable as Ppr
import qualified GHC.Types.Var.Set as GHC
import qualified GHC.Core.Multiplicity as GHC
import qualified GHC.Core.TyCo.Rep as GHC


import           Data.Foldable
import           Foreign.Ptr ( Ptr )
import           Data.Data ( Data )
import qualified Data.Set as Set
import qualified Data.Map as M
import           System.FilePath
import           System.Random
import           Data.Word
import           Data.List

import qualified Gibbon.Common as Gib
import qualified Gibbon.Pretty as Gib
import qualified Gibbon.L0.Syntax as Gib
import qualified Gibbon.Compiler as Gib
import qualified Gibbon.DynFlags as Gib


--------------------------------------------------------------------------------

data Packed a = Packed (Ptr a)
  deriving Show

{-# NOINLINE liftPacked #-}
liftPacked :: (a -> b) -> Packed a -> Packed b
liftPacked = error "liftPacked"

type PackedAnnEnv = GHC.NameEnv PackedAnn

data PackedAnn = LiftPacked
    deriving Data

instance Ppr.Outputable PackedAnn where
    ppr LiftPacked = Ppr.text "LiftPacked"


--------------------------------------------------------------------------------


plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = installGibbonPlugin
                           -- , GHC.pluginRecompile = GHC.purePlugin
                           }
  where
    installGibbonPlugin :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
    installGibbonPlugin _ todos = return (gibbonCoreTodo : todos)

    gibbonCoreTodo :: GHC.CoreToDo
    gibbonCoreTodo = GHC.CoreDoPluginPass "GibbonLiftPacked" gibbonPlugin


gibbonPlugin :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
gibbonPlugin mod_guts = do
    GHC.liftIO $ print "[Gibbon Core Plugin (final)] Starting..."

    -- -- (0)
    -- GHC.putMsg (Ppr.text "\nInput module:\n----------------------------------------" Ppr.$$ (GHC.ppr (GHC.mg_binds mod_guts)))

    -- (1) and (2): Find all arguments to liftPacked, form an initial root set, and then fetch the transitive closure.
    (to_lift, dcons, closure) <- transitiveClosure mod_guts
    GHC.putMsg (Ppr.text "\nExpressions to lift:\n----------------------------------------" Ppr.$$ (GHC.ppr (to_lift, closure)))

    closure' <- mapM (\(f,rhs) ->
                          if elem f to_lift
                          then do
                            let name = GHC.idName f
                            uniq <- GHC.getUniqueM
                            let name' = GHC.mkFCallName uniq (fromString $ "c_" ++ nameToString name)
                            pure (GHC.setIdName f name',rhs)
                          else pure (f,rhs))
                     closure

    -- (3) Translate the closure to Gibbon L0.
    l0_prog <- coreToL0 dcons closure'
    GHC.liftIO $ putStrLn "\nL0 program:\n----------------------------------------"
    GHC.liftIO $ putStrLn (Gib.pprender l0_prog)

    -- (4) Have Gibbon generate a .o file.
    fp <- GHC.liftIO $ generateObjectFile l0_prog
    GHC.liftIO $ putStrLn "\nCompiled:\n----------------------------------------"
    GHC.liftIO $ putStrLn fp

    -- (5) Link the .o file in the module.
    let objfile = replaceExtension fp ".o"
    GHC.liftIO $ Gib.compileRTS gibbonConfigForPlugin
    lib_dir <- GHC.liftIO Gib.getRTSBuildDir
    let rtsfile = lib_dir </> "gibbon_rts.o"
    let mod_guts' = mod_guts { GHC.mg_foreign_files = (GHC.mg_foreign_files mod_guts)
                                                    ++ [ ( GHC.RawObject, objfile)
                                                       , ( GHC.RawObject, rtsfile)
                                                       ]
                             }

    -- fficalls <- foldrM (\(f,rhs) acc ->
    --                       if elem f to_lift
    --                       then do
    --                         let name = GHC.idName f
    --                         uniq <- GHC.getUniqueM
    --                         let name' = GHC.mkFCallName uniq ("c_" ++ nameToString name)
    --                         let f' = GHC.setIdName f name'
    --                         uniq2 <- GHC.getUniqueM
    --                         let name'' = GHC.mkFCallName uniq ("fast_" ++ nameToString name)
    --                         let f'' = GHC.setIdName f name''
    --                         -- case rhs of
    --                         --     GHC.Lam w bod ->
    --                         --       GHC.Lam w (GHC.mkCoreApps f'' )
    --                       else pure acc)
    --                  []
    --                  closure
    -- GHC.putMsg (Ppr.text "\nFFI calls:\n----------------------------------------" Ppr.$$ (GHC.ppr (fficalls)))

    -- (6) Replace (liftPacked f) with a FFI function call to gibbon_f.

    return mod_guts'


--------------------------------------------------------------------------------

gibbonConfigForPlugin :: Gib.Config
gibbonConfigForPlugin = let
    config =  Gib.defaultConfig { Gib.mode = Gib.Library (Gib.toVar "xxx") }
    dflags' = Gib.gopt_set Gib.Opt_DisableGC $ Gib.gopt_set Gib.Opt_Packed (Gib.dynflags config)
  in
    config { Gib.dynflags = dflags', Gib.optc = " -O3 " }

generateObjectFile :: Gib.Prog0 -> IO FilePath
generateObjectFile l0 = do
  uniq <- randomIO :: IO Word16
  let fp = "/tmp/gibbon-ghc-integration-file-" ++ show uniq ++ ".hs"
  Gib.compileFromL0 gibbonConfigForPlugin 0 fp l0
  return fp

--------------------------------------------------------------------------------

transitiveClosure :: GHC.ModGuts -> GHC.CoreM ([GHC.Id], [GHC.DataCon], [(GHC.Var, GHC.CoreExpr)])
transitiveClosure mod_guts = do
        -- Things defined in other modules and libraries.
        hsc_env <- GHC.getHscEnv
        external_package_state <- GHC.liftIO $ GHC.hscEPS hsc_env
        let external_ids = GHC.nonDetNameEnvElts (GHC.eps_PTE external_package_state)
            external_unfoldings =
                foldr (\tyt acc ->
                            case tyt of
                                GHC.AnId i -> case GHC.maybeUnfoldingTemplate (GHC.realIdUnfolding i) of
                                                  Nothing -> acc
                                                  Just expr -> GHC.extendVarEnv acc i expr
                                _ -> acc)
                      GHC.emptyVarEnv
                      external_ids

        -- Things defined in this module.
        let (_module_binds_ls,module_binds,module_ids) =
                foldr (\b (acc1,acc2,acc3) -> case b of
                                     GHC.NonRec i rhs -> ((i,rhs):acc1,GHC.extendVarEnv acc2 i rhs, i:acc3)
                                     GHC.Rec ls -> foldr (\(i,rhs) (acc4,acc5,acc6) ->
                                                              ((i,rhs):acc4,GHC.extendVarEnv acc5 i rhs, i:acc6))
                                                         (acc1,acc2,acc3)
                                                         ls)
                      ([],GHC.emptyVarEnv,[])
                      (GHC.mg_binds mod_guts)

        -- Get Ids that are given a 'LiftPacked' pragma.
        (_, packed_annots :: PackedAnnEnv) <- GHC.getFirstAnnotations GHC.deserializeWithData mod_guts
        let to_lift =  filter (\v -> GHC.elemNameEnv (GHC.idName v) packed_annots) module_ids

        -- Given a list of Ids, suck in their transitive closure.
        let fixpoint dcons_ls binds_ls sucked_in todo
                -- No more Ids to process.
                | [] <- todo
                = (dcons_ls, binds_ls)
                -- This Id is already sucked in or is meant to be excluded.
                | (x:xs) <- todo
                , GHC.elemDVarSet x sucked_in ||
                  varToString x `Set.member` excludedFromClos
                = fixpoint dcons_ls binds_ls sucked_in xs
                -- Data constructor.
                | (x:xs) <- todo
                , Just dcon <- GHC.isDataConId_maybe x
                = fixpoint (dcon:dcons_ls) binds_ls sucked_in xs
                -- Value binding.
                | (x:xs) <- todo
                = if elem x module_ids
                  then let rhs = GHC.lookupVarEnv_NF module_binds x
                           binds_ls1 = (x,rhs):binds_ls
                           sucked_in1 = GHC.extendDVarSet sucked_in x
                           xs1 = (GHC.exprSomeFreeVarsList GHC.isId rhs) ++ xs
                       in -- GHC.pprTrace "(1):" (GHC.ppr (x, rhs, GHC.exprSomeFreeVarsList GHC.isId rhs))
                          (fixpoint dcons_ls binds_ls1 sucked_in1 xs1)
                  else case GHC.lookupVarEnv external_unfoldings x of
                           Nothing ->
                              -- GHC.pprSorry ("No unfolding available for:") (GHC.ppr x)
                               GHC.pprTrace "WARNING:" (GHC.ppr (Ppr.text "No unfolding available for:" Ppr.<> GHC.ppr x))
                                   (fixpoint dcons_ls binds_ls sucked_in xs)
                           Just rhs ->
                               let binds_ls1 = (x,rhs):binds_ls
                                   sucked_in1 = GHC.extendDVarSet sucked_in x
                                   xs1 = (GHC.exprSomeFreeVarsList GHC.isId rhs) ++ xs
                               in -- GHC.pprTrace "(2):" (GHC.ppr (x,rhs,GHC.exprSomeFreeVarsList GHC.isId rhs))
                                  fixpoint dcons_ls binds_ls1 sucked_in1 xs1

        -- The main thing.
        let (dcons, binds) = fixpoint [] [] GHC.emptyDVarSet to_lift

        pure (to_lift, dcons, binds)


-- Things that are not included in the transitive closure.
excludedFromClos :: Set.Set String
excludedFromClos = Set.fromList $
    [ "I#" ] ++
    [ "$fOrdInt", "compareInt", "ltInt", "leInt", "gtInt", "geInt", "$fOrdInt_$cmax", "$fOrdInt_$cmin", "$fOrdInt_$c<="] ++
    [ "$fEqInt", "eqInt", "neInt" ] ++
    [ "$fNumInt", "$fNumInt_$c+", "$fNumInt_$c-", "$fNumInt_$c*",
      "$fNumInt_$cnegate", "$fNumInt_$cabs", "$fNumInt_$csignum",
      "$fNumInt_$cfromInteger" ] ++
    [ "-", "<=", "+" ]

{-

findLP :: GHC.CoreBind -> [GHC.CoreExpr]
findLP bind = gorec bind []
  where
    gorec bind acc = case bind of
        GHC.NonRec _ bod -> go bod []
        GHC.Rec ls       -> foldr (\(_,rhs) acc -> go rhs acc) [] ls

    go expr acc = case expr of
        GHC.Var v        -> acc
        GHC.Lit _lit     -> acc
        GHC.App f arg    -> case f of
                                -- GHC.Var v -> if isLP v
                                --              then f : arg : acc
                                --              else go arg (go f acc)
                                GHC.App g@(GHC.App f arg) arg2 -> case f of
                                    GHC.Var v -> if isLP v
                                                 then f : g : arg : arg2 : acc
                                                 else go arg (go f acc)
                                    _ -> go arg (go f acc)
                                _ -> go arg (go f acc)
        GHC.Lam _ bod    -> go bod acc
        GHC.Let bind rhs -> go rhs (gorec bind acc)
        GHC.Case scrt _ _ alts ->
            foldr (\(GHC.Alt _ _ rhs) acc1 -> go rhs acc1) (go scrt acc) alts
        GHC.Cast rhs _ -> go rhs acc
        _ -> acc


    isLP v = GHC.nameOccName (GHC.varName v) == (GHC.mkVarOcc "liftPacked")
-}


--------------------------------------------------------------------------------

coreToL0 :: [GHC.DataCon] -> [(GHC.Id, GHC.CoreExpr)] -> GHC.CoreM Gib.Prog0
coreToL0 dcons funs = do
    let ddefs = convertDcons dcons
    funs' <- mapM convertFun funs
    let fundefs = M.fromList $ map (\f -> (Gib.funName f, f)) funs'
    pure $ Gib.Prog { Gib.ddefs = ddefs
                    , Gib.fundefs = fundefs
                    , Gib.mainExp = Nothing
                    }

convertFun :: (GHC.Id, GHC.CoreExpr) -> GHC.CoreM Gib.FunDef0
convertFun (toplvl,bod0) =
    case bod0 of
        GHC.Lam arg bod -> do
            bod' <- go bod
            pure $ Gib.FunDef (Gib.toVar (nameToString (GHC.idName toplvl)))
                              [(Gib.toVar (varToString arg))]
                              (Gib.ForAll [] (ghcTyToGibTy (GHC.idType toplvl)))
                              bod'
                              (Gib.FunMeta Gib.Rec Gib.NoInline False)
  where
    go expr =
        case expr of
            GHC.Var v -> pure $ Gib.VarE $ Gib.toVar (varToString v)
            GHC.Case scrt v ty alts -> do
                let makeif =  let (GHC.Alt dcon0 _ _) = head alts in
                                  case dcon0 of
                                      GHC.DataAlt dcon ->
                                          let name = nameToString (GHC.dataConName dcon) in
                                              name == "True" || name == "False"
                if makeif
                  then do
                      let [(GHC.Alt _ _ false_expr)] = filter (\(GHC.Alt (GHC.DataAlt dcon) _ _) -> nameToString (GHC.dataConName dcon) == "False") alts
                      let [(GHC.Alt _ _ true_expr)]  = filter (\(GHC.Alt (GHC.DataAlt dcon) _ _) -> nameToString (GHC.dataConName dcon) == "True") alts
                      scrt' <- go scrt
                      true_expr' <- go true_expr
                      false_expr' <- go false_expr
                      pure $ Gib.IfE scrt' true_expr' false_expr'
                  else do
                      scrt' <- go scrt
                      alts' <- mapM (\(GHC.Alt (GHC.DataAlt dcon) vars rhs) -> do
                                          let dcon' = nameToString (GHC.dataConName dcon)
                                          let vars' = map (\v -> (Gib.toVar (nameToString (GHC.idName v)), ghcTyToGibTy (GHC.idType v))) vars
                                          rhs' <- go rhs
                                          pure (dcon', vars', rhs'))
                                    alts
                      pure $ Gib.CaseE scrt' alts'
            GHC.App _ _ -> do
                let (f:args) = uncurryApp expr
                -- GHC.putMsg (Ppr.text "\nUncurried;\n----------------------------------------" Ppr.$$ (GHC.ppr (f,args)))
                case f of
                    GHC.Var fx -> do
                        case GHC.isDataConWorkId_maybe fx of
                            Nothing -> do
                                case (varToString fx) of
                                    "-" -> do
                                        -- args' <- mapM go args
                                        let x = args !! 2
                                        let y = args !! 3
                                        x' <- go x
                                        y' <- go y
                                        pure $ Gib.PrimAppE Gib.SubP [x',y']
                                    "+" -> do
                                        -- args' <- mapM go args
                                        let x = args !! 2
                                        let y = args !! 3
                                        x' <- go x
                                        y' <- go y
                                        pure $ Gib.PrimAppE Gib.AddP [x',y']
                                    "<=" -> do
                                        -- args' <- mapM go args
                                        let x = args !! 2
                                        let y = args !! 3
                                        x' <- go x
                                        y' <- go y
                                        pure $ Gib.PrimAppE Gib.LtEqP [x',y']
                                    _ -> do
                                        args' <- mapM go args
                                        pure $ Gib.AppE (Gib.toVar (varToString fx)) [] args'

                            Just dcon ->
                                case nameToString (GHC.dataConName dcon) of
                                    "I#" -> case head args of
                                                GHC.Lit lit -> case lit of
                                                                   GHC.LitNumber _ i -> pure $ Gib.LitE (fromIntegral i)
                                                                   _ -> error "unexpected"
                                    _ -> do
                                        args' <- mapM go args
                                        pure $ Gib.DataConE (Gib.ProdTy []) (nameToString (GHC.dataConName dcon)) args'
                    _ ->
                        error "unexpected"
                        -- pure $ Gib.AppE (Gib.toVar "todo4") [] []

{-
                arg' <- go arg
                case f of
                    GHC.Var x ->
                        case GHC.isDataConWorkId_maybe x of
                            Nothing   -> pure $ Gib.AppE (Gib.toVar (varToString x)) [] [arg']
                            Just dcon -> if nameToString (GHC.dataConName dcon) == "I#"
                                         then case arg of
                                                  GHC.Lit lit -> case lit of
                                                                     GHC.LitNumber _ i -> pure $ Gib.LitE (fromIntegral i)
                                                  _ -> error "unexpected"
                                         else do
                                             pure $ Gib.DataConE (Gib.ProdTy []) (nameToString (GHC.dataConName dcon)) [arg']
                    _ -> do
                        let (g,args) = uncurryApp expr
                        case g of
                        GHC.putMsg (Ppr.text "\nUncurried;\n----------------------------------------" Ppr.$$ (GHC.ppr xs))
                        pure $ Gib.AppE (Gib.toVar "todo3") [] [arg']
-}
            GHC.Lam var bod -> do
                bod' <- go bod
                pure $ Gib.Ext (Gib.LambdaE [(Gib.toVar (varToString var), ghcTyToGibTy (GHC.varType var))] bod')
            _ -> do
                -- GHC.putMsg (Ppr.text "\nExpr;\n----------------------------------------" Ppr.$$ (GHC.ppr expr))
                -- pure (Gib.LitE 20)
                error "todo"

uncurryApp :: GHC.CoreExpr -> [GHC.CoreExpr]
uncurryApp = go []
  where
    go acc e =
      case e of
        GHC.App f arg ->
          go (arg : acc) f
        _ -> e : acc

convertDcons :: [GHC.DataCon] -> Gib.DDefs0
convertDcons dcons =
    foldr go M.empty dcons
  where
    go :: GHC.DataCon -> Gib.DDefs0 -> Gib.DDefs0
    go dcon ddefs
        | GHC.isVanillaDataCon dcon
        , tycon <- GHC.dataConTyCon dcon
        , GHC.isVanillaAlgTyCon tycon
        , tyname <- GHC.tyConName tycon
        , tyname_str <- nameToString tyname
        , tyname_var <- Gib.toVar tyname_str
        = case tyname_str of
              "Int"   -> ddefs
              "Float" -> ddefs
              "Bool"  -> ddefs
              _ -> let tyvars =  GHC.tyConTyVars tycon
                       tyvars_var = map (Gib.UserTv . Gib.toVar . varToString) tyvars
                       dcname = GHC.dataConName dcon
                       (_,_,_,_,dcon_args,_dcon_res) = GHC.dataConFullSig dcon
                       dcon_tys = map (\ty -> (False,ghcScaledTyToGibTy ty)) dcon_args
                       dcon_gib = (nameToString dcname, dcon_tys)
                   in case M.lookup tyname_var ddefs of
                          Nothing   ->
                              let ddef = Gib.DDef tyname_var tyvars_var [dcon_gib]
                              in M.insert tyname_var ddef ddefs
                          Just ddef ->
                              let ddef' = ddef { Gib.dataCons = dcon_gib : (Gib.dataCons ddef) }
                              in M.insert tyname_var ddef' ddefs


        | tycon <- GHC.dataConTyCon dcon
        = GHC.sorryDoc ("Non-vanilla datacons not supported yet:") (GHC.ppr (dcon,tycon))


ghcScaledTyToGibTy :: GHC.Scaled GHC.Type -> Gib.Ty0
ghcScaledTyToGibTy (GHC.Scaled _ ty) = ghcTyToGibTy ty

ghcTyToGibTy :: GHC.Type -> Gib.Ty0
ghcTyToGibTy ty
    | GHC.AppTy{} <- ty
    = let (arg_tys,res_ty) = GHC.splitPiTys ty
      in GHC.sorryDoc "todo(1):" (GHC.ppr (arg_tys,res_ty))

    | GHC.ForAllTy{} <- ty
    = GHC.sorryDoc "todo(2):" (GHC.ppr ty)

    | GHC.TyConApp tycon tyargs <- ty
    = if not (length tyargs == GHC.tyConArity tycon)
        then GHC.sorryDoc "unsaturated TyConApp:" (GHC.ppr ty)
        else let tyname_str = nameToString (GHC.tyConName tycon) in
                 case tyname_str of
                     "Int" -> Gib.IntTy
                     "Float" -> Gib.FloatTy
                     "Bool" -> Gib.BoolTy
                     _oth  -> let tyvars = GHC.tyConTyVars tycon
                                  tyvars_var = map (Gib.TyVar . Gib.UserTv . Gib.toVar . varToString) tyvars
                              in Gib.PackedTy tyname_str tyvars_var
                     -- GHC.sorryDoc "todo(3):" (GHC.ppr ty)

    | GHC.TyVarTy v <- ty
    = Gib.TyVar (Gib.UserTv (Gib.toVar (varToString v)))

    | GHC.FunTy _ _ arg res <- ty
    = Gib.ArrowTy [ghcTyToGibTy arg] (ghcTyToGibTy res)

    | otherwise
    = GHC.sorryDoc "todo(4):" (GHC.ppr ty)


--------------------------------------------------------------------------------

varToString :: GHC.Var -> String
varToString = nameToString . GHC.varName

nameToString :: GHC.Name -> String
nameToString = GHC.occNameString . GHC.nameOccName
