{-# LANGUAGE DeriveDataTypeable #-}

module Gibbon.Plugin ( plugin, PackedAnn(..) ) where

import qualified GHC.Plugins as GHC
import qualified GHC.Utils.Outputable as Ppr
import           GHC.Types.Var.Set as GHC
import           Data.Data ( Data )
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- GHC Core-to-Core Plugin
--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = installGibbonPlugin
                           , GHC.pluginRecompile = GHC.purePlugin }

installGibbonPlugin :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
installGibbonPlugin _ todos = return (gibbonCoreTodo : todos)

gibbonCoreTodo :: GHC.CoreToDo
gibbonCoreTodo = GHC.CoreDoPluginPass "GibbonLiftPacked" test
  where
    test :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
    test mod_guts = do
        GHC.liftIO $ print "[Gibbon Core Plugin] Starting..."

        -- Things defined in other modules and libraries.
        hsc_env <- GHC.getHscEnv
        external_package_state <- GHC.liftIO $ GHC.hscEPS hsc_env
        let external_ids = GHC.nameEnvElts (GHC.eps_PTE external_package_state)
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
        let (module_binds_ls,module_binds,module_ids) =
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
                       in GHC.pprTrace "(1):" (GHC.ppr (x,rhs,GHC.exprSomeFreeVarsList GHC.isId rhs))
                          (fixpoint dcons_ls binds_ls1 sucked_in1 xs1)
                  else case GHC.lookupVarEnv external_unfoldings x of
                           Nothing ->
                              -- GHC.pprSorry ("No unfolding available for:") (GHC.ppr x)
                               GHC.pprTrace "ERROR:" (GHC.ppr (Ppr.text "No unfolding available for:" Ppr.<> GHC.ppr x))
                                   (fixpoint dcons_ls binds_ls sucked_in xs)
                           Just rhs ->
                               let binds_ls1 = (x,rhs):binds_ls
                                   sucked_in1 = GHC.extendDVarSet sucked_in x
                                   xs1 = (GHC.exprSomeFreeVarsList GHC.isId rhs) ++ xs
                                   str = varToString x
                               in GHC.pprTrace "(2):" (GHC.ppr (x,rhs,GHC.exprSomeFreeVarsList GHC.isId rhs))
                                  fixpoint dcons_ls binds_ls1 sucked_in1 xs1

        -- The main thing.
        let (dcons,binds) = fixpoint [] [] GHC.emptyDVarSet to_lift

        GHC.putMsg (Ppr.text "\nDatacons:\n----------------------------------------" Ppr.$$ (GHC.ppr dcons))
        GHC.putMsg (Ppr.text "\nTransitive closure:\n----------------------------------------" Ppr.$$ (GHC.ppr binds))
        pure mod_guts

type PackedAnnEnv = GHC.NameEnv PackedAnn

data PackedAnn = LiftPacked
    deriving Data

instance Ppr.Outputable PackedAnn where
    ppr LiftPacked = Ppr.text "LiftPacked"


-- Things that are not included in the transitive closure.
excludedFromClos :: Set.Set String
excludedFromClos = Set.fromList $
    [ "I#" ] ++
    [ "$fOrdInt", "compareInt", "ltInt", "leInt", "gtInt", "geInt", "$fOrdInt_$cmax", "$fOrdInt_$cmin"] ++
    [ "$fEqInt", "eqInt", "neInt" ] ++
    [ "$fNumInt", "$fNumInt_$c+", "$fNumInt_$c-", "$fNumInt_$c*",
      "$fNumInt_$cnegate", "$fNumInt_$cabs", "$fNumInt_$csignum",
      "$fNumInt_$cfromInteger" ]

varToString :: GHC.Var -> String
varToString = GHC.occNameString . GHC.nameOccName . GHC.varName
