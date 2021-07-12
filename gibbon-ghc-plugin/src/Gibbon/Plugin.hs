module Gibbon.Plugin ( plugin ) where

import qualified GHC.Plugins as GHC

--------------------------------------------------------------------------------
-- GHC Core-to-Core Plugin
--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = installGibbonPlugin
                           }
  where
    installGibbonPlugin :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
    installGibbonPlugin _ todos = return (gibbonCoreTodo : todos)

gibbonCoreTodo :: GHC.CoreToDo
gibbonCoreTodo = GHC.CoreDoPluginPass "TEST" test
  where
    test :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
    test mod_guts = do
        GHC.liftIO $ print "[Gibbon Core] test..."
        hsc_env <- GHC.getHscEnv
        external_package_state <- GHC.liftIO $ GHC.hscEPS hsc_env
        let all_ids = GHC.nameEnvElts (GHC.eps_PTE external_package_state)
        GHC.putMsg (GHC.ppr (map (\tyt -> case tyt of
                                              GHC.AnId i -> Just (i, GHC.maybeUnfoldingTemplate (GHC.realIdUnfolding i))
                                              _ -> Nothing)
                                 all_ids))
        pure mod_guts
