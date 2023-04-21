module Gibbon.Plugin1 ( plugin ) where

-- import qualified GHC.Plugins as GHC
import GHC.Linker as GHC
import GHC.Linker.Loader as GHC
import GHC.Plugins as GHC
import GHC.SysTools.Info
import GHC.Utils.Logger
import GHC.Driver.Session
import GHC.Driver.Backend
import GHC.Settings

import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Map as Map

--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = installGibbonPlugin }

installGibbonPlugin :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
installGibbonPlugin _ todos = return (linkCoreTodo : todos)

linkCoreTodo :: GHC.CoreToDo
linkCoreTodo = GHC.CoreDoPluginPass "testlinking" test
  where
    test :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
    test mod_guts = do
        GHC.liftIO $ print "[Gibbon Core Plugin (1)] Starting..."

        let cfile = "/home/ckoparka/chai/tree-velocity/gibbon-ghc-integration/plugin1/cbits/test1.c"
        let objfile = "/home/ckoparka/chai/tree-velocity/gibbon-ghc-integration/plugin1/cbits/test2.o"
        let adir = "/home/ckoparka/chai/tree-velocity/gibbon-ghc-integration/plugin1/cbits/"
        let aname = "test2"

        hsc_env <- getHscEnv
        dflags  <- getDynFlags

        -- (1) works.
        let mod_guts1 = mod_guts { mg_foreign_files = (mg_foreign_files mod_guts)
                                                        ++ [ ( RawObject, objfile) ]
                                 }

{-
        -- (2) doesn't work.
        let dflags' = dflags { ldInputs = (ldInputs dflags) ++ (map optionOfPath [ objfile ]) }
        liftIO $ loadCmdLineLibs (hscInterp hsc_env) (hsc_env { hsc_dflags = dflags'})
        -- -- liftIO $ print (backend dflags)
        -- loader_st <- liftIO $ showLoaderState (hscInterp hsc_env)
        -- putMsg loader_st

        -- (3) doesn't work.
        let allObjs = map optionOfPath [ objfile ]
        logger <- getLogger
        when (not (isNoLink (ghcLink dflags))) $ liftIO $ do
          linker_info <- getLinkerInfo logger dflags
          writeIORef (rtldInfo dflags)
            $ Just
            $ case linker_info of
                GnuLD     opts -> GnuLD     (nub (opts ++ allObjs))
                GnuGold   opts -> GnuGold   (nub (opts ++ allObjs))
                DarwinLD  opts -> DarwinLD  (nub (opts ++ allObjs))
                SolarisLD opts -> SolarisLD (nub (opts ++ allObjs))
                AixLD     opts -> AixLD     (nub (opts ++ allObjs))
                LlvmLLD   opts -> LlvmLLD   (nub (opts ++ allObjs))
                UnknownLD      -> UnknownLD  -- no linking performed?
-}
        pure mod_guts1


--------------------------------------------------------------------------------

alterToolSettings :: (ToolSettings -> ToolSettings) -> DynFlags -> DynFlags
alterToolSettings f dynFlags = dynFlags { toolSettings = f (toolSettings dynFlags) }

addOptl :: String -> DynFlags -> DynFlags
addOptl f = alterToolSettings (\s -> s { toolSettings_opt_l   = f : toolSettings_opt_l s})

optionOfPath :: FilePath -> Option
optionOfPath = FileOption []
