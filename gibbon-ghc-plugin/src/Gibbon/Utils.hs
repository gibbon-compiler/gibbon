module Gibbon.Utils where

import qualified GHC.Plugins as GHC

varToString :: GHC.Var -> String
varToString = nameToString . GHC.varName

nameToString :: GHC.Name -> String
nameToString = GHC.occNameString . GHC.nameOccName
