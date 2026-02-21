{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat


import OctTreeBase

-- @BENCH adt_fields=16


gibbon_main = do
  _ <- printsymIO (quote "Running program OctTree Physics Simulation: ")
  _ <- printsymIO (quote "NEWLINE")
  let octTree = buildOctree (sizeParam + 8) 17 0 64
  _ <- printsymIO (quote "Running pass countActive (fold, uses=10): ")
  _ <- printsymIO (quote "NEWLINE")
  totActive <- iterateIO (\() -> countActive octTree 60)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (totActive)

main = runGibbonMainIO gibbon_main
