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
  _ <- printsymIO (quote "Running pass sumEnergy (fold, uses=12): ")
  _ <- printsymIO (quote "NEWLINE")
  totEnergy <- iterateIO (\() -> sumEnergy octTree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (totEnergy)

main = runGibbonMainIO gibbon_main
