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
  _ <- printsymIO (quote "Running pass barnesHutPotential (fold_like, uses=11): ")
  _ <- printsymIO (quote "NEWLINE")
  bhPotential <- iterateIO (\() -> barnesHutPotential octTree 21 60)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (bhPotential)

main = runGibbonMainIO gibbon_main
