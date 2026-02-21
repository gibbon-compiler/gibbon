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
  _ <- printsymIO (quote "Running pass fmmPotential (fold_like, uses=12): ")
  _ <- printsymIO (quote "NEWLINE")
  fmmPot <- iterateIO (\() -> fmmPotential octTree 21 4 70)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (fmmPot)

main = runGibbonMainIO gibbon_main
