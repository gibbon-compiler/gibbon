{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat


import OctTreeBase

-- @BENCH adt_fields=16

instance GibbonShow Octree where
  gibbonShow _ = "0"


gibbon_main = do
  _ <- printsymIO (quote "Running program OctTree Physics Simulation: ")
  _ <- printsymIO (quote "NEWLINE")
  let octTree = buildOctree (sizeParam + 8) 17 0 64
  _ <- printsymIO (quote "Running pass clearFlags (map, uses=15): ")
  _ <- printsymIO (quote "NEWLINE")
  octTree'' <- iterateIO (\() -> clearFlags octTree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  let active = countActive octTree'' 60
  return active

main = runGibbonMainIO gibbon_main
