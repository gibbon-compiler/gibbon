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
  _ <- printsymIO (quote "Running pass scaleEnergy (map, uses=16): ")
  _ <- printsymIO (quote "NEWLINE")
  octTree' <- iterateIO (\() -> scaleEnergy octTree 9)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  let scaledEnergy = sumEnergy octTree'
  return scaledEnergy

main = runGibbonMainIO gibbon_main
