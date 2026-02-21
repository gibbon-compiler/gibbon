module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (8) 17 0 64
      _ = printsym (quote "Running pass scaleEnergy (map, uses=16): ")
      _ = printsym (quote "NEWLINE")
      octTree' = iterate (scaleEnergy octTree 9)
      scaledEnergy = sumEnergy octTree'
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in scaledEnergy
