module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (sizeParam + 8) 17 0 64

      _ = printsym (quote "Running pass sumEnergy (fold, uses=12): ")
      _ = printsym (quote "NEWLINE")
      totEnergy = iterate (sumEnergy octTree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in totEnergy
