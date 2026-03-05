module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (sizeParam + 8) 17 0 64

      _ = printsym (quote "Running pass sumMass (fold, uses=10): ")
      _ = printsym (quote "NEWLINE")
      totMass = iterate (sumMass octTree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in totMass
