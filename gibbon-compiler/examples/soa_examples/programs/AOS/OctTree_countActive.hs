module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (sizeParam + 8) 17 0 64
      _ = printsym (quote "Running pass countActive (fold, uses=10): ")
      _ = printsym (quote "NEWLINE")
      totActive = iterate (countActive octTree 60)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in totActive
