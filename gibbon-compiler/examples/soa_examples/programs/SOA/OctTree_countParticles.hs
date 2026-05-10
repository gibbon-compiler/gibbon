module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (sizeParam + 8) 17 0 64

      _ = printsym (quote "Running pass countParticles (fold, uses=8): ")
      _ = printsym (quote "NEWLINE")
      totParticles = iterate (countParticles octTree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in totParticles
