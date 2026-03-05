module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (sizeParam + 8) 17 0 64

      _ = printsym (quote "Running pass fmmPotential (fold_like, uses=12): ")
      _ = printsym (quote "NEWLINE")
      fmmPot = iterate (fmmPotential octTree 21 4 70)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in fmmPot
