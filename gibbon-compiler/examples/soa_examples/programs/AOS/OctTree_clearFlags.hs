module Main where

import OctTreeBase

-- @BENCH adt_fields=16

gibbon_main =
  let _ = printsym (quote "Running program OctTree Physics Simulation: ")
      _ = printsym (quote "NEWLINE")
      octTree = buildOctree (8) 17 0 64

      _ = printsym (quote "Running pass clearFlags (map, uses=15): ")
      _ = printsym (quote "NEWLINE")
      octTree'' = iterate (clearFlags octTree)
      active = countActive octTree'' 60
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
  in active
