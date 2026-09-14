data Tree = Leaf Int | Node Tree Tree

mk :: Int -> Tree
mk n = if n <= 0 then Leaf 1 else Node (mk (n-1)) (mk (n-1))

gibbon_main =
  let t = mk 2
      _ = printPacked t
      _ = printsym (quote "NEWLINE")
      _ = printint 42
      _ = printsym (quote "NEWLINE")
  in 0
