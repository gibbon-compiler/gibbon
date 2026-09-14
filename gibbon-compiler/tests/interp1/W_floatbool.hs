half :: Float -> Float
half x = x .+. 0.5

gibbon_main =
  let _ = printfloat (half 2.0)
      _ = printsym (quote "NEWLINE")
      _ = printbool True
      _ = printsym (quote "NEWLINE")
      _ = printbool False
      _ = printsym (quote "SPACE")
      _ = printint 7
      _ = printsym (quote "NEWLINE")
  in 0
