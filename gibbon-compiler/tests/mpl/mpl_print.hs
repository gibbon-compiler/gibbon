-- Every printing primitive, and the special symbols.
half :: Float -> Float
half x = x .+. 0.5

gibbon_main =
  let _ = printfloat (half 2.0)
      _ = printsym (quote "NEWLINE")
      _ = printfloat (0.0 .-. 1.25)
      _ = printsym (quote "NEWLINE")
      _ = printbool True
      _ = printsym (quote "SPACE")
      _ = printbool False
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "LEFTPAREN")
      _ = printsym (quote "COMMA")
      _ = printsym (quote "RIGHTPAREN")
      _ = printsym (quote "NEWLINE")
  in 0
