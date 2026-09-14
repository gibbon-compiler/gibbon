-- Division and exponentiation, including the negative cases where SML's
-- `div`/`mod` disagree with C's `/`/`%`.
gibbon_main =
  let _ = printint (7 / 3)
      _ = printsym (quote "NEWLINE")
      _ = printint (mod 7 3)
      _ = printsym (quote "NEWLINE")
      _ = printint ((0 - 7) / 3)
      _ = printsym (quote "NEWLINE")
      _ = printint (mod (0 - 7) 3)
      _ = printsym (quote "NEWLINE")
      _ = printint (2 ^ 10)
      _ = printsym (quote "NEWLINE")
      _ = printint (3 ^ 5)
      _ = printsym (quote "NEWLINE")
      _ = printint (0 - 7)
      _ = printsym (quote "NEWLINE")
  in 0
