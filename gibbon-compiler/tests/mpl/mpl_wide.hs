-- Values past 2^31: MLton's default Int is 32 bits and traps on overflow.
big :: Int64 -> Int64
big x = x * 1000

gibbon_main =
  let _ = printint (big 4000000)
      _ = printsym (quote "NEWLINE")
      _ = printint (0 - (big 4000000))
      _ = printsym (quote "NEWLINE")
  in 0
