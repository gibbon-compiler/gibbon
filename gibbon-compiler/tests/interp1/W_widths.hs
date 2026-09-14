w8 :: Int8 -> Int8
w8 x = x + 1

w16 :: Int16 -> Int16
w16 x = x + 1

w32 :: Int32 -> Int32
w32 x = x + 1

w64 :: Int64 -> Int64
w64 x = x + 1

gibbon_main =
  let _ = printint (w8 100)
      _ = printsym (quote "NEWLINE")
      _ = printint (w16 30000)
      _ = printsym (quote "NEWLINE")
      _ = printint (w32 2000000000)
      _ = printsym (quote "NEWLINE")
      _ = printint (w64 4000000000)
      _ = printsym (quote "NEWLINE")
  in 0
