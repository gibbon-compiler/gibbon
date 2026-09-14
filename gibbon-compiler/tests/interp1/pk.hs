-- Narrow widths in packed constructor fields, including negative values.
data M = M Int8 Int16 Int32 Int64 M | MNil

mk :: Int64 -> M
mk n = if n <= 0
       then MNil
       else M (toInt8 (0 - n)) (toInt16 (0 - n * 300))
              (toInt32 (0 - n * 100000)) (0 - n * 100000000000)
              (mk (n - 1))

sum8 :: M -> Int64
sum8 m = case m of
           MNil -> 0
           M a _b _c _d r -> toInt64 a + sum8 r

sum16 :: M -> Int64
sum16 m = case m of
            MNil -> 0
            M _a b _c _d r -> toInt64 b + sum16 r

sum32 :: M -> Int64
sum32 m = case m of
            MNil -> 0
            M _a _b c _d r -> toInt64 c + sum32 r

sum64 :: M -> Int64
sum64 m = case m of
            MNil -> 0
            M _a _b _c d r -> d + sum64 r

gibbon_main =
  let m = mk 5
      _p = printPacked m
      _n = printsym (quote "NEWLINE")
      _a = printint (sum8 m)
      _n1 = printsym (quote "NEWLINE")
      _b = printint (sum16 m)
      _n2 = printsym (quote "NEWLINE")
      _c = printint (sum32 m)
      _n3 = printsym (quote "NEWLINE")
      _d = printint (sum64 m)
      _n4 = printsym (quote "NEWLINE")
  in 0
