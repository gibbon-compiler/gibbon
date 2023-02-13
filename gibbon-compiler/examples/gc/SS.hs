data T = K2 T T | K0

reduce :: T -> Int
reduce tr =
  case tr of
    K0 -> 0
    K2 x y -> 1 + reduce x + reduce y

foo :: Int -> T
foo n =
  if n == 0
  then K0
  else K2 (foo (n-1)) (foo (n-1))

bar :: Int -> T
bar n =
  let tr = foo n
  in case tr of
       K0 -> K2 K0 K0
       K2 _ _ -> tr

gibbon_main =
  let tr1 = iterate (foo 2)
      tr2 = iterate (bar 2)
  in reduce tr1 + reduce tr2
