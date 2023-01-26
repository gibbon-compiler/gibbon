-- Test case for https://github.com/iu-parfunc/gibbon/issues/185.

data Foo = K4 Foo Int Int Int
         | K3 Foo Int Int
         | K2 Foo Int
         | K1 Foo
         | K0

foo :: Foo -> Int
foo y =
  case y of
    K4 x i j k -> foo x + i + j + k
    K3 x i j   -> foo x + i + j
    K2 x i     -> foo x + i
    K1 x       -> foo x
    K0         -> 0

bar :: Foo -> Int
bar y =
  case y of
    K4 x i j k -> k
    K3 x i j   -> j
    K2 x i     -> i
    K1 x       -> bar x
    K0         -> 0

gibbon_main =
  let e = K4 (K3 (K2 (K1 K0) 1) 2 3) 4 5 6
  in (foo e, bar e)
