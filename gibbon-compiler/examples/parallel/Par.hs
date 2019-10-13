module Par where

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 10
  else if i == 1
       then B (mkFoo (i-1)) (mkFoo (i-1))
       else C (mkFoo (i-1)) (mkFoo (i-1)) (mkFoo (i-1))


{-# ANN sumFoo (gibbon_payload, [0]) #-}
sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B a b   ->
      let tup = (sumFoo a) .||. (sumFoo b)
          x = tup !!! 0
          y = tup !!! 1
      in x + y
    C a b c ->
      let trp = (sumFoo a) .||. ((sumFoo b) .||. (sumFoo c))
          x = trp !!! 0
          tup = trp !!! 1
          y = tup !!! 0
          z = tup !!! 1
      in x + y + z
