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
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C a b c ->
      let trp = par (sumFoo a) (sumFoo b) (sumFoo c)
          x = trp !!! 0
          y = trp !!! 1
          z = trp !!! 2
      in x + y + z
