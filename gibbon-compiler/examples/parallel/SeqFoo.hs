module SeqFoo where

data Foo = A Int
         | B Int Foo Foo
         | C Int Foo Foo Foo

mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 1
  else if i == 1
       then B i (mkFoo (i-1)) (mkFoo (i-1))
       else
           let x = mkFoo (i-1)
               y = mkFoo (i-1)
               z = mkFoo (i-1)
           in C i x y z

{-

mkFoo2 :: Int -> (Int, Foo)
mkFoo2 i =
  if i <= 0
  then (i, A 1)
  else if i == 1
       then
           let p = mkFoo2 (i-1)
               q = mkFoo2 (i-1)
               x = p !!! 1
               y = q !!! 1
           in (i, B i x y)
       else
           let p = (mkFoo2 (i-1))
               q = (mkFoo2 (i-1))
               r = mkFoo2 (i-1)
               x = p !!! 1
               y = q !!! 1
               z = r !!! 1
           in (i, C i x y z)

-}

sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B i a b   ->
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C i a b c ->
      let x = (sumFoo a)
          y = (sumFoo b)
          z = sumFoo c
      in x + y + z

copy :: Foo -> Foo
copy foo =
  case foo of
    A i     -> A i
    B i a b   ->
      let x = copy a
          y = copy b
      in B i x y
    C i a b c ->
      let x = (copy a)
          y = (copy b)
          z = copy c
      in C i x y z

gibbon_main =
  let -- a = mkFoo2 sizeParam
      -- x = a !!! 1

      n = sizeParam
      x = iterate (mkFoo n)
      y = iterate (copy x)
  in iterate (sumFoo y)
