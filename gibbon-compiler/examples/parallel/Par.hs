module Par where

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
           let x = spawn (mkFoo (i-1))
               y = spawn (mkFoo (i-1))
               z = mkFoo (i-1)
               _ = sync
           in C i x y z

sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B i a b   ->
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C i a b c ->
      let x = spawn (sumFoo a)
          y = spawn (sumFoo b)
          z = sumFoo c
          _ = sync
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
      let x = spawn (copy a)
          y = spawn (copy b)
          z = copy c
          _ = sync
      in C i x y z

gibbon_main =
  let x = mkFoo 7
      y = copy x
  in sumFoo y
