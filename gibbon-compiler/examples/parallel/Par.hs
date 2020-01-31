module Par where

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 1
  else if i == 1
       then B (mkFoo (i-1)) (mkFoo (i-1))
       else C (mkFoo (i-1)) (mkFoo (i-1)) (mkFoo (i-1))


sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B a b   ->
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C a b c ->
      let x = sumFoo a
          y = sumFoo b
          z = sumFoo c
      in x + y + z

copy :: Foo -> Foo
copy foo =
  case foo of
    A i     -> A i
    B a b   ->
      let x = copy a
          y = copy b
      in B x y
    C a b c ->
      let x = spawn (copy a)
          y = spawn (copy b)
          z = copy c
          _ = sync
      in C x y z

gibbon_main =
  let x = mkFoo 7
      y = copy x
  in sumFoo y
