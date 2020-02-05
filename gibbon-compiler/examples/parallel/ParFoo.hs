module ParFoo where

data Foo = A Int
         | B Int Foo Foo
         | C Int Foo Foo Foo

mkFoo_seq :: Int -> Foo
mkFoo_seq i =
  if i <= 0
  then A 1
  else if i == 1
       then B i (mkFoo_seq (i-1)) (mkFoo_seq (i-1))
       else
           let x = mkFoo_seq (i-1)
               y = mkFoo_seq (i-1)
               z = mkFoo_seq (i-1)
           in C i x y z


mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 1
  else if i == 1
       then B i (mkFoo (i-1)) (mkFoo (i-1))
       else
           if i < 10
           then mkFoo_seq i
           else let x = spawn (mkFoo (i-1))
                    y = spawn (mkFoo (i-1))
                    z = mkFoo (i-1)
                    _ = sync
                in C i x y z
{-

mkFoo2_seq :: Int -> (Int, Foo)
mkFoo2_seq i =
  if i <= 0
  then (i, A 1)
  else if i == 1
       then
           let p = mkFoo2_seq (i-1)
               q = mkFoo2_seq (i-1)
               x = p !!! 1
               y = q !!! 1
           in (i, B i x y)
       else
           let p = mkFoo2_seq (i-1)
               q = mkFoo2_seq (i-1)
               r = mkFoo2_seq (i-1)
               x = p !!! 1
               y = q !!! 1
               z = r !!! 1
           in (i, C i x y z)

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
           if i <= 10
           then mkFoo2_seq i
           else
               let p = spawn (mkFoo2 (i-1))
                   q = spawn (mkFoo2 (i-1))
                   r = mkFoo2 (i-1)
                   _ = sync
                   x = p !!! 1
                   y = q !!! 1
                   z = r !!! 1
               in (i, C i x y z)
-}

sumFoo_seq :: Foo -> Int
sumFoo_seq foo =
  case foo of
    A i     -> i
    B i a b   ->
      let x = sumFoo_seq a
          y = sumFoo_seq b
      in x + y
    C i a b c ->
      let x = sumFoo_seq a
          y = sumFoo_seq b
          z = sumFoo_seq c
      in x + y + z

sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B i a b   ->
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C i a b c ->
      if i < 10
      then sumFoo_seq foo
      else
          let x = spawn (sumFoo a)
              y = spawn (sumFoo b)
              z = sumFoo c
              _ = sync
          in x + y + z

copy_seq :: Foo -> Foo
copy_seq foo =
  case foo of
    A i     -> A i
    B i a b   ->
      let x = copy_seq a
          y = copy_seq b
      in B i x y
    C i a b c ->
      let x = copy_seq a
          y = copy_seq b
          z = copy_seq c
      in C i x y z

copy :: Foo -> Foo
copy foo =
  case foo of
    A i     -> A i
    B i a b   ->
      let x = copy a
          y = copy b
      in B i x y
    C i a b c ->
      if i < 10
      then copy_seq foo
      else
          let x = spawn (copy a)
              y = spawn (copy b)
              z = copy c
              _ = sync
          in C i x y z

gibbon_main =
  let -- a = mkFoo2 sizeParam
      -- x = a !!! 1

      n = sizeParam
      x = iterate (mkFoo n)
      y = iterate (copy x)
  in iterate (sumFoo y)
