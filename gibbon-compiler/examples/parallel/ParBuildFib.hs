module ParBuildFib where

data Tree = Leaf Int
          | Node Int Tree Tree

fib_seq :: Int -> Int
fib_seq n =
    if n == 0
    then 0
    else if n == 1
    then 1
    else
        let x = fib_seq (n - 1)
            y = fib_seq (n - 2)
        in x + y

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y


mkTree :: Int -> Int -> Tree
mkTree cutoff i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      if i < cutoff
      then mkTree_seq i
      else let x = spawn (mkTree cutoff (i-1))
               y = mkTree cutoff (i-1)
               _ = sync
           in Node i x y

sumTree_seq :: Tree -> Int
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in i + x + y

gibbon_main =
  let n = sizeParam
      cutoff = 19
      x = iterate (mkTree cutoff n)
  in (sumTree_seq x)
