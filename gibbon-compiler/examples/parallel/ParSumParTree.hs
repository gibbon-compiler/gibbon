module ParSumTree where

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

mkTree :: Int -> Tree
mkTree i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      if i < 19
      then mkTree_seq i
      else let x = spawn (mkTree (i-1))
               y = mkTree (i-1)
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

sumTree :: Tree -> Int
sumTree foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      if i < 19
      then sumTree_seq foo
      else
          let x = spawn (sumTree a)
              y = sumTree b
              _ = sync
          in i + x + y

gibbon_main =
  let n = sizeParam
      x = mkTree n
      y = iterate (sumTree x)
  in y
