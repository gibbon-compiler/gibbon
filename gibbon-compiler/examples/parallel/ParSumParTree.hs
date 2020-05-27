module ParSumTree where

data Tree = Leaf Int
          | Node Int Tree Tree

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf 6765
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

mkTree :: Int -> Int -> Tree
mkTree cutoff i =
  if i <= 0
  then Leaf 6765
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

sumTree :: Int -> Tree -> Int
sumTree cutoff foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      if i < cutoff
      then sumTree_seq foo
      else
          let x = spawn (sumTree cutoff a)
              y = sumTree cutoff b
              _ = sync
          in i + x + y

gibbon_main =
  let n = sizeParam
      cutoff = 19
      x = mkTree cutoff n
      y = iterate (sumTree cutoff x)
  in y
