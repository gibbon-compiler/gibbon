module Par where

data Tree = Leaf Int
          | Node Int Tree Tree

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf 1
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

sumTree_seq :: Tree -> Int
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in i + x + y

copy_seq :: Tree -> Tree
copy_seq foo =
  case foo of
    Leaf i     -> Leaf i
    Node i a b ->
      let x = copy_seq a
          y = copy_seq b
      in Node i x y

gibbon_main =
  let n = sizeParam
      x = (mkTree_seq n)
      -- y = iterate (copy_seq x)
  in iterate (sumTree_seq x)
