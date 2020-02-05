module ParTree where

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


mkTree :: Int -> Tree
mkTree i =
  if i <= 0
  then Leaf 1
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

copy_seq :: Tree -> Tree
copy_seq foo =
  case foo of
    Leaf i     -> Leaf i
    Node i a b ->
      let x = copy_seq a
          y = copy_seq b
      in Node i x y

copy :: Tree -> Tree
copy foo =
  case foo of
    Leaf i     -> Leaf i
    Node i a b ->
      if i < 19
      then copy_seq foo
      else
          let x = spawn (copy a)
              y = copy b
              _ = sync
          in Node i x y

gibbon_main =
  let n = sizeParam
      x = mkTree_seq n
      -- y = iterate (copy x)
  in iterate (sumTree x)
