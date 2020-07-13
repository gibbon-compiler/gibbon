module BinTree where

import Fib

data Tree = Leaf Int
          | Node Int Tree Tree

-- build

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf 6765
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

mkTree_par :: Int -> Int -> Tree
mkTree_par cutoff i =
  if i < cutoff
  then (mkTree_seq i)
  else
      let x = spawn (mkTree_par cutoff (i-1))
          y = mkTree_par cutoff (i-1)
          _ = sync
      in Node i x y

-- buildfib

mkTreeFib_seq :: Int -> Tree
mkTreeFib_seq i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      let x = mkTreeFib_seq (i-1)
          y = mkTreeFib_seq (i-1)
      in Node i x y


mkTreeFib_par :: Int -> Int -> Tree
mkTreeFib_par cutoff i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      if i < cutoff
      then mkTreeFib_seq i
      else let x = spawn (mkTreeFib_par cutoff (i-1))
               y = mkTreeFib_par cutoff (i-1)
               _ = sync
           in Node i x y


-- add1

add1Tree_seq :: Tree -> Tree
add1Tree_seq tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      let l1 = (add1Tree_seq l)
          r1 = (add1Tree_seq r)
      in Node (i+1) l1 r1

add1Tree_par :: Int -> Tree -> Tree
add1Tree_par cutoff tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      if i < cutoff
      then add1Tree_seq tr
      else
        let l1 = spawn (add1Tree_par cutoff l)
            r1 = (add1Tree_par cutoff r)
            _  = sync
        in Node (i+1) l1 r1

-- sum

sumTree_seq :: Tree -> Int
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in i + x + y

sumTree_par :: Int -> Tree -> Int
sumTree_par cutoff foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      if i < cutoff
      then sumTree_seq foo
      else
          let x = spawn (sumTree_par cutoff a)
              y = sumTree_par cutoff b
              _ = sync
          in i + x + y
