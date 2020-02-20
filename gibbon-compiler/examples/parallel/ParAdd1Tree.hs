module ParAdd1Tree where

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

add1Tree_seq :: Tree -> Tree
add1Tree_seq tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      let l1 = (add1Tree_seq l)
          r1 = (add1Tree_seq r)
      in Node (i+1) l1 r1

add1Tree :: Tree -> Tree
add1Tree tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      if i < 19
      then add1Tree_seq tr
      else
        let l1 = spawn (add1Tree l)
            r1 = (add1Tree r)
            _  = sync
        in Node (i+1) l1 r1

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
      x = mkTree_seq n
      y = iterate (add1Tree x)
  in (sumTree_seq y)
