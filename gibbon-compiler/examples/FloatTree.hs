module FloatTree where

data Tree = Leaf Float
          | Node Float Tree Tree

mkTree_seq :: Float -> Tree
mkTree_seq i =
  if i .<=. 0.0
  then Leaf frand
  else
      let x = mkTree_seq (i .-. 1.0)
          y = mkTree_seq (i .-. 1.0)
      in Node i x y

add1Tree_seq :: Tree -> Tree
add1Tree_seq tr =
  case tr of
    Leaf i     -> Leaf (i .+. 1.0)
    Node i l r ->
      let l1 = (add1Tree_seq l)
          r1 = (add1Tree_seq r)
      in Node (i .+. 1.0) l1 r1

sumTree_seq :: Tree -> Float
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in x .+. y

gibbon_main =
  let n = sizeParam
      x = mkTree_seq (intToFloat n)
      y = add1Tree_seq x
  in sqrt (sumTree_seq y)
