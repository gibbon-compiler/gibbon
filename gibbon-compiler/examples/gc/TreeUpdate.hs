-- 3,6,7,5,3,5,6,2,9,1,2,7,0,9,3,6,0,6,2,6,1,8,7,9,2,
-- 0,2,3,7,5,9,2,2,8,9,7,3,6,1,2,9,3,1,9,4,7,8,4,5,0,
-- 3,6,1,0,6,3,2,0,6,1,5,5,4,7,6,5,6,9,3,7,4,5,2,5,4,
-- 7,4,4,3,0,7,8,6,8,8,4,3,1,4,9,2,0,6,8,9,2,6,6,4,9

module TreeUpdate where

import Gibbon.Vector

data SearchTree = Null
                | Leaf Int
                | Node Int SearchTree SearchTree

copySearchTree :: SearchTree -> SearchTree
copySearchTree tr =
  case tr of
    Null -> Null
    Leaf i -> Leaf i
    Node i x y -> Node i (copySearchTree x) (copySearchTree y)

helper :: Int -> Int -> SearchTree
helper s e =
  if e < s
  then Null
  else if s == e
       then Leaf s
       else let m = ((e - s) / 2) + s
            in Node m (helper s (m - 1)) (helper (m + 1) e)

countnodes :: SearchTree -> Int
countnodes tr =
  case tr of
    Null       -> 0
    Leaf _     -> 1
    Node _ l r -> 1 + countnodes l + countnodes r


sumTree :: SearchTree -> Int
sumTree tr =
  case tr of
    Null       -> 0
    Leaf n     -> n
    Node n l r -> n + sumTree l + sumTree r


treeInsert :: SearchTree -> Int -> SearchTree
treeInsert tr n =
  case tr of
    Null    -> Leaf n
    Leaf n1 -> if n == n1
               then Leaf n1
               else if n < n1
                    then Node n1 (Leaf n) Null
                    else Node n1 Null     (Leaf n)
    Node n1 l r -> if n1 == n
                   then Node n1 (copyPacked l) (copyPacked r)
                   else if n < n1
                        then Node n1 (copyPacked l) (treeInsert r n)
                        else Node n1 (treeInsert l n) (copyPacked r)

minTree :: SearchTree -> Int
minTree tr =
  case tr of
    Null   -> 0
    Leaf n -> n
    Node n l r -> case l of
                    Null -> n
                    Leaf m -> m
                    Node _ y z -> minTree y

treeDelete :: SearchTree -> Int -> SearchTree
treeDelete tr n =
  case tr of
    Null -> Null
    Leaf n1 -> if n1 == n
               then Null
               else Leaf n1
    Node n1 l r -> if n1 == n
                   then let k = minTree r
                        in Node k (copyPacked l) (treeDelete r k)
                   else if n1 < n
                        then Node n1 (copyPacked l) (treeDelete r n)
                        else Node n1 (treeDelete l n) (copyPacked r)

loop :: Vector Int -> Int -> SearchTree -> Int -> SearchTree
loop nums idx tr n =
  if n == 0
  then tr
  else let idx1 = mod (idx+1) (length nums)
             -- if idx == (length nums - 1) then 0 else idx+1
           j = nth nums idx1
       in if mod j 2 == 0
          then loop nums idx1 (treeInsert tr j) (n-1)
          else loop nums idx1 (treeDelete tr (j-1)) (n-1)


gibbon_main =
  let pts :: Vector Int
      pts = readArrayFile Nothing
      n = sizeParam
      tr = (helper 0 3)
      upd = iterate (loop pts 0 tr n)
  in countnodes upd
