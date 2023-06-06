module Sharing where

data Tree = Leaf Int
          | Node Tree Tree

mkSharedTree :: Int -> Tree
mkSharedTree n =
  if n == 0
  then Leaf 1
  else
    let tr = mkSharedTree (n-1)
    in case tr of
         Leaf i   -> Node (copyPacked tr) (copyPacked tr)
         Node _ _ -> Node (copyPacked tr) (copyPacked tr)

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n   -> n
    Node x y -> sumTree x + sumTree y

data PList = Cons Int PList | Nil

-- copyPList :: PList -> PList
-- copyPList ls =
--   case ls of
--     Nil -> Nil
--     Cons i rst -> Cons i (copyPList rst)

buildList :: Tree -> Int -> PList
buildList tr n =
  if n == 0
    then Nil
    else Cons n (buildList tr (n-1))

reverse :: Tree -> PList -> PList -> PList
reverse tr xs acc =
  case xs of
    Nil -> acc
    Cons y ys -> reverse tr ys (Cons y acc)


sumPList :: PList -> Int
sumPList xs =
  case xs of
    Nil -> 0
    Cons y ys -> y + sumPList ys

addints :: Int -> Int -> Int
addints x y = x + y

gibbon_main =
  let n   = sizeParam
      tr  = mkSharedTree 1
      -- ls = buildList tr n
      ls  = iterate (addints 10 20)
  in sumTree tr
