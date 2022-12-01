module Reverse where

data PList = Cons Int PList | Nil

copyPList :: PList -> PList
copyPList ls =
  case ls of
    Nil -> Nil
    Cons i rst -> Cons i (copyPList rst)


reverse :: PList -> PList -> PList
reverse xs acc =
  case xs of
    Nil -> acc
    Cons y ys -> reverse ys (Cons y acc)

buildList :: Int -> PList
buildList n =
  if n == 0
    then Nil
    else Cons n (buildList (n-1))

sumPList :: PList -> Int
sumPList xs =
  case xs of
    Nil -> 0
    Cons y ys -> y + sumPList ys

gibbon_main =
  let n   = sizeParam
      ls  = buildList n
      -- m = sumList ls
      acc = Nil
      rev = iterate (reverse ls acc)
  in sumPList rev
