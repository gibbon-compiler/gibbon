module Main where

data PList = Cons Int PList | Nil

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

sumList :: PList -> Int
sumList xs =
  case xs of
    Nil -> 0
    Cons y ys -> y + sumList ys

gibbon_main =
  let n   = sizeParam
      ls  = buildList n
      acc = Nil
      rev = reverse ls acc
  in (sumList ls == sumList rev)
