data List = Cons Int Float List | Nil
{-# ANN type List "Factored" #-}

{-# ANN mkList "OPT:StoreScalarCounts" #-}
mkList :: Int -> List
mkList len =
  if len <= 0
  then Nil
  else let rst = mkList (len - 1)
       in Cons len 1.0 rst

sumList :: List -> Int
sumList xs =
  case xs of
    Nil -> 0
    Cons i f rst -> i + sumList rst

add1List :: List -> List
add1List xs =
  case xs of 
	Nil -> Nil
	Cons i f rst -> Cons (i + 1) f (add1List rst)

gibbon_main =
  let xs = mkList 10000
      xs' = add1List xs
  in sumList xs'
