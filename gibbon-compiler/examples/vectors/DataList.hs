module DataList where

{-

type List a = [a]
empty_ll = []
cons_ll x ls = x : ls
head_ll ls = head ls
tail_ll ls = tail ls
is_empty_ll ls = null ls
alloc_ll = []

-}

data Ints = MkInts (List (Int, Int))
  deriving Show

mkInts :: Int -> Ints
mkInts n =
    let vec :: List (Int, Int)
        -- vec = generate n (\i -> (i, i))
        vec = alloc_ll
        vec2 = cons_ll (1, 1) alloc_ll
    in MkInts vec2

sumInts' :: List (Int, Int) -> Int
sumInts' ls =
  if is_empty_ll ls
  then 0
  else let (a,b) = head_ll ls
           tl = tail_ll ls
       in a + b + sumInts' tl

sumInts :: Ints -> Int
sumInts is =
    case is of
        MkInts ls -> sumInts' ls

gibbon_main = sumInts (mkInts 11)
