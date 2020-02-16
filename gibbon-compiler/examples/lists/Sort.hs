module Sort where

-- It's a for loop.
lesser :: Int -> Int -> Int -> Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
lesser i n elt0 elt1 ls acc =
  if i == n
  then acc
  else  let x   = vnth i ls
            rst = lesser (i+1) n elt0 elt1 ls acc
        in if (x !!! 0) < elt0 && (x !!! 1) < elt1
           then vsnoc rst x
           else rst

-- It's a for loop.
greater_eq :: Int -> Int -> Int -> Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
greater_eq i n elt0 elt1 ls acc =
  if i == n
  then acc
  else  let x   = vnth i ls
            rst = greater_eq (i+1) n elt0 elt1 ls acc
        in if (x !!! 0) >= elt0 && (x !!! 1) >= elt1
           then vsnoc rst x
           else rst

append :: Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
append n ls1 ls2 =
  if n == vlength ls2
  then ls1
  else append (n+1) (vsnoc ls1 (vnth n ls2)) ls2

sort :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
sort ls acc =
  let n = vlength ls in
  if n == 0
  then acc
  else if n == 1
  then vsnoc acc (vnth 0 ls)
  else let pivot = vnth (n-1) ls

           acc1 :: [(Int,Int)]
           acc1 = vempty
           ls1  = lesser 0 ((vlength ls) - 1) (pivot !!! 0) (pivot !!! 1) ls acc1

           acc2 :: [(Int,Int)]
           acc2 = vempty
           ls2  = sort ls1 acc2

           acc3 :: [(Int,Int)]
           acc3 = vempty
           ls3  = greater_eq 0 ((vlength ls) - 1) (pivot !!! 0) (pivot !!! 1) ls acc3

           acc4 :: [(Int,Int)]
           acc4 = vempty
           ls4  = sort ls3 acc4

           ls5  = vsnoc ls2 pivot
           ls6  = append 0 ls5 ls4

       in ls6

gibbon_main =
    let ls0 :: [(Int, Int)]
        ls0 = vempty

        ls1 = vsnoc ls0 (10, 5)
        ls2 = vsnoc ls1 (2, 3)

        acc :: [(Int,Int)]
        acc = vempty

        ls3 = sort ls2 acc
        x = vnth 0 ls3
        y = vnth 1 ls3

    in (x!!!0, x !!! 1, y !!! 0, y !!! 1)
