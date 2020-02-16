module Sort where

-- It's a for loop.
lesser :: Int -> Int -> Int -> Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
lesser i n elt0 elt1 ls acc =
  if i == n
  then acc
  else  let x   = vnth i ls
            rst = lesser (i+1) n elt0 elt1 ls acc
        in if (x !!! 0) < elt0
           then vsnoc rst x
           else rst

-- It's a for loop.
greater_eq :: Int -> Int -> Int -> Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
greater_eq i n elt0 elt1 ls acc =
  if i == n
  then acc
  else  let x   = vnth i ls
            rst = greater_eq (i+1) n elt0 elt1 ls acc
        in if (x !!! 0) >= elt0
           then vsnoc rst x
           else rst

append :: Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
append n ls1 ls2 =
  if n == vlength ls2
  then ls1
  else append (n+1) (vsnoc ls1 (vnth n ls2)) ls2

sort0 :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
sort0 ls acc =
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
           ls2  = sort0 ls1 acc2

           acc3 :: [(Int,Int)]
           acc3 = vempty
           ls3  = greater_eq 0 ((vlength ls) - 1) (pivot !!! 0) (pivot !!! 1) ls acc3

           acc4 :: [(Int,Int)]
           acc4 = vempty
           ls4  = sort0 ls3 acc4

           ls5  = vsnoc ls2 pivot
           ls6  = append 0 ls5 ls4

       in ls6

sort :: [(Int, Int)] -> [(Int, Int)]
sort ls =
    let acc :: [(Int, Int)]
        acc = vempty
    in sort0 ls acc

psort0 :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
psort0 ls acc =
  let n = vlength ls in
  if n <= 1000
  then sort0 ls acc
  else let pivot = vnth (n-1) ls

           acc1 :: [(Int,Int)]
           acc1 = vempty
           ls1  = lesser 0 ((vlength ls) - 1) (pivot !!! 0) (pivot !!! 1) ls acc1

           acc2 :: [(Int,Int)]
           acc2 = vempty
           ls2  = spawn (psort0 ls1 acc2)

           acc3 :: [(Int,Int)]
           acc3 = vempty
           ls3  = greater_eq 0 ((vlength ls) - 1) (pivot !!! 0) (pivot !!! 1) ls acc3

           acc4 :: [(Int,Int)]
           acc4 = vempty
           ls4  = spawn (psort0 ls3 acc4)

           _    = sync

           ls5  = vsnoc ls2 pivot
           ls6  = append 0 ls5 ls4

       in ls6

psort :: [(Int, Int)] -> [(Int, Int)]
psort ls =
    let acc :: [(Int, Int)]
        acc = vempty
    in psort0 ls acc


--------------------------------------------------------------------------------

mkList0 :: Int -> [(Int, Int)] -> [(Int, Int)]
mkList0 n acc=
  if n == 0
  then acc
  else let i = mod rand 50
           j = mod rand 50
       in mkList0 (n-1) (vsnoc acc (i,j))

mkList :: Int -> [(Int, Int)]
mkList n =
  let acc :: [(Int, Int)]
      acc = vempty
  in mkList0 n acc

sumList0 :: Int -> Int -> [(Int, Int)] -> Int -> Int
sumList0 i n ls acc =
  if i == n
  then acc
  else let p = vnth i ls
       in sumList0 (i+1) n ls (acc + (p !!! 0) + (p !!! 1))

sumList :: [(Int, Int)] -> Int
sumList ls =
  sumList0 0 (vlength ls) ls 0

--------------------------------------------------------------------------------

gibbon_main =
    let n   = sizeParam
        ls  = mkList n
        ls2 = iterate (psort ls)
    in (sumList ls, sumList ls2)
