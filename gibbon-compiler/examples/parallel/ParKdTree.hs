module ParKdTree where

coord :: Int -> Int -> Int -> Int
coord axis x y =
  if axis == 0
  then x
  else y

getNextAxis_2D :: Int -> Int
getNextAxis_2D i = mod (i + 1) 2

cmp1 :: (Int, Int) -> (Int, Int) -> Int
cmp1 a b = (a !!! 0) - (b !!! 0)

cmp2 :: (Int, Int) -> (Int, Int) -> Int
cmp2 a b = (a !!! 1) - (b !!! 1)

sort :: Int -> [(Int, Int)] -> [(Int, Int)]
sort axis ls =
    if axis == 0
    then vsort ls cmp1
    else vsort ls cmp2

slice0 :: Int -> Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
slice0 i n ls acc =
  if i == n
  then acc
  else  let x = vnth i ls
        in slice0 (i+1) n ls (vsnoc acc x)

slice :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
slice i n ls =
  let  acc :: [(Int, Int)]
       acc = vempty
  in slice0 i n ls acc

--------------------------------------------------------------------------------
-- The main algorithm

data KdTree  = KdNode Int     -- ^ axis
                      Int     -- ^ x-coord
                      Int     -- ^ y-coord
                      KdTree  -- ^ left
                      KdTree  -- ^ right
             | KdEmpty
  deriving Show

fromList :: [(Int, Int)] -> KdTree
fromList pts = fromListWithAxis 0 0 pts

fromListWithAxis :: Int -> Int -> [(Int, Int)] -> KdTree
fromListWithAxis depth axis pts =
    if depth > 10
    then pFromListWithAxis depth axis pts
    else let len = vlength pts in
    if len == 0
    then KdEmpty
    else
      let sorted_pts = sort axis pts
          pivot_idx  = div len 2
          pivot      = vnth pivot_idx sorted_pts
          left_pts   = slice 0 pivot_idx sorted_pts
          right_pts  = slice (pivot_idx+1) len sorted_pts
          next_axis  = getNextAxis_2D axis
          left_tr    = fromListWithAxis (depth+1) next_axis left_pts
          right_tr   = fromListWithAxis (depth+1) next_axis right_pts
      in KdNode axis (pivot !!! 0) (pivot !!! 1) left_tr right_tr

pFromList :: [(Int, Int)] -> KdTree
pFromList pts = pFromListWithAxis 0 0 pts

pFromListWithAxis :: Int -> Int -> [(Int, Int)] -> KdTree
pFromListWithAxis depth axis pts =
    if depth < 10
    then fromListWithAxis depth axis pts
    else let len = vlength pts in
    if len == 0
    then KdEmpty
    else
      let sorted_pts = sort axis pts
          pivot_idx  = div len 2
          pivot      = vnth pivot_idx sorted_pts
          left_pts   = slice 0 pivot_idx sorted_pts
          right_pts  = slice (pivot_idx+1) len sorted_pts
          next_axis  = getNextAxis_2D axis
          left_tr    = spawn (pFromListWithAxis (depth+1) next_axis left_pts)
          right_tr   = pFromListWithAxis (depth+1) next_axis right_pts
          _          = sync
      in KdNode axis (pivot !!! 0) (pivot !!! 1) left_tr right_tr

dist :: Int -> Int -> Int -> Int -> Int
dist a_x a_y b_x b_y = ((a_x - b_x) ^ 2) + ((a_y - b_y) ^ 2)

least_dist :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int)
least_dist a_x a_y b_x b_y c_x c_y =
  let d1 = dist a_x a_y b_x b_y
      d2 = dist a_x a_y c_x c_y
  in if d1 < d2
     then (b_x, b_y)
     else (c_x, c_y)

nearest :: KdTree -> Int -> Int -> (Int, Int)
nearest tr probe_x probe_y =
  case tr of
    KdEmpty -> (-100,-100)
    KdNode axis pivot_x pivot_y left right ->
      let tst_probe = coord axis probe_x probe_y
          tst_pivot = coord axis pivot_x pivot_y
      in
      if tst_probe < tst_pivot
      then find_nearest pivot_x pivot_y probe_x probe_y tst_pivot tst_probe left right
      else find_nearest pivot_x pivot_y probe_x probe_y tst_pivot tst_probe right left

find_nearest :: Int -> Int -> Int -> Int -> Int -> Int -> KdTree -> KdTree -> (Int, Int)
find_nearest pivot_x pivot_y probe_x probe_y tst_pivot tst_probe tr1 tr2 =
  let best0 = nearest tr1 probe_x probe_y
      best0_x = best0 !!! 0
      best0_y = best0 !!! 1
      candidate1 = least_dist probe_x probe_y best0_x best0_y pivot_x pivot_y
      candidate1_x = candidate1 !!! 0
      candidate1_y = candidate1 !!! 1
      -- whether the difference between the splitting coordinate of the search point and current node
      -- is less than the distance (overall coordinates) from the search point to the current best.
  in if ((tst_probe - tst_pivot) ^ 2) <= dist probe_x probe_y candidate1_x candidate1_y
     then let candidate2   = nearest tr2 probe_x probe_y
              candidate2_x = candidate2 !!! 0
              candidate2_y = candidate2 !!! 1
              best1 = least_dist probe_x probe_y candidate1_x candidate1_y candidate2_x candidate2_y
          in best1
     else candidate1


sumKdTree :: KdTree -> Int
sumKdTree tr =
  case tr of
    KdEmpty -> 0
    KdNode _ x y left right ->
      let m = coord 0 x y
          n = coord 1 x y
          o = sumKdTree left
          p = sumKdTree right
      in m + n + o + p

--------------------------------------------------------------------------------

mkList0 :: Int -> [(Int, Int)] -> [(Int, Int)]
mkList0 n acc=
  if n == 0
  then acc
  else let i = mod rand n
           j = mod rand n
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
        -- Start out sequential, and if depth > 100, switch to parallel
        tr = iterate (fromList ls)
        m  = (div n 2)
        p  = nearest tr m m
        d  = dist (p !!! 0) (p !!! 1) m m
    -- in (sumKdTree tr, sumList ls)
    in (m, m, p)
