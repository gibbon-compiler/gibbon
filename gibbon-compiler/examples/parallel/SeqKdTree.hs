module SeqKdTree where

coord :: Int -> (Int, Int) -> Int
coord axis pt =
  if axis == 0
  then pt !!! 0
  else pt !!! 1

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

data KdTree  = KdNode Int     -- ^ splitting axis (0 == x, 1 == y)
                      Int     -- ^ x-coord
                      Int     -- ^ y-coord
                      KdTree  -- ^ left
                      KdTree  -- ^ right
             | KdEmpty
  deriving Show

-- | Build a KD-Tree out of a set of points
fromList :: [(Int, Int)] -> KdTree
fromList pts = fromListWithAxis 0 pts

-- | A KD-Tree that's split at 'axis'
fromListWithAxis :: Int -> [(Int, Int)] -> KdTree
fromListWithAxis axis pts =
    let len = vlength pts in
    if len == 0
    then KdEmpty
    else
      let sorted_pts = sort axis pts
          pivot_idx  = div len 2
          pivot      = vnth pivot_idx sorted_pts
          left_pts   = slice 0 pivot_idx sorted_pts
          right_pts  = slice (pivot_idx+1) len sorted_pts
          next_axis  = getNextAxis_2D axis
          left_tr    = fromListWithAxis next_axis left_pts
          right_tr   = fromListWithAxis next_axis right_pts
      in KdNode axis (pivot !!! 0) (pivot !!! 1) left_tr right_tr

-- | Distance between two points
dist :: (Int, Int) -> (Int, Int) -> Int
dist a b =
  let a_x = a !!! 0
      a_y = a !!! 1
      b_x = b !!! 0
      b_y = b !!! 1
  in ((a_x - b_x) ^ 2) + ((a_y - b_y) ^ 2)

-- | Return the point that is closest to a
least_dist :: (Int, Int) -> (Int, Int) -> (Int, Int) -> (Int, Int)
least_dist a b c =
  let d1 = dist a b
      d2 = dist a c
  in if d1 < d2 then b else c

-- | Return the nearest neighbor of probe
nearest :: KdTree -> (Int, Int) -> (Int, Int)
nearest tr probe =
  case tr of
    KdEmpty -> (-100,-100)
    KdNode axis pivot_x pivot_y left right ->
      let pivot   =  (pivot_x, pivot_y)
          tst_probe = coord axis probe
          tst_pivot = coord axis pivot
      in
      if tst_probe < tst_pivot
      then find_nearest pivot probe tst_pivot tst_probe left right
      else find_nearest pivot probe tst_pivot tst_probe right left

-- | Find the closest point to probe in a KD-tree
find_nearest :: (Int, Int) -> (Int, Int) -> Int -> Int -> KdTree -> KdTree -> (Int, Int)
find_nearest pivot probe tst_pivot tst_probe side other =
  let best0 = nearest side probe
      candidate1 = least_dist probe best0 pivot
      -- whether the difference between the splitting coordinate of the search point and current node
      -- is less than the distance (overall coordinates) from the search point to the current best.
  in if ((tst_probe - tst_pivot) ^ 2) <= dist probe candidate1
     then let candidate2   = nearest other probe
              best1 = least_dist probe candidate1 candidate2
          in best1
     else candidate1

-- | Sum of all points in KD-Tree
sumKdTree :: KdTree -> Int
sumKdTree tr =
  case tr of
    KdEmpty -> 0
    KdNode _ x y left right ->
      let o = sumKdTree left
          p = sumKdTree right
      in x + y + o + p

--------------------------------------------------------------------------------

mkList0 :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
mkList0 n limit acc=
  if n == 0
  then acc
  else let i = mod rand limit
           j = mod rand limit
       in mkList0 (n-1) limit (vsnoc acc (i,j))

-- | Create a list of 'n' elements where each point is in [0,(n*100)] square
mkList :: Int -> [(Int, Int)]
mkList n =
  let acc :: [(Int, Int)]
      acc = vempty
      limit = (n*10) + 1
  in mkList0 n limit acc

-- | A for loop that sums up all elements in the array
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
        tr  = iterate (fromList ls)
        m   = (div n 2)
        probe = (m, m)
        got   = nearest tr probe
        d     = dist probe got
    in (probe !!! 0, probe !!! 1, got !!! 0, got !!! 1)
