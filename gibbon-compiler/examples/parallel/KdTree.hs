module KdTree where

import Gibbon.Vector
import Gibbon.Vector.Parallel

-- import MergeSort

coord :: Int -> (Float, Float, Float) -> Float
coord axis pt =
  if axis == 0
  then pt !!! 0
  else if axis == 1
  then pt !!! 1
  else pt !!! 2

print3dPoint :: (Float, Float, Float) -> ()
print3dPoint tup =
    let (a,b,c) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ")")
    in ()

getNextAxis_2D :: Int -> Int
getNextAxis_2D i = mod (i + 1) 2

min :: Float -> Float -> Float
min a b = if a .<. b then a else b

max :: Float -> Float -> Float
max a b = if a .>. b then a else b

eqPt :: (Float, Float, Float) -> (Float, Float, Float) -> Bool
eqPt a b =
    let (ax,ay,az) = a
        (bx,by,bz) = b
    in ax .==. bx && ay .==. by && az .==. bz

cmp1 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp1 a b =
    let (ax,_,_) = a
        (bx,_,_) = b
    in floatToInt (ax .-. bx)

cmp2 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp2 a b =
    let (_,ay,_) = a
        (_,by,_) = b
    in floatToInt (ay .-. by)

cmp3 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp3 a b =
    let (_,_,az) = a
        (_,_,bz) = b
    in floatToInt (az .-. bz)

sort :: Int -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
sort axis ls =
    let ls2 = copy ls in
    if axis == 0
    then inplacevsort ls2 cmp1
    else if axis == 1
    then inplacevsort ls2 cmp2
    else inplacevsort ls2 cmp3

sort_par :: Int -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
sort_par axis ls =
    let ls2 = copy_par ls in
    if axis == 0
    then inplacevsort ls2 cmp1
    else if axis == 1
    then inplacevsort ls2 cmp2
    else inplacevsort ls2 cmp3

-- sort_par2 :: Int -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
-- sort_par2 axis ls =
--     if axis == 0
--     then mergeSort cmp1 ls
--     else if axis == 1
--     then mergeSort cmp2 ls
--     else mergeSort cmp3 ls

--------------------------------------------------------------------------------
-- The main algorithm

data KdTree = KdLeaf Float  -- ^ x coord
                     Float  -- ^ y coord
                     Float  -- ^ z coord

            | KdNode Float  -- x coord
                     Float  -- y coord
                     Float  -- z coood
                     Int    -- ^ number of elements in this node
                     Int    -- ^ splitting axis (0 == x, 1 == y)
                     Float  -- ^ split value
                     Float  -- ^ min_x
                     Float  -- ^ max_x
                     Float  -- ^ min_y
                     Float  -- ^ max_y
                     Float  -- ^ min_z
                     Float  -- ^ max_z
                     KdTree -- ^ left
                     KdTree -- ^ right

           | KdEmpty
  deriving Show

getMinX :: KdTree -> Float
getMinX tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ min_x _ _ _ _ _ _ _ -> min_x
    KdLeaf x _ _                     -> x

getMaxX :: KdTree -> Float
getMaxX tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ max_x _ _ _ _ _ _ -> max_x
    KdLeaf x _ _                     -> x

getMinY :: KdTree -> Float
getMinY tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ min_y _ _ _ _ _ -> min_y
    KdLeaf _ y _                     -> y

getMaxY :: KdTree -> Float
getMaxY tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ max_y _ _ _ _ -> max_y
    KdLeaf _ y _                     -> y

getMinZ :: KdTree -> Float
getMinZ tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ _ min_z _ _ _ -> min_z
    KdLeaf _ _ z                     -> z

getMaxZ :: KdTree -> Float
getMaxZ tr =
  case tr of
    KdEmpty -> 0.0
    KdNode _ _ _ _ _ _ _ _ _ _ _ max_z _ _ -> max_z
    KdLeaf _ _ z                     -> z


getElems_kdtree :: KdTree -> Int
getElems_kdtree tr =
  case tr of
    KdEmpty -> 0
    KdNode _ _ _ elems _ _ _ _ _ _ _ _ _ _ -> elems
    KdLeaf _ y _                     -> 1

getx_kdtree :: KdTree -> Float
getx_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode x _ _ _ _ _ _ _ _ _ _ _ _ _ -> x
        KdLeaf x _ _                       -> x

gety_kdtree :: KdTree -> Float
gety_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode _ y _ _ _ _ _ _ _ _ _ _ _ _ -> y
        KdLeaf _ y _                       -> y

getz_kdtree :: KdTree -> Float
getz_kdtree tr =
    case tr of
        KdEmpty -> 0.0
        KdNode _ _ z _ _ _ _ _ _ _ _ _ _ _ -> z
        KdLeaf _ _ z                       -> z

fromListWithAxis_seq :: Int -> Vector (Float, Float, Float) -> KdTree
fromListWithAxis_seq axis pts =
    let len = vlength pts in
    if len == 0
    then KdEmpty
    else if len == 1
    then let (x,y,z) = nth pts 0
         in KdLeaf x y z
    else let sorted_pts = sort axis pts
             pivot_idx  = div len 2
             pivot      = nth sorted_pts pivot_idx
             (x,y,z)    = pivot
             left_pts   = slice 0 pivot_idx sorted_pts
             right_pts  = slice (pivot_idx+1) (len - pivot_idx - 1) sorted_pts
             next_axis  = getNextAxis_2D axis
             left_tr    = fromListWithAxis_seq next_axis left_pts
             right_tr   = fromListWithAxis_seq next_axis right_pts
             min_x      = min (getMinX left_tr) (getMinX right_tr)
             max_x      = max (getMaxX left_tr) (getMaxX right_tr)
             min_y      = min (getMinY left_tr) (getMinY right_tr)
             max_y      = max (getMaxY left_tr) (getMaxY right_tr)
             min_z      = min (getMinZ left_tr) (getMinZ right_tr)
             max_z      = max (getMaxZ left_tr) (getMaxZ right_tr)
             total_elems= (getElems_kdtree left_tr) + (getElems_kdtree right_tr) + 1
         in KdNode x y z total_elems axis (coord axis pivot) min_x max_x min_y max_y min_z max_z left_tr right_tr

-- | Build a KD-Tree out of a set of points
fromList_seq :: Vector (Float, Float, Float) -> KdTree
fromList_seq pts = fromListWithAxis_seq 0 pts

fromListWithAxis_par :: Int -> Int -> Vector (Float, Float, Float) -> KdTree
fromListWithAxis_par cutoff axis pts =
    let len = vlength pts in
    if len < cutoff
    then fromListWithAxis_seq axis pts
    else let sorted_pts = sort_par axis pts
             pivot_idx  = div len 2
             pivot      = nth sorted_pts pivot_idx
             (x,y,z)    = pivot
             left_pts   = slice 0 pivot_idx sorted_pts
             right_pts  = slice (pivot_idx+1) (len - pivot_idx - 1) sorted_pts
             next_axis  = getNextAxis_2D axis
             left_tr    = spawn (fromListWithAxis_par cutoff next_axis left_pts)
             right_tr   = fromListWithAxis_par cutoff next_axis right_pts
             _          = sync
             min_x      = min x (min (getMinX left_tr) (getMinX right_tr))
             max_x      = max x (max (getMaxX left_tr) (getMaxX right_tr))
             min_y      = min y (min (getMinY left_tr) (getMinY right_tr))
             max_y      = max y (max (getMaxY left_tr) (getMaxY right_tr))
             min_z      = min z (min (getMinZ left_tr) (getMinZ right_tr))
             max_z      = max z (max (getMaxZ left_tr) (getMaxZ right_tr))
             total_elems= (getElems_kdtree left_tr) + (getElems_kdtree right_tr) + 1
         in KdNode x y z total_elems axis (coord axis pivot) min_x max_x min_y max_y min_z max_z left_tr right_tr

-- | Build a KD-Tree out of a set of points
fromList_par :: Int -> Vector (Float, Float, Float) -> KdTree
fromList_par cutoff pts = fromListWithAxis_par cutoff 0 pts

--------------------------------------------------------------------------------

-- | Maps a list of points to a list of their nearest neighbor.
allNearest_seq :: KdTree -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
allNearest_seq tr ls =
    map (\p -> nearest tr p) ls

allNearest_par :: KdTree -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
allNearest_par tr ls =
    map_par (\p -> nearest tr p) ls

nearest :: KdTree -> (Float, Float, Float) -> (Float, Float, Float)
nearest tr query =
    case tr of
        KdEmpty -> (0.0,0.0,0.0)
        KdLeaf x y z -> (x,y,z)
        KdNode x y z total_points axis split_val min_x max_x min_y max_y min_z max_z left_tr right_tr ->
            let pivot = (x,y,z)
                tst_query = coord axis query
                tst_pivot = coord axis pivot
            in if tst_query .<. tst_pivot
               then find_nearest pivot query tst_pivot tst_query left_tr right_tr
               else find_nearest pivot query tst_pivot tst_query right_tr left_tr

-- | Find the closest point to query in a KD-tree
find_nearest :: (Float, Float, Float) -> (Float, Float, Float) -> Float -> Float -> KdTree -> KdTree -> (Float, Float, Float)
find_nearest pivot query tst_pivot tst_query good_side other_side =
  let best0 = nearest good_side query
      candidate1 = least_dist query best0 pivot
      -- whether the difference between the splitting coordinate of the search point and current node
      -- is less than the distance (overall coordinates) from the search point to the current best.
      nearest_other_side = tst_query .-. tst_pivot
  in if (nearest_other_side .*. nearest_other_side) .<=. (dist3d query candidate1)
     then let candidate2 = nearest other_side query
              best1 = least_dist query candidate1 candidate2
          in best1
     else candidate1
  -- in let candidate2 = nearest other_side query
  --        best1 = least_dist query candidate1 candidate2
  --    in best1

-- | Return the point that is closest to a
least_dist :: (Float, Float, Float) -> (Float, Float, Float) -> (Float, Float, Float) -> (Float, Float, Float)
least_dist a b c =
  let d1 = dist3d a b
      d2 = dist3d a c
  in if d1 .<. d2 then b else c

--------------------------------------------------------------------------------

-- | Sum of all points in KD-Tree
sumKdTree :: KdTree -> Float
sumKdTree tr =
  case tr of
    KdEmpty -> 0.0
    KdLeaf x y z -> x .+. y .+. z
    KdNode x y z _ _ _ _ _ _ _ _ _ left right ->
      let o = sumKdTree left
          p = sumKdTree right
      in x .+. y .+. z .+. o .+. p

countLeaves :: KdTree -> Int
countLeaves tr =
  case tr of
    KdEmpty -> 0
    KdLeaf _ _ _ -> 1
    KdNode _ _ _ _ _ _ _ _ _ _ _ _ left right ->
      let o = countLeaves left
          p = countLeaves right
      in o + p

sumList :: Vector (Float, Float, Float) -> Float
sumList ls = foldl (\acc (pt :: (Float, Float, Float)) ->
                        let (x,y,z) = pt
                        in acc .+. x .+. y .+. z)
                   0.0 ls

-- | Distance between two points
dist3d :: (Float, Float, Float) -> (Float, Float, Float) -> Float
dist3d a b =
  let (a_x, a_y, a_z) = a
      (b_x, b_y, b_z) = b
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
      d3 = (a_z .-. b_z)
  in (d1 .*. d1) .+. (d2 .*. d2) .+. (d3 .*. d3)


-- | Two point correlation
countCorr_seq :: (Float, Float, Float) -> Float -> KdTree -> Int
countCorr_seq probe radius tr =
  case tr of
    KdEmpty -> 0

    KdLeaf x y z ->
      if (dist3d probe (x, y, z)) .<. (radius .*. radius)
      then 1
      else 0

    KdNode x y z elems axis split_val min_x max_x min_y max_y min_z max_z left right ->
      -- Ported over from ASTBenchmarks
      let center_x  = (min_x .+. max_x) ./. 2.0
          center_y  = (min_y .+. max_y) ./. 2.0
          center_z  = (min_z .+. max_z) ./. 2.0
          (probe_x, probe_y, probe_z) = probe
          d_x       = probe_x .-. center_x
          d_y       = probe_y .-. center_y
          d_z       = probe_z .-. center_z
          boxdist_x = (max_x .-. min_x) ./. 2.0
          boxdist_y = (max_y .-. min_y) ./. 2.0
          boxdist_z = (max_z .-. min_z) ./. 2.0
          sum       = (d_x .*. d_x) .+. (d_y .*. d_y) .+. (d_z .*. d_z)
          boxsum    = (boxdist_x .*. boxdist_x) .+. (boxdist_y .*. boxdist_y) .+. (boxdist_z .*. boxdist_z)
      in if (sum .-. boxsum) .<. (radius .*. radius)
         then let n1 = countCorr_seq probe radius left
                  n2 = countCorr_seq probe radius right
              in if (dist3d probe (x, y, z)) .<. (radius .*. radius)
                 then n1 + n2 + 1
                 else n1 + n2
         else
             if (dist3d probe (x, y, z)) .<. (radius .*. radius)
             then 1
             else 0

-- | Two point correlation
countCorr_par :: Int -> (Float, Float, Float) -> Float -> KdTree -> Int
countCorr_par cutoff probe radius tr =
  case tr of
    KdEmpty -> 0
    KdLeaf x y z ->
      if (dist3d probe (x, y, z)) .<. (radius .*. radius)
      then 1
      else 0

    KdNode x y z elems axis split_val min_x max_x min_y max_y min_z max_z left right ->
      if elems < cutoff then countCorr_seq probe radius tr else
      -- Ported over from ASTBenchmarks
      let center_x  = (min_x .+. max_x) ./. 2.0
          center_y  = (min_y .+. max_y) ./. 2.0
          center_z  = (min_z .+. max_z) ./. 2.0
          (probe_x, probe_y, probe_z) = probe
          d_x       = probe_x .-. center_x
          d_y       = probe_y .-. center_y
          d_z       = probe_z .-. center_z
          boxdist_x = (max_x .-. min_x) ./. 2.0
          boxdist_y = (max_y .-. min_y) ./. 2.0
          boxdist_z = (max_z .-. min_z) ./. 2.0
          sum       = (d_x .*. d_x) .+. (d_y .*. d_y) .+. (d_z .*. d_z)
          boxsum    = (boxdist_x .*. boxdist_x) .+. (boxdist_y .*. boxdist_y) .+. (boxdist_z .*. boxdist_z)
      in if (sum .-. boxsum) .<. (radius .*. radius)
         then let n1 = spawn (countCorr_par cutoff probe radius left)
                  n2 = countCorr_par cutoff probe radius right
                  _  = sync
              in if (dist3d probe (x, y, z)) .<. (radius .*. radius)
                 then n1 + n2 + 1
                 else n1 + n2
         else
             if (dist3d probe (x, y, z)) .<. (radius .*. radius)
             then 1
             else 0

--------------------------------------------------------------------------------

check_buildkdtree :: Vector (Float, Float, Float) -> KdTree -> ()
check_buildkdtree pts tr =
    let p = sumList pts
        q = sumKdTree tr
        err = (q .-. p)
    in print_check (float_abs (q .-. p) .<. 0.01)

check_countcorr :: Vector (Float, Float, Float) -> (Float, Float, Float) -> Int -> Float -> ()
check_countcorr pts query actual radius =
    let radius_sq = radius .*. radius
        expected = foldl (\acc pt  ->
                             if (dist3d query pt) .<. radius_sq
                             then acc + 1
                             else acc)
                   0 pts
        _ = printsym (quote "Expected: ")
        _ = printint expected
        _ = printsym (quote "\n")
        _ = printsym (quote "Actual: ")
        _ = printint actual
        _ = printsym (quote "\n")
    in print_check (expected == actual)

check_nearest :: Vector (Float, Float, Float) -> Vector (Float, Float, Float) -> Float -> ()
check_nearest pts actual radius =
    let n = length pts
        idxs = generate n (\i -> i)
        radius_sq = radius .*. radius
        tup = foldl (\(acc :: (Bool, Int, Int)) i ->
                         let pt = nth pts i
                             nn = nth actual i
                             (acc_b, acc_inexact, acc_not_near) = acc
                         in if eqPt pt nn
                            then (acc_b && True, acc_inexact, acc_not_near)
                            else if (dist3d pt nn) .<. radius_sq
                                 then (acc_b && True, acc_inexact+1, acc_not_near)
                                 else (False, acc_inexact+1, acc_not_near+1))
              (True, 0, 0) idxs
        (is_ok, inexact, not_near) = tup
        _ = printsym (quote "Inexact: ")
        _ = printint inexact
        _ = printsym (quote "\n")
        _ = printsym (quote "Not near: ")
        _ = printint not_near
        _ = printsym (quote "\n")
    in print_check is_ok
