module Seq2DCorr where

coord :: Int -> (Float, Float, Float) -> Float
coord axis pt =
  if axis == 0
  then pt !!! 0
  else if axis == 1
  then pt !!! 1
  else pt !!! 2

getNextAxis_2D :: Int -> Int
getNextAxis_2D i = mod (i + 1) 2

min :: Float -> Float -> Float
min a b = if a .<. b then a else b

max :: Float -> Float -> Float
max a b = if a .>. b then a else b

cmp1 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp1 a b = floatToInt ((a !!! 0) .-. (b !!! 0))

cmp2 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp2 a b = floatToInt ((a !!! 1) .-. (b !!! 1))

cmp3 :: (Float, Float, Float) -> (Float, Float, Float) -> Int
cmp3 a b = floatToInt ((a !!! 2) .-. (b !!! 2))

sort :: Int -> [(Float, Float, Float)] -> [(Float, Float, Float)]
sort axis ls =
    if axis == 0
    -- This isn't safe, but avoids memory blowup
    then let _ = inplacevsort ls cmp1
         in ls
    else if axis == 1
    then let _ = inplacevsort ls cmp2
         in ls
    else let _ = inplacevsort ls cmp3
         in ls

--------------------------------------------------------------------------------
-- The main algorithm

data KdTree = KdLeaf Float  -- ^ x coord
                     Float  -- ^ y coord
                     Float  -- ^ z coord

            | KdNode Int    -- ^ number of elements in this node
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
  deriving Show

getMinX :: KdTree -> Float
getMinX tr =
  case tr of
    KdNode _ _ _ min_x _ _ _ _ _ _ _ -> min_x
    KdLeaf x _ _                     -> x

getMaxX :: KdTree -> Float
getMaxX tr =
  case tr of
    KdNode _ _ _ _ max_x _ _ _ _ _ _ -> max_x
    KdLeaf x _ _                     -> x

getMinY :: KdTree -> Float
getMinY tr =
  case tr of
    KdNode _ _ _ _ _ min_y _ _ _ _ _ -> min_y
    KdLeaf _ y _                     -> y

getMaxY :: KdTree -> Float
getMaxY tr =
  case tr of
    KdNode _ _ _ _ _ _ max_y _ _ _ _ -> max_y
    KdLeaf _ y _                     -> y

getMinZ :: KdTree -> Float
getMinZ tr =
  case tr of
    KdNode _ _ _ _ _ _ _ min_z _ _ _ -> min_z
    KdLeaf _ _ z                     -> z

getMaxZ :: KdTree -> Float
getMaxZ tr =
  case tr of
    KdNode _ _ _ _ _ _ _ _ max_z _ _ -> max_z
    KdLeaf _ _ z                     -> z


getElems :: KdTree -> Int
getElems tr =
  case tr of
    KdNode elems _ _ _ _ _ _ _ _ _ _ -> elems
    KdLeaf _ y _                     -> 1


fromListWithAxis :: Int -> [(Float, Float, Float)] -> KdTree
fromListWithAxis axis pts =
    let len = vlength pts in
    if len == 1
    then let pt = vnth 0 pts
         in KdLeaf (pt !!! 0) (pt !!! 1) (pt !!! 2)
    else let sorted_pts = sort axis pts
             pivot_idx  = div len 2
             pivot      = vnth pivot_idx sorted_pts
             left_pts   = vslice sorted_pts 0 pivot_idx
             right_pts  = vslice sorted_pts pivot_idx len
             next_axis  = getNextAxis_2D axis
             left_tr    = fromListWithAxis next_axis left_pts
             right_tr   = fromListWithAxis next_axis right_pts
             min_x      = min (getMinX left_tr) (getMinX right_tr)
             max_x      = max (getMaxX left_tr) (getMaxX right_tr)
             min_y      = min (getMinY left_tr) (getMinY right_tr)
             max_y      = max (getMaxY left_tr) (getMaxY right_tr)
             min_z      = min (getMinZ left_tr) (getMinZ right_tr)
             max_z      = max (getMaxZ left_tr) (getMaxZ right_tr)
             total_elems= (getElems left_tr) + (getElems right_tr)
         in KdNode total_elems axis (coord axis pivot) min_x max_x min_y max_y min_z max_z left_tr right_tr

-- | Build a KD-Tree out of a set of points
fromList :: [(Float, Float, Float)] -> KdTree
fromList pts = fromListWithAxis 0 pts


fromListWithAxis_par :: Int -> [(Float, Float, Float)] -> KdTree
fromListWithAxis_par axis pts =
    let len = vlength pts in
    -- 2 ^ 19 == 524288
    if len < 524288
    then fromListWithAxis axis pts
    -- if len == 1
    -- then let pt = vnth 0 pts
    --      in KdLeaf (pt !!! 0) (pt !!! 1) (pt !!! 2)
    else let sorted_pts = sort axis pts
             pivot_idx  = div len 2
             pivot      = vnth pivot_idx sorted_pts
             left_pts   = vslice sorted_pts 0 pivot_idx
             right_pts  = vslice sorted_pts pivot_idx len
             next_axis  = getNextAxis_2D axis
             left_tr    = spawn (fromListWithAxis_par next_axis left_pts)
             right_tr   = fromListWithAxis_par next_axis right_pts
             _          = sync
             min_x      = min (getMinX left_tr) (getMinX right_tr)
             max_x      = max (getMaxX left_tr) (getMaxX right_tr)
             min_y      = min (getMinY left_tr) (getMinY right_tr)
             max_y      = max (getMaxY left_tr) (getMaxY right_tr)
             min_z      = min (getMinZ left_tr) (getMinZ right_tr)
             max_z      = max (getMaxZ left_tr) (getMaxZ right_tr)
             total_elems= (getElems left_tr) + (getElems right_tr)
         in KdNode total_elems axis (coord axis pivot) min_x max_x min_y max_y min_z max_z left_tr right_tr

-- | Build a KD-Tree out of a set of points
fromList_par :: [(Float, Float, Float)] -> KdTree
fromList_par pts = fromListWithAxis_par 0 pts


-- | Sum of all points in KD-Tree
sumKdTree :: KdTree -> Float
sumKdTree tr =
  case tr of
    KdLeaf x y z -> x .+. y .+. z
    KdNode _ _ _ _ _ _ _ _ _ left right ->
      let o = sumKdTree left
          p = sumKdTree right
      in o .+. p

sumList0 :: Int -> Int -> [(Float, Float, Float)] -> Float -> Float
sumList0 i n ls acc =
  if i == n
  then acc
  else let p = vnth i ls
       in sumList0 (i+1) n ls (acc .+. (p !!! 0) .+. (p !!! 1) .+. (p !!! 2))

sumList :: [(Float, Float, Float)] -> Float
sumList ls =
  sumList0 0 (vlength ls) ls 0.0

--------------------------------------------------------------------------------

gibbon_main =
    let pts :: [(Float, Float, Float)]
        pts = readArrayFile ()
        n       = sizeParam
        radius  = intToFloat n
        tr      = iterate (fromList_par pts)
    in sumKdTree tr
