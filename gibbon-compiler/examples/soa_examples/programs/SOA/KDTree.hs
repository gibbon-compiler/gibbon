-- @BENCH adt_fields=17
data KDTree
  = KDNode Int    -- splitDim (0=x, 1=y, 2=z)
           Int    -- splitVal
           Int    -- bboxMinX
           Int    -- bboxMinY
           Int    -- bboxMinZ
           Int    -- bboxMaxX
           Int    -- bboxMaxY
           Int    -- bboxMaxZ
           Int    -- objectCount
           Int    -- flags
           KDTree KDTree
  | KDLeaf Int    -- pointX
           Int    -- pointY
           Int    -- pointZ
           Int    -- mass / weight
           Int    -- objectId
  | KDEmpty

{-# ANN type KDTree "Factored" #-}

-- Build a synthetic balanced binary KD-tree, cycling split axis by depth.
buildKD :: Int -> Int -> KDTree
buildKD d axis =
  if d == 0
  then KDLeaf d (d + 1) (d + 2) (d * 3) d
  else
    let nextAxis = mod (axis + 1) 3
        splitVal = d * 11 + axis
        l = buildKD (d - 1) nextAxis
        r = buildKD (d - 1) nextAxis
    in KDNode axis splitVal
              (0 - d) (0 - d) (0 - d)
              d d d
              (d * 2) (mod d 2)
              l r

-- Absolute value for Int.
absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

-- 3D Manhattan distance between two points.
dist3 :: Int -> Int -> Int -> Int -> Int -> Int -> Int
dist3 x1 y1 z1 x2 y2 z2 =
  absI (x1 - x2) + absI (y1 - y2) + absI (z1 - z2)

-- Integer minimum.
minI :: Int -> Int -> Int
minI a b = if a < b then a else b

-- Integer maximum.
maxI :: Int -> Int -> Int
maxI a b = if a > b then a else b

-- Lower bound distance from a coordinate to a 1D interval.
axisLowerBound :: Int -> Int -> Int -> Int
axisLowerBound q lo hi =
  if q < lo
  then lo - q
  else if q > hi
       then q - hi
       else 0

-- Lower bound Manhattan distance from a query point to an axis-aligned bbox.
bboxLowerBound :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
bboxLowerBound minX minY minZ maxX maxY maxZ qx qy qz =
  axisLowerBound qx minX maxX
  + axisLowerBound qy minY maxY
  + axisLowerBound qz minZ maxZ

-- Upper bound Manhattan distance from a query point to an axis-aligned bbox.
bboxUpperBound :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
bboxUpperBound minX minY minZ maxX maxY maxZ qx qy qz =
  maxI (absI (qx - minX)) (absI (qx - maxX))
  + maxI (absI (qy - minY)) (absI (qy - maxY))
  + maxI (absI (qz - minZ)) (absI (qz - maxZ))

-- Read one coordinate (x/y/z) chosen by split axis.
coordAt :: Int -> Int -> Int -> Int -> Int
coordAt axis x y z =
  if axis == 0
  then x
  else if axis == 1
       then y
       else z

-- Nearest-neighbor distance query with split-plane and bbox pruning.
nearestDist :: KDTree -> Int -> Int -> Int -> Int
nearestDist t qx qy qz =
  case t of
    KDLeaf x y z _ _ ->
      dist3 x y z qx qy qz

    KDNode splitDim splitVal minX minY minZ maxX maxY maxZ _ _ l r ->
      let qCoord = coordAt splitDim qx qy qz
          -- Distance to splitting plane on the active axis.
          planeDist = absI (qCoord - splitVal)
          -- Lower bound from query to this node's bounding box.
          boxDist = bboxLowerBound minX minY minZ maxX maxY maxZ qx qy qz
          -- Child distances (computed unconditionally for Gibbon compiler stability).
          dl = nearestDist l qx qy qz
          dr = nearestDist r qx qy qz
          -- Visit the side containing the query point first (near side).
          near = if qCoord < splitVal then dl else dr
          far  = if qCoord < splitVal then dr else dl
      in if boxDist >= near
         -- If bbox lower bound is already worse than current best, prune.
         then near
         else if planeDist < near
         -- Split plane intersects current best ball, so far side may help.
         then minI near far
         -- Otherwise far side cannot beat current best.
         else near

    KDEmpty ->
      1000000000

-- Check if a point is inside an axis-aligned query box.
pointInBox :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Bool
pointInBox x y z qMinX qMaxX qMinY qMaxY qMinZ qMaxZ =
  if x < qMinX then False else
  if x > qMaxX then False else
  if y < qMinY then False else
  if y > qMaxY then False else
  if z < qMinZ then False else
  if z > qMaxZ then False else
  True

-- Check if a node bbox is disjoint from an axis-aligned query box.
bboxDisjoint :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Bool
bboxDisjoint minX minY minZ maxX maxY maxZ qMinX qMaxX qMinY qMaxY qMinZ qMaxZ =
  if maxX < qMinX then True else
  if minX > qMaxX then True else
  if maxY < qMinY then True else
  if minY > qMaxY then True else
  if maxZ < qMinZ then True else
  if minZ > qMaxZ then True else
  False

-- Range searching: count points inside an axis-aligned query box.
-- Uses bbox rejection plus split-plane routing to recurse into relevant subtrees.
countInRange :: KDTree -> Int -> Int -> Int -> Int -> Int -> Int -> Int
countInRange t qMinX qMaxX qMinY qMaxY qMinZ qMaxZ =
  case t of
    KDLeaf x y z _ _ ->
      if pointInBox x y z qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
      then 1
      else 0

    KDNode splitDim splitVal minX minY minZ maxX maxY maxZ _ _ l r ->
      let disjoint = bboxDisjoint minX minY minZ maxX maxY maxZ qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
          qLo = coordAt splitDim qMinX qMinY qMinZ
          qHi = coordAt splitDim qMaxX qMaxY qMaxZ
          cl = countInRange l qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
          cr = countInRange r qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
      in if disjoint
         then 0
         else if qHi < splitVal
              then cl
              else if qLo > splitVal
                   then cr
                   else cl + cr

    KDEmpty ->
      0

-- Range searching: sum masses of points inside an axis-aligned query box.
sumMassInRange :: KDTree -> Int -> Int -> Int -> Int -> Int -> Int -> Int
sumMassInRange t qMinX qMaxX qMinY qMaxY qMinZ qMaxZ =
  case t of
    KDLeaf x y z mass _ ->
      if pointInBox x y z qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
      then mass
      else 0

    KDNode splitDim splitVal minX minY minZ maxX maxY maxZ _ _ l r ->
      let disjoint = bboxDisjoint minX minY minZ maxX maxY maxZ qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
          qLo = coordAt splitDim qMinX qMinY qMinZ
          qHi = coordAt splitDim qMaxX qMaxY qMaxZ
          ml = sumMassInRange l qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
          mr = sumMassInRange r qMinX qMaxX qMinY qMaxY qMinZ qMaxZ
      in if disjoint
         then 0
         else if qHi < splitVal
              then ml
              else if qLo > splitVal
                   then mr
                   else ml + mr

-- Two-point correlation style pass:
-- count points whose distance from a reference point lies in [rLo, rHi].
twoPointCorrelation :: KDTree -> Int -> Int -> Int -> Int -> Int -> Int
twoPointCorrelation t qx qy qz rLo rHi =
  case t of
    KDLeaf x y z _ _ ->
      let d = dist3 x y z qx qy qz
      in if d < rLo
         then 0
         else if d > rHi
              then 0
              else 1

    KDNode _ _ minX minY minZ maxX maxY maxZ _ _ l r ->
      let dMin = bboxLowerBound minX minY minZ maxX maxY maxZ qx qy qz
          dMax = bboxUpperBound minX minY minZ maxX maxY maxZ qx qy qz
          cl = twoPointCorrelation l qx qy qz rLo rHi
          cr = twoPointCorrelation r qx qy qz rLo rHi
      in if dMin > rHi
         then 0
         else if dMax < rLo
              then 0
              else cl + cr

    KDEmpty ->
      0

-- Point-cloud neighborhood pass:
-- count points within a Manhattan radius around a reference point.
pointCloudNeighborhood :: KDTree -> Int -> Int -> Int -> Int -> Int
pointCloudNeighborhood t qx qy qz radius =
  case t of
    KDLeaf x y z mass oid ->
      let _ = mass + oid
          d = dist3 x y z qx qy qz
      in if d <= radius then 1 else 0

    KDNode splitDim _ minX minY minZ maxX maxY maxZ _ _ l r ->
      let dMin = bboxLowerBound minX minY minZ maxX maxY maxZ qx qy qz
          cl = pointCloudNeighborhood l qx qy qz radius
          cr = pointCloudNeighborhood r qx qy qz radius
      in if dMin > radius
         then 0
         else if splitDim == 0
              then cl + cr
              else cr + cl

    KDEmpty ->
      0

-- Multi-phase photon-mapping-style traversal.
-- Ray origin/direction are derived from seed per phase (no hardcoded query point).
-- Structure mirrors ray_cast style:
-- local_term + kreflect * reflected_ray + krefract * refracted_ray.
photonMappingBenchmark :: KDTree -> Int -> Int -> Int -> Int -> Int
photonMappingBenchmark t phases rays seed radius =
  case t of
    KDLeaf x y z _ _ ->
      let active = if phases == 0 then 0 else if rays == 0 then 0 else 1
          ox = (seed * 13) - (phases * 7)
          oy = (seed * 5) + (rays * 3)
          oz = (seed * 11) - rays
          d = dist3 x y z ox oy oz
          mHit = if d <= radius then 1 else 0
      in active * mHit * rays

    KDNode splitDim splitVal minX minY minZ maxX maxY maxZ _ _ l r ->
      let active = if phases == 0 then 0 else if rays == 0 then 0 else 1
          ox = (seed * 13) - (phases * 7)
          oy = (seed * 5) + (rays * 3)
          oz = (seed * 11) - rays
          dx = (seed * 3) - (phases * 2)
          dy = (seed * 7) - rays
          dz = (seed * 5) - (phases + rays)
          oCoord = coordAt splitDim ox oy oz
          dCoord = coordAt splitDim dx dy dz
          planeDist = absI (oCoord - splitVal)
          boxDist = bboxLowerBound minX minY minZ maxX maxY maxZ ox oy oz
          reflected = rays / 2
          ior_i = 2 + splitDim
          ior_t = 1 + (splitVal - (splitVal / 3) * 3)
          tir = if ior_i > ior_t
                then if (planeDist * ior_i) > (radius * ior_t) then 1 else 0
                else 0
          refracted = if tir == 1 then 0 else rays / 3
          nextRays = active * (reflected + refracted)
          nextPhase = if phases > 0 then phases - 1 else 0
          nextSeed = seed + 17
          nextRadius = if radius > 3 then radius - 3 else 3
          _ = if dCoord < 0 then 0 - dCoord else dCoord
          hl = photonMappingBenchmark l nextPhase nextRays nextSeed nextRadius
          hr = photonMappingBenchmark r nextPhase nextRays nextSeed nextRadius
          side = if oCoord < splitVal then 1 else 0
          near = side * hl + ((1 - side) * hr)
          far  = side * hr + ((1 - side) * hl)
          mBox = if boxDist > radius then 0 else 1
          mPlane = if planeDist <= radius then 1 else 0
          local = mBox * rays
          kReflect = 2 + (splitDim - (splitDim / 2) * 2)      -- [2..3]
          kRefract = if tir == 1 then 0 else 1 + (ior_t / 2)  -- [1..2]
          reflectedTerm = (kReflect * near) / 3
          refractedTerm = (kRefract * mPlane * far) / 3
      in active * (local + reflectedTerm + refractedTerm)

    KDEmpty ->
      0

-- Benchmark entrypoint: build tree and iterate nearest-neighbor query.
gibbon_main =
            let _ = printsym (quote "Running program KDTree: ")
                _ = printsym (quote "NEWLINE")
                kdTree = buildKD (sizeParam + 22) 0
                _ = printsym (quote "Running pass Find nearest Neighbour (fold_like, uses=13): ")
                _ = printsym (quote "NEWLINE")
                dist = iterate (nearestDist kdTree 1 2 3)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass countInRange tight_box (fold_like, uses=13): ")
                _ = printsym (quote "NEWLINE")
                inRangeCount = iterate (countInRange kdTree (-20) 20 (-12) 12 (-7) 7)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumMassInRange (fold_like, uses=14): ")
                _ = printsym (quote "NEWLINE")
                massInRange = iterate (sumMassInRange kdTree (-25) 25 (-20) 20 (-15) 15)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass twoPointCorrelation bin_8_16 (fold_like, uses=11): ")
                _ = printsym (quote "NEWLINE")
                corrCount = iterate (twoPointCorrelation kdTree 0 0 0 8 16)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass pointCloudNeighborhood (fold_like, uses=11): ")
                _ = printsym (quote "NEWLINE")
                cloudCount = iterate (pointCloudNeighborhood kdTree 0 0 0 24)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass photonMappingBenchmark (fold_like, uses=12): ")
                _ = printsym (quote "NEWLINE")
                photonHits = iterate (photonMappingBenchmark kdTree 5 16 7 18)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
            in (dist, inRangeCount, massInRange, corrCount, cloudCount, photonHits)
