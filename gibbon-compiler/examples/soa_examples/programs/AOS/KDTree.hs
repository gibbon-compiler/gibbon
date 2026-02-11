data Octree
  = OctNode Int   -- centerX
            Int   -- centerY
            Int   -- centerZ
            Int   -- halfSize
            Int   -- objectCount
            Int   -- flags
            Octree Octree Octree Octree
            Octree Octree Octree Octree
  | OctLeaf Int   -- pointX
            Int   -- pointY
            Int   -- pointZ
            Int   -- mass / weight
            Int   -- objectId
  | OctEmpty

{-# ANN type Octree "Linear" #-}

buildOct :: Int -> Octree
buildOct d =
  if d == 0
  then OctLeaf d (d+1) (d+2) (d*3) d
  else
    OctNode d d d d d (mod d 2)
      (buildOct (d-1)) (buildOct (d-1))
      (buildOct (d-1)) (buildOct (d-1))
      (buildOct (d-1)) (buildOct (d-1))
      (buildOct (d-1)) (buildOct (d-1))

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

dist3 :: Int -> Int -> Int -> Int -> Int -> Int -> Int
dist3 x1 y1 z1 x2 y2 z2 =
  absI (x1 - x2) + absI (y1 - y2) + absI (z1 - z2)

minI :: Int -> Int -> Int
minI a b = if a < b then a else b

nearestDist :: Octree -> Int -> Int -> Int -> Int
nearestDist t qx qy qz =
  case t of
    OctLeaf x y z _ _ ->
      dist3 x y z qx qy qz

    OctNode _ _ _ _ _ _ c1 c2 c3 c4 c5 c6 c7 c8 ->
      let d1 = nearestDist c1 qx qy qz
          d2 = nearestDist c2 qx qy qz
          d3 = nearestDist c3 qx qy qz
          d4 = nearestDist c4 qx qy qz
          d5 = nearestDist c5 qx qy qz
          d6 = nearestDist c6 qx qy qz
          d7 = nearestDist c7 qx qy qz
          d8 = nearestDist c8 qx qy qz
      in minI d1 (minI d2 (minI d3 (minI d4
         (minI d5 (minI d6 (minI d7 d8))))))

    OctEmpty ->
      1000000000

gibbon_main =
            let _ = printsym (quote "Running program KDTree: ")
                _ = printsym (quote "NEWLINE")
                octTree = buildOct 9
                _ = printsym (quote "Running pass Find nearest Neighbour: ")
                _ = printsym (quote "NEWLINE")
                dist = iterate (nearestDist octTree 1 2 3)
                _  = printsym (quote "End")
                _  = printsym (quote "NEWLINE")
            in (dist)



