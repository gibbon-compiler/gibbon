{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude   #-}

module Bhut where

import Gibbon.Prelude
import Gibbon.Vector
import Gibbon.Vector.Parallel

import Geometry

-----------------------------------------------------------------------------------------

type Point2d = ( Float -- ^ x coord
               , Float -- ^ y coord
               )

type MassPoint = ( Float -- ^ x coord
                 , Float -- ^ y coord
                 , Float -- ^ mass
                 )

type Particle  = ( Float -- ^ x coord
                 , Float -- ^ y coord
                 , Float -- ^ mass
                 , Float -- ^ velocity x
                 , Float -- ^ velocity y
                 )

type Box = (Float, Float, Float, Float)

print_masspoint :: MassPoint -> ()
print_masspoint tup =
    let (a,b,c) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ")")
    in ()

print_box :: Box -> ()
print_box tup =
    let (a,b,c,d) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ",")
        _ = printfloat d
        _ = printsym (quote ")")
    in ()

print_particle :: Particle -> ()
print_particle tup =
    let (a,b,c,d,e) = tup
        _ = printsym (quote "(")
        _ = printfloat a
        _ = printsym (quote ",")
        _ = printfloat b
        _ = printsym (quote ",")
        _ = printfloat c
        _ = printsym (quote ",")
        _ = printfloat d
        _ = printsym (quote ",")
        _ = printfloat e
        _ = printsym (quote ")")
    in ()

--------------------------------------------------------------------------------

data BH_Tree = BH_Empty
             | BH_Leaf Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
             | BH_Node Float   -- ^ x coord (centroid)
                       Float   -- ^ y coord (centroid)
                       Float   -- ^ mass    (centroid)
                       Int     -- ^ total points
                       Float   -- ^ width (max_dim box)
                       BH_Tree -- ^ north-west
                       BH_Tree -- ^ north-east
                       BH_Tree -- ^ south-east
                       BH_Tree -- ^ south-west

sumQtree :: BH_Tree -> Float
sumQtree tr =
    case tr of
        BH_Empty -> 0.0
        BH_Leaf x y m -> x .+. y .+. m
        BH_Node x y m _ _ tr1 tr2 tr3 tr4 ->
            (sumQtree tr1) .+. (sumQtree tr2) .+. (sumQtree tr3) .+. (sumQtree tr4)

countLeavesQtree :: BH_Tree -> Int
countLeavesQtree tr =
    case tr of
        BH_Empty -> 0
        BH_Leaf x y m -> 1
        BH_Node x y m _ _ tr1 tr2 tr3 tr4 ->
            (countLeavesQtree tr1) + (countLeavesQtree tr2) + (countLeavesQtree tr3) + (countLeavesQtree tr4)

sum_mass_points :: Vector MassPoint -> Float
sum_mass_points mpts =
  foldl (\acc (pt :: MassPoint) ->
            let (x,y,z) = pt
            in acc .+. x .+. y .+. z)
    0.0
    mpts

myprintBHTree :: BH_Tree -> ()
myprintBHTree bht =
    case bht of
        BH_Empty ->
            let _ = printsym (quote "(BH_Empty)")
            in ()
        BH_Leaf x y m ->
            let _ = printsym (quote "(BH_Leaf")
                _ = print_masspoint (x,y,m)
                _ = printsym (quote ") ")
            in ()
        BH_Node x y m total width tr1 tr2 tr3 tr4->
            let _ = printsym (quote "(BH_Node")
                _ = print_masspoint (x,y,m)
                _ = printint total
                _ = printsym (quote " ")
                _ = printfloat width
                _ = printsym (quote " ")
                _ = myprintBHTree tr1
                _ = myprintBHTree tr2
                _ = myprintBHTree tr3
                _ = myprintBHTree tr4
                _ = printsym (quote ") ")
            in ()

getx_qtree :: BH_Tree -> Float
getx_qtree tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf x _ _             -> x
    BH_Node x _ _ _ _ _ _ _ _ -> x

gety_qtree :: BH_Tree -> Float
gety_qtree tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf _ y _             -> y
    BH_Node _ y _ _ _ _ _ _ _ -> y

getTotalPoints_qtree :: BH_Tree -> Int
getTotalPoints_qtree tr =
  case tr of
    BH_Empty                  -> 0
    BH_Leaf _ _ _             -> 1
    BH_Node _ _ _ n _ _ _ _ _ -> n


--------------------------------------------------------------------------------

applyAccel :: Particle -> Point2d -> Particle
{-# INLINE applyAccel #-}
applyAccel particle accel =
  let (x,y,m,vx,vy) = particle
      (ax,ay) = accel
      -- global constant
      dt = 2.0
  in (x, y, m, vx .+. (ax .*. dt), vy .+. (ay .*. dt))

isClose :: Point2d -> Point2d -> Float -> Bool
{-# INLINE isClose #-}
isClose a b width =
    let r2 = dist_point2d a b
        widthsq = width .*. width
    in r2 .<. widthsq

accel :: MassPoint -> Float -> Float -> Float -> Point2d
{-# INLINE accel #-}
accel mpt1 x2 y2 m2 =
  let (x1,y1,m1) = mpt1
  in if (x1 .==. x2) && (y1 .==. y2) && (m1 .==. m2)
     then (0.0, 0.0)
     else
       let dx = x1 .-. x2
           dy = y1 .-. y2
           rsqr = (dx .*. dx) .+. (dy .*. dy)
           r = sqrt rsqr
           s = (m1 .*. m2 ./. (rsqr .*. r))
       in (dx .*. s, dy .*. s)

-- the acceleration of a mass point after applying the force applied by surrounding
-- mass points
calcAccel_seq :: MassPoint -> BH_Tree -> Point2d
calcAccel_seq mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts width tr1 tr2 tr3 tr4 ->
      let (a,b,_) = mpt in
      if isClose (a, b) (x, y) width
      then
        let (x1,y1) = calcAccel_seq mpt tr1
            (x2,y2) = calcAccel_seq mpt tr2
            (x3,y3) = calcAccel_seq mpt tr3
            (x4,y4) = calcAccel_seq mpt tr4
        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

{-

calcAccel_par :: Int -> MassPoint -> BH_Tree -> Point2d
calcAccel_par cutoff mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts width tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y) width
      then
        if total_pts < cutoff then calcAccel_seq mpt tr else
        let (x1,y1) = spawn (calcAccel_par cutoff mpt tr1)
            (x2,y2) = spawn (calcAccel_par cutoff mpt tr2)
            (x3,y3) = spawn (calcAccel_par cutoff mpt tr3)
            (x4,y4) = calcAccel_par cutoff mpt tr4
            _  = sync
        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

-}

calcCentroid_seq :: Vector MassPoint -> MassPoint
calcCentroid_seq mpts =
    let lam1 = (\(acc :: MassPoint) (mpt :: MassPoint) ->
                     let (x,y,m) = mpt
                         (acc_x, acc_y, acc_m) = acc
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        sum = foldl
                lam1
                (0.0, 0.0, 0.0)
                mpts
        (sum_x, sum_y, sum_m) = sum
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

{-

calcCentroid_par :: Vector MassPoint -> MassPoint
calcCentroid_par mpts =
    let lam1 = (\(acc :: MassPoint) (mpt :: MassPoint) ->
                     let (x,y,m) = mpt
                         (acc_x, acc_y, acc_m) = acc
                     in (acc_x .+. (x.*.m), acc_y .+. (y.*.m), acc_m .+. m))
        lam2  = (\(acc1 :: MassPoint) (acc2 :: MassPoint) ->
                     let (x1,y1,z1) = acc1
                         (x2,y2,z2) = acc2
                     in (x1 .+. x2, y1 .+. y2, z1 .+. z2))
        sum = foldl2_par
                lam1
                (0.0, 0.0, 0.0)
                lam2
                mpts
        (sum_x, sum_y, sum_m) = sum
    in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

-}

inBox :: Box -> Point2d -> Bool
{-# INLINE inBox #-}
inBox box point =
  let (llx,lly,rux,ruy) = box
      (px, py) = point
  in (px .>=. llx) && (px .<=. rux) && (py .>=. lly) && (py .<=. ruy)

-- Parallelize...
masspointsInBox_seq :: Box -> Vector MassPoint -> Vector MassPoint
masspointsInBox_seq box mpts =
    filter
      (\(mpt :: MassPoint) ->
                  let (x,y,_) = mpt
                  in  inBox box (x,y))
      mpts

maxDim :: Box -> Float
{-# INLINE maxDim #-}
maxDim box =
    let (llx,lly,rux,ruy) = box
    in maxFloat (rux.-.llx) (ruy.-.lly)

buildQtree_seq :: Box -> Vector MassPoint -> BH_Tree
buildQtree_seq box mpts =
    let len = length mpts
        (llx,lly,rux,ruy) = box
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let (x,y,m) = calcCentroid_seq mpts
            in BH_Leaf x y m
        else
            let mpt = calcCentroid_seq mpts
                midx = (llx .+. rux) ./. 2.0
                midy = (lly .+. ruy) ./. 2.0
                b1 = (llx, lly, midx, midy)
                b2 = (llx, midy, midx, ruy)
                b3 = (midx, midy, rux, ruy)
                b4 = (midx, lly, rux, midy)
                p1 = masspointsInBox_seq b1 mpts
                tr1 = buildQtree_seq b1 p1
                p2 = masspointsInBox_seq b2 mpts
                tr2 = buildQtree_seq b2 p2
                p3 = masspointsInBox_seq b3 mpts
                tr3 = buildQtree_seq b3 p3
                p4 = masspointsInBox_seq b4 mpts
                tr4 = buildQtree_seq b4 p4
                total_points =
                    (getTotalPoints_qtree tr1) + (getTotalPoints_qtree tr2) +
                    (getTotalPoints_qtree tr3) + (getTotalPoints_qtree tr4)
                width = maxDim box
                (x,y,m) = mpt
            in BH_Node x y m total_points width tr1 tr2 tr3 tr4

buildQtree_par :: Int -> Box -> Vector MassPoint -> BH_Tree
buildQtree_par cutoff box mpts =
    let len = length mpts in
        -- _ = printsym (quote "cutoff=")
        -- _ = printint cutoff
        -- _ = printsym (quote "\n") in
    if len < cutoff then buildQtree_seq box mpts else
    let (llx,lly,rux,ruy) = box
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let (x,y,m) = calcCentroid_seq mpts
            in BH_Leaf x y m
        else
            let (x,y,m) = calcCentroid_seq mpts
                midx = (llx .+. rux) ./. 2.0
                midy = (lly .+. ruy) ./. 2.0
                b1 = (llx, lly, midx, midy)
                b2 = (llx, midy, midx, ruy)
                b3 = (midx, midy, rux, ruy)
                b4 = (midx, lly, rux, midy)
                p1 = masspointsInBox_seq b1 mpts
                tr1 = spawn (buildQtree_par cutoff b1 p1)
                p2 = masspointsInBox_seq b2 mpts
                tr2 = spawn (buildQtree_par cutoff b2 p2)
                p3 = masspointsInBox_seq b3 mpts
                tr3 = spawn (buildQtree_par cutoff b3 p3)
                p4 = masspointsInBox_seq b4 mpts
                tr4 = buildQtree_par cutoff b4 p4
                _ = sync
                total_points =
                    (getTotalPoints_qtree tr1) + (getTotalPoints_qtree tr2) +
                    (getTotalPoints_qtree tr3) + (getTotalPoints_qtree tr4)
                width = maxDim box
            in BH_Node x y m total_points width tr1 tr2 tr3 tr4


--------------------------------------------------------------------------------

debugPrint :: BH_Tree -> Vector Particle -> ()
debugPrint bht ps2 =
    let _ = myprintBHTree bht
        _ = printsym (quote "\n")
        _ = printVec (\p -> let _ = print_particle p
                                _ = printsym (quote "\n")
                            in ()) ps2
        _ = printsym (quote "\n")
    in ()


oneStep_seq :: BH_Tree
            -> Vector MassPoint
            -> Vector Particle
            -> Vector Particle
oneStep_seq bht mpts ps =
    let ps2 = iterate (generate (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel))
    in ps2

oneStep_par :: Int
            -> BH_Tree
            -> Vector MassPoint
            -> Vector Particle
            -> Vector Particle
oneStep_par cutoff bht mpts ps =
    let ps2 = iterate (generate_par2 4096 (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                -- accel = calcAccel_par cutoff mpt bht
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel))
    in ps2

--------------------------------------------------------------------------------

check_buildquadtree :: Vector MassPoint -> BH_Tree -> ()
check_buildquadtree mpts bht =
    let expected = sum_mass_points mpts
        actual = sumQtree bht
        count1 = countLeavesQtree bht
        count2 = getTotalPoints_qtree bht
        _ = printsym (quote "Sum: expected= ")
        _ = printfloat expected
        _ = printsym (quote ", ")
        _ = printsym (quote "actual= ")
        _ = printfloat actual
        _ = printsym (quote "\n")
        _ = printsym (quote "Counts: ")
        _ = printint count1
        _ = printsym (quote ", ")
        _ = printint count2
        _ = printsym (quote "\n")
    in print_check (float_abs (expected .-. actual) .<. 0.01)

accel_for :: Particle -> Vector Particle -> Point2d
accel_for query input =
    foldl (\(acc :: Point2d) (pt :: Particle) ->
                  let (aax, aay) = acc
                      (x,y,m,_,_) = pt
                      (x1,x2,m2,_,_) = query
                      query_mp = (x1,x2,m2)
                      (ax,ay) = accel query_mp x y m
                  in (aax .+. ax, aay .+. ay))
    (0.0, 0.0)
    input

check_bhut :: Vector Particle -> Vector Particle -> ()
check_bhut input particles =
    let
        n = length input
        checkpoints0 :: Vector Int
        checkpoints0 = valloc 4
        checkpoints1 = inplaceUpdate 0 0 checkpoints0
        checkpoints2 = inplaceUpdate 1 (div n 4) checkpoints1
        checkpoints3 = inplaceUpdate 2 (div n 2) checkpoints2
        checkpoints4 = inplaceUpdate 3 (n-1) checkpoints2
        delta = foldl (\err idx ->
                          let query = nth input idx
                              axay = accel_for query input
                              (_,_,_,expected_ax, expected_ay) = applyAccel query axay
                              (_,_,_,actual_ax,actual_ay) = nth particles idx
                              -- _ = printsym (quote "Expected: ")
                              -- _ = printfloat expected_ax
                              -- _ = printsym (quote ",")
                              -- _ = printfloat expected_ay
                              -- _ = printsym (quote "\n")
                              -- _ = printsym (quote "Actual: ")
                              -- _ = printfloat actual_ax
                              -- _ = printsym (quote ",")
                              -- _ = printfloat actual_ay
                              -- _ = printsym (quote "\n")
                          in float_abs (expected_ax .-. actual_ax) .+. float_abs (expected_ay .-. actual_ay))
                  0.0 checkpoints4

    in print_check (delta .<. 0.01)
