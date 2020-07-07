module Bhut where

import Gibbon.Vector

{-

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

type Box = ( Float, Float, Float, Float)

-}

data BH_Tree = BH_Empty
             | BH_Leaf Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
             | BH_Node Float   -- ^ x coord
                       Float   -- ^ y coord
                       Float   -- ^ mass
                       Int     -- ^ total points
                       Float   -- ^ Size (max_dim box)
                       BH_Tree -- ^ north-west
                       BH_Tree -- ^ north-east
                       BH_Tree -- ^ south-east
                       BH_Tree -- ^ south-west

maxFloat :: Float -> Float -> Float
maxFloat a b = if a .>. b then a else b

minFloat :: Float -> Float -> Float
minFloat a b = if a .<. b then a else b

getX :: BH_Tree -> Float
getX tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf x _ _             -> x
    BH_Node x _ _ _ _ _ _ _ _ -> x

getY :: BH_Tree -> Float
getY tr =
  case tr of
    BH_Empty                  -> 0.0
    BH_Leaf _ y _             -> y
    BH_Node _ y _ _ _ _ _ _ _ -> y

getTotalPoints :: BH_Tree -> Int
getTotalPoints tr =
  case tr of
    BH_Empty                  -> 0
    BH_Leaf _ _ _             -> 1
    BH_Node _ _ _ n _ _ _ _ _ -> n

-- | Distance between two points
dist :: (Float, Float) -> (Float, Float) -> Float
dist a b =
  let a_x = a !!! 0
      a_y = a !!! 1
      b_x = b !!! 0
      b_y = b !!! 1
      d1 = (a_x .-. b_x)
      d2 = (a_y .-. b_y)
  in (d1 .*. d1) .+. (d2 .*. d2)

applyAccel :: (Float, Float, Float, Float, Float) -> (Float, Float) -> (Float, Float, Float, Float, Float)
applyAccel particle accel =
  let vx = particle !!! 3
      vy = particle !!! 4
      ax = accel !!! 0
      ay = accel !!! 1
      -- global constant
      dt = 2.0
  in (particle !!! 0, particle !!! 1, particle !!! 2, vx .+. (ax .*. dt), vy .+. (ay .*. dt) )

isClose :: (Float, Float) -> (Float, Float) -> Float -> Bool
isClose a b size =
    let r2 = dist a b
        sizesq = size .*. size
    in r2 .<. sizesq

accel :: (Float, Float, Float) -> Float -> Float -> Float -> (Float, Float)
accel mpt1 x2 y2 m2 =
  let x1 = mpt1 !!! 0
      y1 = mpt1 !!! 1
      m1 = mpt1 !!! 2

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
calcAccel_seq :: (Float, Float, Float) -> BH_Tree -> (Float, Float)
calcAccel_seq mpt tr =
  case tr of
    BH_Empty -> (0.0, 0.0)
    BH_Leaf x y mass -> accel mpt x y mass
    BH_Node x y mass total_pts size tr1 tr2 tr3 tr4 ->
      if isClose (mpt !!! 0, mpt !!! 1) (x, y) size
      then
        let a1 = calcAccel_seq mpt tr1
            x1 = a1 !!! 0
            y1 = a1 !!! 1

            a2 = calcAccel_seq mpt tr2
            x2 = a2 !!! 0
            y2 = a2 !!! 1

            a3 = calcAccel_seq mpt tr3
            x3 = a3 !!! 0
            y3 = a3 !!! 1

            a4 = calcAccel_seq mpt tr4
            x4 = a4 !!! 0
            y4 = a4 !!! 1

        in (x1 .+. x2 .+. x3 .+. x4, y1 .+. y2 .+. y3 .+. y4)
      else accel mpt x y mass

calcCentroid :: Vector (Float, Float, Float) -> (Float, Float, Float)
calcCentroid mpts = (0.0, 0.0, 0.0)
    -- let lam1 :: (Float, Float, Float) -> (Float, Float, Float) -> (Float, Float, Float)
    --     lam1 = (\acc mpt ->
    --                  let x = mpt !!! 0
    --                      y = mpt !!! 1
    --                      m = mpt !!! 2
    --                      acc_x = acc !!! 0
    --                      acc_y = acc !!! 1
    --                      acc_m = acc !!! 2
    --                  in (acc_x + (x*m), acc_y + (y*m), acc_m + m))
    --     sum = foldl
    --             lam1
    --             (0.0, 0.0, 0.0)
    --             mpts
    --     sum_x = sum !!! 0
    --     sum_y = sum !!! 1
    --     sum_m = sum !!! 2
    -- in (sum_x ./. sum_m, sum_y ./. sum_m, sum_m)

inBox :: Float -> Float -> Float -> Float -> Float -> Float -> Bool
inBox llx lly rux ruy px py =
    (px .>. llx) && (px .<=. rux) && (py .>. lly) && (py .<=. ruy)

-- TODO
masspointsInBox :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> Vector (Float, Float, Float)
masspointsInBox box mpts =
    filter
    (\(mpt :: (Float, Float, Float)) ->
                let llx = box !!! 0
                    lly = box !!! 1
                    rux = box !!! 2
                    ruy = box !!! 3
                    x = mpt !!! 0
                    y = mpt !!! 1
                in  inBox llx lly rux ruy x y)
    mpts

maxDim :: (Float, Float, Float, Float) -> Float
maxDim box =
    let llx = box !!! 0
        lly = box !!! 1
        rux = box !!! 2
        ruy = box !!! 3
    in maxFloat (rux.-.llx) (ruy.-.lly)

buildQtree_seq :: (Float, Float, Float, Float) -> Vector (Float, Float, Float) -> BH_Tree
buildQtree_seq box mpts =
    let len = length mpts
        llx = box !!! 0
        lly = box !!! 1
        rux = box !!! 2
        ruy = box !!! 3
    in
        if len == 0
        then BH_Empty
        else if len == 1
        then
            let mpt = calcCentroid mpts
                x  = mpt !!! 0
                y  = mpt !!! 1
                m  = mpt !!! 2
            in BH_Leaf x y m
        else
            let mpt = calcCentroid mpts
                midx = (llx .+. rux) ./. 2.0
                midy = (lly .+. ruy) ./. 2.0
                b1 = (llx, lly, midx, midy)
                b2 = (llx, midy, midx, ruy)
                b3 = (midx, midy, rux, ruy)
                b4 = (midx, lly, rux, midy)
                p1 = masspointsInBox b1 mpts
                tr1 = buildQtree_seq b1 p1
                p2 = masspointsInBox b2 mpts
                tr2 = buildQtree_seq b2 p2
                p3 = masspointsInBox b3 mpts
                tr3 = buildQtree_seq b3 p3
                p4 = masspointsInBox b4 mpts
                tr4 = buildQtree_seq b4 p4
                total_points =
                    (getTotalPoints tr1) + (getTotalPoints tr2) +
                    (getTotalPoints tr3) + (getTotalPoints tr4)
                size = maxDim box
                x = mpt !!! 0
                y = mpt !!! 1
                m = mpt !!! 2
            in BH_Node x y m total_points size tr1 tr2 tr3 tr4


oneStep_seq :: (Float, Float, Float, Float)
            -> Vector (Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
oneStep_seq box mpts ps =
    let bht = buildQtree_seq box mpts
        -- ps2 = generate (length ps) (\i -> nth ps i)
        ps2 = generate (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel)
    in ps2

gibbon_main =
  let -- pts :: Vector (Float, Float)
      -- pts = readArrayFile ()

      pts :: Vector (Float, Float)
      pts = generate 10 (\i -> (1.0 .*. (intToFloat i), 1.0 .*. (intToFloat i)))

      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0)) pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      particles1 = (oneStep_seq box mpts particles)
  in 10
