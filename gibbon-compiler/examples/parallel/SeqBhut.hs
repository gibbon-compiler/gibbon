module SeqBhut where

import Bhut

oneStep_seq :: (Float, Float, Float, Float)
            -> Vector (Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
            -> Vector (Float, Float, Float, Float, Float)
oneStep_seq box mpts ps =
    let bht = timeit (buildQtree_seq box mpts)
        _ = printsym (quote "tree built\n")
        ps2 = iterate (generate (length ps)
                       (\i ->
                            let p = nth ps i
                                mpt = nth mpts i
                                accel = calcAccel_seq mpt bht
                            in applyAccel p accel))
        -- _ = debugPrint bht ps2
    in ps2


gibbon_main =
  let pts :: Vector (Float, Float)
      pts = readArrayFile ()

      particles  = map (\(pt :: (Float, Float)) ->
                            let x = pt !!! 0
                                y = pt !!! 1
                            in (x,y,1.0,0.0,0.0))
                   pts
      mpts = map (\(pt :: (Float,Float)) ->
                      let x = pt !!! 0
                          y = pt !!! 1
                      in (x,y,1.0))
                 pts
      llx = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 0) acc) 100000.0 pts
      lly = foldl (\acc (pt :: (Float,Float)) -> minFloat (pt !!! 1) acc) 100000.0 pts
      rux = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 0) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      ruy = foldl (\acc (pt :: (Float,Float)) -> maxFloat (pt !!! 1) acc) ((0.0 .-. 1.0) .*. 100000.0) pts
      box = (llx, lly, rux, ruy)
      particles1 = (oneStep_seq box mpts particles)
      err = check particles1
  in err
  -- in 10
