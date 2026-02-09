data Query
  = Join Int  -- join type
         Int  -- estimated rows
         Int  -- cost
         Int  -- memory
         Query Query
  | Filter Int  -- predicate id
           Int  -- selectivity
           Int  -- cost
           Int  -- flags
           Query
  | Scan Int  -- table id
         Int  -- rows
         Int  -- cost
         Int  -- width
  | QEmpty

{-# ANN type Query "Linear" #-}

-- buildQuery :: Int -> Query
-- buildQuery d =
--   if d == 0
--   then Scan d (d*100) (d*5) (d*2)
--   else Join (mod d 3) (d*50) (d*10) (d*4)
--        (buildQuery (d-1))
--        (buildQuery (d-1))

buildQuery :: Int -> Query
buildQuery d =
  if d == 0
  then
    Scan d (d*100 + 1000) (d*5 + 10) (d*2 + 50)
  else
    if mod d 3 == 0 then
      -- Filter node (very common in real query plans)
      Filter (mod d 7)        -- predicate id
             (mod d 100)      -- selectivity %
             (d*3)            -- filter cost
             (mod d 2)
             (buildQuery (d-1))
    else
      -- Join node
      Join (mod d 2)          -- join type
           (d*50 + 500)       -- left rows
           (d*40 + 400)       -- right rows
           (d*10 + 100)       -- join cost
           (buildQuery (d-1))
           (buildQuery (d-1))

-- Reduction 1: Total cost
-- Cost-based optimization
sumCost :: Query -> Int
sumCost q =
  case q of
    Join _ _ c _ l r -> c + sumCost l + sumCost r
    Filter _ _ c _ s -> c + sumCost s
    Scan _ _ c _ -> c
    QEmpty -> 0

-- Reduction 2: Total rows
-- Cardinality estimation
sumRows :: Query -> Int
sumRows q =
  case q of
    Join _ r _ _ l s -> r + sumRows l + sumRows s
    Filter _ sel _ _ s -> sel + sumRows s
    Scan _ r _ _ -> r
    QEmpty -> 0

-- Reduction 3: Count joins
-- Heuristic optimization
countJoins :: Query -> Int
countJoins q =
  case q of
    Join _ _ _ _ l r -> 1 + countJoins l + countJoins r
    Filter _ _ _ _ s -> countJoins s
    Scan _ _ _ _ -> 0
    QEmpty -> 0

-- Reduction 4: Memory footprint
-- Execution planning
sumMemory :: Query -> Int
sumMemory q =
  case q of
    Join _ _ _ m l r -> m + sumMemory l + sumMemory r
    Filter _ _ _ m s -> m + sumMemory s
    Scan _ _ _ w -> w
    QEmpty -> 0

-- Map 1: Scale costs
-- Cost model tuning
scaleCosts :: Query -> Int -> Query
scaleCosts q k =
  case q of
    Join t r c m l s ->
      Join t r (c * k) m (scaleCosts l k) (scaleCosts s k)
    Filter p sel c f s ->
      Filter p sel (c * k) f (scaleCosts s k)
    Scan t r c w ->
      Scan t r (c * k) w
    QEmpty ->
      QEmpty

-- Map 2: Clear flags
-- After optimization phase
clearQueryFlags :: Query -> Query
clearQueryFlags q =
  case q of
    Filter p s c _ sub ->
      Filter p s c 0 (clearQueryFlags sub)
    Join t r c m l s ->
      Join t r c m (clearQueryFlags l) (clearQueryFlags s)
    Scan t r c w ->
      Scan t r c w
    QEmpty ->
      QEmpty


gibbon_main =
            let queryTree = buildQuery 33
                -- _ = printPacked queryTree
                totCost = iterate (sumCost queryTree)
                totRows = iterate (sumRows queryTree)
                totJoins = iterate (countJoins queryTree)
                totMem = iterate (sumMemory queryTree)
                queryTree' = iterate (scaleCosts queryTree 10)
                queryTree'' = iterate (clearQueryFlags queryTree')
                _  = printsym (quote "NEWLINE")
                _  = printsym (quote "NEWLINE")
            in (totCost, totRows, totJoins, totMem)







