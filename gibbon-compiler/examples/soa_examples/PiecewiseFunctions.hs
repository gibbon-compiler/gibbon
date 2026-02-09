data PW
  = Leaf Int    -- coefficient
         Int    -- degree
         Int    -- error estimate
  | Node Int    -- split dimension
         Int    -- split value
         Int    -- bounding box info
         PW
         PW

{-# ANN type PW "Linear" #-}


-- Builds a balanced kd-tree of given depth
buildPW :: Int -> PW
buildPW d =
  if (d == 0)
  then
    Leaf (d + 1)      -- coefficient
         (d + 2)      -- degree
         (d + 3)      -- error estimate
  else
    let splitDim = d - (d / 3) * 3   -- pseudo cycling dim
        splitVal = d * 10
        bbox     = d * 100
        l        = buildPW (d - 1)
        r        = buildPW (d - 1)
    in Node splitDim splitVal bbox l r

-- Computes integral-like metric
-- Reads ONLY coefficient
sumCoeffs :: PW -> Int
sumCoeffs p =
  case p of
    Leaf coeff _ _ ->
      coeff
    Node _ _ _ l r ->
      sumCoeffs l + sumCoeffs r

-- Used in adaptive refinement decisions
-- Reads ONLY degree field
maxDegree :: PW -> Int
maxDegree p =
  case p of
    Leaf _ deg _ ->
      deg
    Node _ _ _ l r ->
      let dl = maxDegree l
          dr = maxDegree r
      in if (dl > dr) then dl else dr

-- Error accumulation pass
-- Reads ONLY error field
sumError :: PW -> Int
sumError p =
  case p of
    Leaf _ _ err ->
      err
    Node _ _ _ l r ->
      sumError l + sumError r

-- Tree structure statistics
-- Reads ONLY split dimension
countSplit :: PW -> Int -> Int
countSplit p dim =
  case p of
    Node d _ _ l r ->
      let here = if (d == dim) then 1 else 0
      in here + countSplit l dim + countSplit r dim
    Leaf _ _ _ ->
      0

-- Squares the polynomial coefficient
-- Models f(x) -> f(x)^2
-- Updates ONLY coefficient
squarePW :: PW -> PW
squarePW p =
  case p of
    Leaf coeff deg err ->
      Leaf (coeff * coeff) deg err
    Node d v b l r ->
      Node d v b
           (squarePW l)
           (squarePW r)

-- Models f(x) -> f(x) + c
-- Updates ONLY coefficient
addConstPW :: PW -> Int -> PW
addConstPW p c =
  case p of
    Leaf coeff deg err ->
      Leaf (coeff + c) deg err
    Node d v b l r ->
      Node d v b
           (addConstPW l c)
           (addConstPW r c)

-- Symbolic differentiation
-- Updates coefficient and degree
diffPW :: PW -> PW
diffPW p =
  case p of
    Leaf coeff deg err ->
      if (deg == 0)
      then Leaf 0 0 err
      else Leaf (coeff * deg) (deg - 1) err
    Node d v b l r ->
      Node d v b
           (diffPW l)
           (diffPW r)

gibbon_main =
            let pfTree = buildPW 20
                -- _ = printPacked pfTree
                totCoeffs = iterate (sumCoeffs pfTree)
                deg = iterate (maxDegree pfTree)
                err = iterate (sumError pfTree)
                spltCount = iterate (countSplit pfTree 2)
                squarePfTree = iterate (squarePW pfTree)
                addConstPfTree = iterate (addConstPW pfTree 100)
                _  = printsym (quote "NEWLINE")
                _  = printsym (quote "NEWLINE")
            in (totCoeffs, deg, err, spltCount)



