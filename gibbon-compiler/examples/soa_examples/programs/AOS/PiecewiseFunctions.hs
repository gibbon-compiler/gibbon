-- @BENCH adt_fields=8
data PW
  = Leaf Int    -- scaling-function coefficient
         Int    -- local scale level
         Int    -- detail/error proxy
  | Node Int    -- split dimension
         Int    -- split value
         Int    -- node level
         PW
         PW

{-# ANN type PW "Linear" #-}

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

maxI :: Int -> Int -> Int
maxI a b = if a > b then a else b

mixSeed :: Int -> Int -> Int
mixSeed s salt = s * 1103 + salt * 97 + 13

-- Build an adaptive piecewise tree with synthetic coefficients and split metadata.
buildPW :: Int -> Int -> PW
buildPW d seed =
  if d == 0
  then
    let coeff = 5 + mod (absI (mixSeed seed 3)) 29
        scale = 1 + mod (absI (mixSeed seed 5)) 12
        detail = mod (absI (mixSeed seed 7)) 40
    in Leaf coeff scale detail
  else
    let dim = mod (absI (mixSeed seed 11)) 3
        cut = mod (absI (mixSeed seed 13)) 1000
        lvl = d
        l = buildPW (d - 1) (mixSeed seed 1)
        r = buildPW (d - 1) (mixSeed seed 2)
    in Node dim cut lvl l r

-- MADNESS-inspired fold: estimate L2 norm contribution from local coefficients/details.
-- Inspiration: madness/src/madness/mra/mra.h (norm2 traversal over function tree data).
norm2Estimate :: PW -> Int
norm2Estimate p =
  case p of
    Leaf c s d -> c * c + (d * d) / (s + 1)
    Node _ _ _ l r -> norm2Estimate l + norm2Estimate r

-- MADNESS-inspired fold: count leaves violating a truncation tolerance.
-- Inspiration: madness/src/madness/mra/funcimpl.h (truncate_tol / get_thresh style thresholding).
truncateTolViolations :: PW -> Int -> Int
truncateTolViolations p tol =
  case p of
    Leaf _ _ d -> if d > tol then 1 else 0
    Node _ _ _ l r -> truncateTolViolations l tol + truncateTolViolations r tol

-- MADNESS-inspired fold: coefficient-only mass used as compress/reconstruct proxy.
-- Inspiration: madness/src/madness/mra/mra.h (compress/reconstruct on coefficient trees).
compressMass :: PW -> Int
compressMass p =
  case p of
    Leaf c _ _ -> absI c
    Node _ _ _ l r -> compressMass l + compressMass r

-- MADNESS-inspired fold: maximum active refinement level.
-- Inspiration: madness/src/madness/mra/mra.h (set_autorefine / set_refine level propagation).
autorefineMaxLevel :: PW -> Int
autorefineMaxLevel p =
  case p of
    Leaf _ s _ -> s
    Node _ _ lvl l r -> maxI lvl (maxI (autorefineMaxLevel l) (autorefineMaxLevel r))

-- MADNESS-inspired fold: process-map cut histogram from split values.
-- Inspiration: madness/src/madness/world/worlddc.h + mra/funcdefaults.h (pmap partitioning).
pmapCutHistogram :: PW -> Int -> Int
pmapCutHistogram p cut =
  case p of
    Node dim split _ l r ->
      let here = if split > cut then dim + 1 else 0
      in here + pmapCutHistogram l cut + pmapCutHistogram r cut
    Leaf _ _ _ -> 0

-- MADNESS-inspired fold: load-balance work estimate from levels/details.
-- Inspiration: madness/src/madness/mra/lbdeux.h (LBDeux weighted load estimates).
lbDeuxLoadProxy :: PW -> Int
lbDeuxLoadProxy p =
  case p of
    Leaf _ lvl detail -> (lvl + 1) * (1 + detail / 8)
    Node _ _ lvl l r -> (lvl + 1) + lbDeuxLoadProxy l + lbDeuxLoadProxy r

-- Map-like operator: add a constant potential term to all leaves.
-- Inspiration: high-level MADNESS function addition on adaptive function variables.
addConstPW :: PW -> Int -> PW
addConstPW p c =
  case p of
    Leaf coeff sc det -> Leaf (coeff + c) sc det
    Node d v lvl l r -> Node d v lvl (addConstPW l c) (addConstPW r c)

-- Map-like operator: local differentiation proxy on basis coefficients.
-- Inspiration: MADNESS operator differentiation over function trees.
diffPW :: PW -> PW
diffPW p =
  case p of
    Leaf coeff sc det -> if sc == 0 then Leaf 0 0 det else Leaf (coeff * sc) (sc - 1) det
    Node d v lvl l r -> Node d v lvl (diffPW l) (diffPW r)

gibbon_main =
            let _ = printsym (quote "Running Program Piecewise Functions (MADNESS style): ")
                _ = printsym (quote "NEWLINE")
                pfTree = buildPW (sizeParam + 23) 17

                _ = printsym (quote "Running pass norm2Estimate (fold, uses=5): ")
                _ = printsym (quote "NEWLINE")
                norm = iterate (norm2Estimate pfTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass truncateTolViolations (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                refineCnt = iterate (truncateTolViolations pfTree 18)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass compressMass (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                mass = iterate (compressMass pfTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass autorefineMaxLevel (fold, uses=4): ")
                _ = printsym (quote "NEWLINE")
                maxLvl = iterate (autorefineMaxLevel pfTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass pmapCutHistogram (fold, uses=4): ")
                _ = printsym (quote "NEWLINE")
                pmapCuts = iterate (pmapCutHistogram pfTree 500)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass lbDeuxLoadProxy (fold, uses=5): ")
                _ = printsym (quote "NEWLINE")
                loadW = iterate (lbDeuxLoadProxy pfTree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass addConstPW (map, uses=8): ")
                _ = printsym (quote "NEWLINE")
                shifted = iterate (addConstPW pfTree 10)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass diffPW (map, uses=8): ")
                _ = printsym (quote "NEWLINE")
                _diffed = iterate (diffPW shifted)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                massShift = compressMass shifted
                massDiff = compressMass _diffed
            in (norm, refineCnt, mass, maxLvl, pmapCuts, loadW, massShift, massDiff)
