{-# LANGUAGE BangPatterns #-}

module DTreeBench where

import Gibbon.Vector

-- ===============================
-- Decision Tree Benchmark (DTree)
-- ===============================

data DTree
  = Leaf
      Int        -- class label
      Int        -- sample count
  | Node
      Int        -- feature id
      Int        -- threshold
      Int        -- impurity (e.g. Gini * 1000)
      DTree
      DTree

{-# ANN type DTree "Factored" #-}

-- -------------------------------
-- Tree generator (benchmark input)
-- -------------------------------

buildTree :: Int -> DTree
buildTree d =
  if d <= 0
  then Leaf (mod d 3) (1 + (mod d 10))
  else
    let feature   = mod d 16
        threshold = mod d 100
        impurity  = 1000 - d
    in Node feature threshold impurity (buildTree (d - 1)) (buildTree (d - 2))

-- -------------------------------
-- Structural reductions
-- -------------------------------

countNodes :: DTree -> Int
countNodes t =
  case t of
    Leaf _ _ ->
      1
    Node _ _ _ l r ->
      1 + countNodes l + countNodes r

countLeaves :: DTree -> Int
countLeaves t =
  case t of
    Leaf _ _ ->
      1
    Node _ _ _ l r ->
      countLeaves l + countLeaves r

treeDepth :: DTree -> Int
treeDepth t =
  case t of
    Leaf _ _ ->
      1
    Node _ _ _ l r ->
      let dl = treeDepth l in
      let dr = treeDepth r in
      1 + max dl dr

-- -------------------------------
-- ML-style analysis reductions
-- -------------------------------

sumImpurity :: DTree -> Int
sumImpurity t =
  case t of
    Leaf _ _ ->
      0
    Node _ _ imp l r ->
      imp + sumImpurity l + sumImpurity r

sumSamples :: DTree -> Int
sumSamples t =
  case t of
    Leaf _ samples ->
      samples
    Node _ _ _ l r ->
      sumSamples l + sumSamples r

countFeatureUses :: Int -> DTree -> Int
countFeatureUses fid t =
  case t of
    Leaf _ _ ->
      0
    Node f _ _ l r ->
      let here = if f == fid then 1 else 0 in
      here + countFeatureUses fid l
           + countFeatureUses fid r

countClass :: Int -> DTree -> Int
countClass cls t =
  case t of
    Leaf label _ ->
      if label == cls then 1 else 0
    Node _ _ _ l r ->
      countClass cls l + countClass cls r

countSmallLeaves :: Int -> DTree -> Int
countSmallLeaves thresh t =
  case t of
    Leaf _ samples ->
      if samples < thresh then 1 else 0
    Node _ _ _ l r ->
      countSmallLeaves thresh l
      + countSmallLeaves thresh r

-- -------------------------------
-- Inference-related reductions
-- -------------------------------

max :: Int -> Int -> Int
max a b = if a > b
          then a
          else b

inferenceCost :: DTree -> Int
inferenceCost t =
  case t of
    Leaf _ _ ->
      0
    Node _ _ _ l r ->
      1 + max (inferenceCost l) (inferenceCost r)

sumPathLengths :: Int -> DTree -> Int
sumPathLengths depth t =
  case t of
    Leaf _ samples ->
      depth * samples
    Node _ _ _ l r ->
      let dl = sumPathLengths (depth + 1) l in
      let dr = sumPathLengths (depth + 1) r in
      dl + dr

-- -------------------------------
-- Feature vectors (Gibbon.Vector)
-- -------------------------------

type FeatureVec = Vector Int

mkFeatureVec :: Int -> FeatureVec
mkFeatureVec n =
  generate n (\i -> mod (i * 7 + n) 100)

-- Vidush: TODO: We need to fix these classify output
-- -- -------------------------------
-- -- Classification (inference)
-- -- -------------------------------
--
-- classify :: DTree -> FeatureVec -> Int
-- classify t fv =
--   case t of
--     Leaf label _ ->
--       label
--     Node feature threshold _ left right ->
--       let val = nth fv feature in
--       if val <= threshold
--       then classify left fv
--       else classify right fv
--
-- classifyDepth :: DTree -> FeatureVec -> Int -> Int
-- classifyDepth t fv depth =
--   case t of
--     Leaf _ _ ->
--       depth
--     Node feature threshold _ left right ->
--       let val = nth fv feature in
--       if val <= threshold
--       then classifyDepth left fv (depth + 1)
--       else classifyDepth right fv (depth + 1)
--
-- -- -------------------------------
-- -- Batched inference
-- -- -------------------------------
--
-- classifyBatch :: DTree -> Int -> Int -> Int
-- classifyBatch t fvSize i =
--   if i <= 0
--   then 0
--   else
--     let fv = generate fvSize (\j -> mod (j * 3 + i) 100) in
--     let label = classify t fv in
--     label + classifyBatch t fvSize (i - 1)

-- -------------------------------
-- Benchmark entry point
-- -------------------------------

gibbon_main =
  let _ = printsym (quote "Running program Decision Tree: ") in
  let _ = printsym (quote "NEWLINE") in
  let tree = buildTree 35 in
  -- Structural analyses
  let _ = printsym (quote "Running pass countNodes: ") in
  let _ = printsym (quote "NEWLINE") in
  let nodes   = iterate (countNodes tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass countLeaves: ") in
  let _ = printsym (quote "NEWLINE") in
  let leaves  = iterate (countLeaves tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass treeDepth: ") in
  let _ = printsym (quote "NEWLINE") in
  let depth   = iterate (treeDepth tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  -- ML-style reductions
  let _ = printsym (quote "Running pass sumImpurity: ") in
  let _ = printsym (quote "NEWLINE") in
  let imp     = iterate (sumImpurity tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass sumSamples: ") in
  let _ = printsym (quote "NEWLINE") in
  let samples = iterate (sumSamples tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass countFeatureUses: ") in
  let _ = printsym (quote "NEWLINE") in
  let feat0   = iterate (countFeatureUses 0 tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass countSmallLeaves: ") in
  let _ = printsym (quote "NEWLINE") in
  let small   = iterate (countSmallLeaves 5 tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  -- Inference-related reductions
  let _ = printsym (quote "Running pass inferenceCost: ") in
  let _ = printsym (quote "NEWLINE") in
  let cost  = iterate (inferenceCost tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  let _ = printsym (quote "Running pass sumPathLengths: ") in
  let _ = printsym (quote "NEWLINE") in
  let paths = iterate (sumPathLengths 0 tree) in
  let _ = printsym (quote "End") in
  let _ = printsym (quote "NEWLINE") in
  -- Single inference
--  let fv = mkFeatureVec 32 in
--   let pred   = classify tree fv in
--   let pdepth = classifyDepth tree fv 0 in
--
--   -- Batched inference
--   let batch = classifyBatch tree 32 100 in

  (nodes, leaves, depth, imp, samples, feat0, small, cost, paths)
