{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat
import Gibbon.Vector


-- ===============================
-- Decision Tree Benchmark (DTree)
-- ===============================

-- @BENCH adt_fields=7
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
  deriving (Generic)

{-# ANN type DTree "Linear" #-}

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
      1 + maxI dl dr

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

maxI :: Int -> Int -> Int
maxI a b = if a > b
           then a
           else b

inferenceCost :: DTree -> Int
inferenceCost t =
  case t of
    Leaf _ _ ->
      0
    Node _ _ _ l r ->
      1 + maxI (inferenceCost l) (inferenceCost r)

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
  generate n (\i -> mod (i * 7 + n + sizeParam) 100)

-- Vidush: TODO: We need to fix these classify output
-- -------------------------------
-- Classification (inference)
-- -------------------------------

classify :: DTree -> FeatureVec -> Int
classify t fv =
  case t of
    Leaf label _ ->
      label
    Node feature threshold _ left right ->
      let val = nth fv feature in
      if val <= threshold
      then classify left fv
      else classify right fv

classifyDepth :: DTree -> FeatureVec -> Int -> Int
classifyDepth t fv depth =
  case t of
    Leaf _ _ ->
      depth
    Node feature threshold _ left right ->
      let val = nth fv feature in
      if val <= threshold
      then classifyDepth left fv (depth + 1)
      else classifyDepth right fv (depth + 1)

-- -------------------------------
-- Batched inference
-- -------------------------------

classifyBatch :: DTree -> Int -> Int -> Int
classifyBatch t fvSize i =
  if i <= 0
  then 0
  else
    let fv = generate fvSize (\j -> mod (j * 3 + i + sizeParam) 100) in
    let label = classify t fv in
    label + classifyBatch t fvSize (i - 1)

-- -------------------------------
-- Benchmark entry point
-- -------------------------------


gibbon_main = do
  _ <- printsymIO (quote "Running program Decision Tree: ")
  _ <- printsymIO (quote "NEWLINE")
  let tree = buildTree (sizeParam + 35)
  _ <- printsymIO (quote "Running pass countNodes (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  nodes <- iterateIO (\() -> countNodes tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass countLeaves (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  leaves <- iterateIO (\() -> countLeaves tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass treeDepth (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  depth <- iterateIO (\() -> treeDepth tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumImpurity (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  imp <- iterateIO (\() -> sumImpurity tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumSamples (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  samples <- iterateIO (\() -> sumSamples tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass countFeatureUses (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  feat0 <- iterateIO (\() -> countFeatureUses 0 tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass countSmallLeaves (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  small <- iterateIO (\() -> countSmallLeaves 5 tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass inferenceCost (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  cost <- iterateIO (\() -> inferenceCost tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumPathLengths (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  paths <- iterateIO (\() -> sumPathLengths 0 tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  let fv = mkFeatureVec 32
  _ <- printsymIO (quote "Running pass classify tree (fold, uses=5): ")
  _ <- printsymIO (quote "NEWLINE")
  pred <- iterateIO (\() -> classify tree fv)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass classify Depth (fold, uses=4): ")
  _ <- printsymIO (quote "NEWLINE")
  pdepth <- iterateIO (\() -> classifyDepth tree fv 0)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass classify Batch (fold, uses=5): ")
  _ <- printsymIO (quote "NEWLINE")
  batch <- iterateIO (\() -> classifyBatch tree 32 100)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (nodes, leaves, depth, imp, samples, feat0, small, cost, paths, pred, pdepth, batch)

main = runGibbonMainIO gibbon_main

instance NFData DTree
