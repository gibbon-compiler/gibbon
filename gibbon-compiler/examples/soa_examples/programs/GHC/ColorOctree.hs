{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat

-- @BENCH adt_fields=25
data ColorOctree
  = CNode Int  -- sumR
          Int  -- sumG
          Int  -- sumB
          Int  -- pixel count
          Int  -- level
          Int  -- bboxMinR
          Int  -- bboxMinG
          Int  -- bboxMinB
          Int  -- bboxMaxR
          Int  -- bboxMaxG
          Int  -- bboxMaxB
          Int  -- variance proxy
          Int  -- energy proxy
          Int  -- bucket flags
          ColorOctree ColorOctree ColorOctree ColorOctree
          ColorOctree ColorOctree ColorOctree ColorOctree
  | CPixel Int Int Int
  | CEmpty
  deriving (Generic)

{-# ANN type ColorOctree "Linear" #-}

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

sum8 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
sum8 a b c d e f g h = a + b + c + d + e + f + g + h

mixSeed :: Int -> Int -> Int
mixSeed s salt = s * 1103 + salt * 97 + 13

cSumR :: ColorOctree -> Int
cSumR t =
  case t of
    CNode r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> r
    CPixel r _ _ -> r
    CEmpty -> 0

cSumG :: ColorOctree -> Int
cSumG t =
  case t of
    CNode _ g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> g
    CPixel _ g _ -> g
    CEmpty -> 0

cSumB :: ColorOctree -> Int
cSumB t =
  case t of
    CNode _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> b
    CPixel _ _ b -> b
    CEmpty -> 0

cCount :: ColorOctree -> Int
cCount t =
  case t of
    CNode _ _ _ cnt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> cnt
    CPixel _ _ _ -> 1
    CEmpty -> 0

buildColorOctree :: Int -> Int -> Int -> ColorOctree
buildColorOctree depth level seed =
  if depth == 0
  then
    let r = mod (absI (mixSeed seed 3)) 256
        g = mod (absI (mixSeed seed 5)) 256
        b = mod (absI (mixSeed seed 7)) 256
    in CPixel r g b
  else
    let c0 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 1)
        c1 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 2)
        c2 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 3)
        c3 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 4)
        c4 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 5)
        c5 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 6)
        c6 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 7)
        c7 = buildColorOctree (depth - 1) (level + 1) (mixSeed seed 8)
        sr = sum8 (cSumR c0) (cSumR c1) (cSumR c2) (cSumR c3)
                  (cSumR c4) (cSumR c5) (cSumR c6) (cSumR c7)
        sg = sum8 (cSumG c0) (cSumG c1) (cSumG c2) (cSumG c3)
                  (cSumG c4) (cSumG c5) (cSumG c6) (cSumG c7)
        sb = sum8 (cSumB c0) (cSumB c1) (cSumB c2) (cSumB c3)
                  (cSumB c4) (cSumB c5) (cSumB c6) (cSumB c7)
        cnt = sum8 (cCount c0) (cCount c1) (cCount c2) (cCount c3)
                   (cCount c4) (cCount c5) (cCount c6) (cCount c7)
        rMean = if cnt == 0 then 0 else sr / cnt
        gMean = if cnt == 0 then 0 else sg / cnt
        bMean = if cnt == 0 then 0 else sb / cnt
        minR = if rMean > 20 then rMean - 20 else 0
        minG = if gMean > 20 then gMean - 20 else 0
        minB = if bMean > 20 then bMean - 20 else 0
        maxR = if rMean + 20 < 255 then rMean + 20 else 255
        maxG = if gMean + 20 < 255 then gMean + 20 else 255
        maxB = if bMean + 20 < 255 then bMean + 20 else 255
        spread = absI (maxR - minR) + absI (maxG - minG) + absI (maxB - minB)
        varP = spread * (1 + mod level 3)
        energy = (sr + sg + sb) / (1 + cnt)
        flags = mod (absI (mixSeed seed 29)) 8
    in CNode sr sg sb cnt level minR minG minB maxR maxG maxB varP energy flags c0 c1 c2 c3 c4 c5 c6 c7

paletteEntriesQuantized :: ColorOctree -> Int -> Int -> Int
paletteEntriesQuantized t maxDepth theta =
  case t of
    CNode _ _ _ cnt lvl minR minG minB maxR maxG maxB varP energy flags a b c d e f g h ->
      let compact = absI (maxR - minR) + absI (maxG - minG) + absI (maxB - minB) + (varP / 4)
          threshold = theta * (lvl + 1) + (flags * 2)
          approx = if lvl >= maxDepth || energy < 12 then 1 else 0
          recur = sum8
                    (paletteEntriesQuantized a maxDepth theta)
                    (paletteEntriesQuantized b maxDepth theta)
                    (paletteEntriesQuantized c maxDepth theta)
                    (paletteEntriesQuantized d maxDepth theta)
                    (paletteEntriesQuantized e maxDepth theta)
                    (paletteEntriesQuantized f maxDepth theta)
                    (paletteEntriesQuantized g maxDepth theta)
                    (paletteEntriesQuantized h maxDepth theta)
      in if compact * (1 + cnt / 16) < threshold then 1 + approx else recur
    CPixel _ _ _ -> 1
    CEmpty -> 0

quantizationErrorProxy :: ColorOctree -> Int -> Int -> Int -> Int
quantizationErrorProxy t maxDepth eta weight =
  case t of
    CNode sr sg sb cnt lvl _ _ _ _ _ _ _ _ _ a b c d e f g h ->
      let depthTerm = lvl + 1
          farLhs = cnt * 10
          farRhs = eta * depthTerm
          r = if cnt == 0 then 0 else sr / cnt
          g0 = if cnt == 0 then 0 else sg / cnt
          b0 = if cnt == 0 then 0 else sb / cnt
          approx = (absI (r - g0) + absI (g0 - b0) + absI (b0 - r)) * weight
          recur = sum8
                    (quantizationErrorProxy a maxDepth eta weight)
                    (quantizationErrorProxy b maxDepth eta weight)
                    (quantizationErrorProxy c maxDepth eta weight)
                    (quantizationErrorProxy d maxDepth eta weight)
                    (quantizationErrorProxy e maxDepth eta weight)
                    (quantizationErrorProxy f maxDepth eta weight)
                    (quantizationErrorProxy g maxDepth eta weight)
                    (quantizationErrorProxy h maxDepth eta weight)
      in if lvl >= maxDepth || farLhs < farRhs then approx else recur
    CPixel r g b -> absI (r - g) + absI (g - b) + absI (b - r)
    CEmpty -> 0


gibbon_main = do
  _ <- printsymIO (quote "Running program ColorOctree Quantization: ")
  _ <- printsymIO (quote "NEWLINE")
  let colorTree = buildColorOctree (sizeParam + 8) 0 31
  _ <- printsymIO (quote "Running pass paletteEntriesQuantized (fold, uses=13): ")
  _ <- printsymIO (quote "NEWLINE")
  paletteEntries <- iterateIO (\() -> paletteEntriesQuantized colorTree 4 12)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass quantizationErrorProxy (fold, uses=10): ")
  _ <- printsymIO (quote "NEWLINE")
  quantError <- iterateIO (\() -> quantizationErrorProxy colorTree 4 11 3)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return ((paletteEntries, quantError))

main = runGibbonMainIO gibbon_main

instance NFData ColorOctree
