-- ColorOctree: ColorOctree (Linear).
-- Functions: absI, sum8, minI, min8, mixSeed, cSumR, cSumG, cSumB, cCount,
-- buildColorOctree. ...
-- Annotated: MayVectorize on toYCoCg, markPaletteLeaves.
data ColorOctree
  = CNode Int64  -- sumR
          Int64  -- sumG
          Int64  -- sumB
          Int64  -- pixel count
          Int64  -- level
          Int64  -- bboxMinR
          Int64  -- bboxMinG
          Int64  -- bboxMinB
          Int64  -- bboxMaxR
          Int64  -- bboxMaxG
          Int64  -- bboxMaxB
          Int64  -- variance proxy
          Int64  -- energy proxy
          Int64  -- bucket flags
          ColorOctree ColorOctree ColorOctree ColorOctree
          ColorOctree ColorOctree ColorOctree ColorOctree
  | CPixel Int64 Int64 Int64
  | CEmpty

{-# ANN type ColorOctree "Linear" #-}

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

sum8 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
sum8 a b c d e f g h = a + b + c + d + e + f + g + h

minI :: Int -> Int -> Int
minI a b = if a < b then a else b

min8 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
min8 a b c d e f g h = minI (minI (minI a b) (minI c d)) (minI (minI e f) (minI g h))

mixSeed :: Int -> Int -> Int
mixSeed s salt = s * 1103 + salt * 97 + 13

cSumR :: ColorOctree -> Int64
cSumR t =
  case t of
    CNode r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> r
    CPixel r _ _ -> r
    CEmpty -> 0

cSumG :: ColorOctree -> Int64
cSumG t =
  case t of
    CNode _ g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> g
    CPixel _ g _ -> g
    CEmpty -> 0

cSumB :: ColorOctree -> Int64
cSumB t =
  case t of
    CNode _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> b
    CPixel _ _ b -> b
    CEmpty -> 0

cCount :: ColorOctree -> Int64
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

paletteEntriesQuantized :: ColorOctree -> Int64 -> Int64 -> Int64
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

quantizationErrorProxy :: ColorOctree -> Int64 -> Int64 -> Int64 -> Int64
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

-- Colours left after one pruning sweep at threshold `ep`: nodes whose
-- quantization error exceeds `ep` and that still hold pixels.
reduceColorCount :: ColorOctree -> Int64 -> Int64
reduceColorCount t ep =
  case t of
    CNode _ _ _ cnt _ _ _ _ _ _ _ varP _ _ a b c d e f g h ->
      let here = if varP > ep then (if cnt > 0 then 1 else 0) else 0
      in here + sum8 (reduceColorCount a ep) (reduceColorCount b ep)
                     (reduceColorCount c ep) (reduceColorCount d ep)
                     (reduceColorCount e ep) (reduceColorCount f ep)
                     (reduceColorCount g ep) (reduceColorCount h ep)
    CPixel _ _ _ -> 0
    CEmpty -> 0

-- Smallest squared RGB distance from (tr, tg, tb) to any colour leaf.
closestColor :: ColorOctree -> Int64 -> Int64 -> Int64 -> Int64
closestColor t tr tg tb =
  case t of
    CNode _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b c d e f g h ->
      min8 (closestColor a tr tg tb) (closestColor b tr tg tb)
           (closestColor c tr tg tb) (closestColor d tr tg tb)
           (closestColor e tr tg tb) (closestColor f tr tg tb)
           (closestColor g tr tg tb) (closestColor h tr tg tb)
    CPixel r g b ->
      let dr = r - tr
          dg = g - tg
          db = b - tb
      in dr * dr + dg * dg + db * db
    CEmpty -> 1000000

-- RGB to YCoCg scaled by 4 (Y = R+2G+B, Co = 2R-2B, Cg = 2G-R-B): colour
-- sums convert linearly, bounding boxes by interval arithmetic.
{-# ANN toYCoCg "OPT:MayVectorize" #-}
toYCoCg :: ColorOctree -> ColorOctree
toYCoCg t =
  case t of
    CNode sr sg sb cnt lvl minR minG minB maxR maxG maxB varP energy flags a b c d e f g h ->
      CNode (sr + sg + sg + sb) (sr + sr - sb - sb) (sg + sg - sr - sb) cnt lvl
            (minR + minG + minG + minB) (minR + minR - maxB - maxB) (minG + minG - maxR - maxB)
            (maxR + maxG + maxG + maxB) (maxR + maxR - minB - minB) (maxG + maxG - minR - minB)
            varP energy flags
            (toYCoCg a) (toYCoCg b) (toYCoCg c) (toYCoCg d)
            (toYCoCg e) (toYCoCg f) (toYCoCg g) (toYCoCg h)
    CPixel r g b -> CPixel (r + g + g + b) (r + r - b - b) (g + g - r - b)
    CEmpty -> CEmpty

-- Marks every node at level >= 2 holding at least `ppc` pixels as a
-- palette leaf (flag bit 8).
{-# ANN markPaletteLeaves "OPT:MayVectorize" #-}
markPaletteLeaves :: ColorOctree -> Int64 -> ColorOctree
markPaletteLeaves t ppc =
  case t of
    CNode sr sg sb cnt lvl minR minG minB maxR maxG maxB varP energy flags a b c d e f g h ->
      let flags' = if lvl >= 2
                   then (if cnt >= ppc then (if flags < 8 then flags + 8 else flags) else flags)
                   else flags
      in CNode sr sg sb cnt lvl minR minG minB maxR maxG maxB varP energy flags'
               (markPaletteLeaves a ppc) (markPaletteLeaves b ppc)
               (markPaletteLeaves c ppc) (markPaletteLeaves d ppc)
               (markPaletteLeaves e ppc) (markPaletteLeaves f ppc)
               (markPaletteLeaves g ppc) (markPaletteLeaves h ppc)
    CPixel r g b -> CPixel r g b
    CEmpty -> CEmpty

countMarked :: ColorOctree -> Int64
countMarked t =
  case t of
    CNode _ _ _ _ _ _ _ _ _ _ _ _ _ flags a b c d e f g h ->
      (if flags >= 8 then 1 else 0)
        + sum8 (countMarked a) (countMarked b) (countMarked c) (countMarked d)
               (countMarked e) (countMarked f) (countMarked g) (countMarked h)
    CPixel _ _ _ -> 0
    CEmpty -> 0

gibbon_main =
  let _ = printsym (quote "Running program ColorOctree Quantization: ")
      _ = printsym (quote "NEWLINE")
      colorTree = buildColorOctree (sizeParam + 8) 0 31

      _ = printsym (quote "Running pass paletteEntriesQuantized (fold, uses=13): ")
      _ = printsym (quote "NEWLINE")
      paletteEntries = iterate (paletteEntriesQuantized colorTree 4 12)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass quantizationErrorProxy (fold, uses=10): ")
      _ = printsym (quote "NEWLINE")
      quantError = iterate (quantizationErrorProxy colorTree 4 11 3)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass reduceColorCount (fold, uses=2): ")
      _ = printsym (quote "NEWLINE")
      colors = iterate (reduceColorCount colorTree 300)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass closestColor (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      closest = iterate (closestColor colorTree 200 60 120)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass toYCoCg (map, uses=12, shared=5): ")
      _ = printsym (quote "NEWLINE")
      yccTree = iterate (toYCoCg colorTree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass markPaletteLeaves (map, uses=3, shared=16): ")
      _ = printsym (quote "NEWLINE")
      markedTree = iterate (markPaletteLeaves colorTree 65536)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      lumaSum = cSumR yccTree
      paletteLeaves = countMarked markedTree
  in (paletteEntries, quantError, colors, closest, lumaSum, paletteLeaves)
