-- @BENCH adt_fields=15
data DOM
  = Elem Int   -- tag id
         Int   -- class id
         Int   -- style flags
         Int   -- layout cost
         Int   -- x
         Int   -- y
         Int   -- width
         Int   -- height
         DOM
         DOM
  | Text Int   -- char count
         Int   -- font size
         Int   -- color
         Int   -- width
         Int   -- height
  | Empty



{-# ANN type DOM "Factored" #-}

buildRenderTree :: Int -> DOM
buildRenderTree n =
   if n <= 0
   then
   let chars = 20
       font  = 14
       w     = chars * font
       h     = font + 4
   in Text chars font 0xFF0000 w h
   else
   Elem (mod n 7)          -- tag id
        (mod n 4)          -- class id
        (mod (n*3) 8)      -- style flags
        (n * 5)            -- layout cost
        0                  -- x
        (n * 10)           -- y
        0                  -- width (computed later)
        0                  -- height
        (buildRenderTree (n-1))
        (buildRenderTree (n-1))

sumArea :: DOM -> Int
sumArea d =
  case d of
    Elem _ _ _ _ _ _ w h l r ->
      (w * h) + sumArea l + sumArea r
    Text _ _ _ w h ->
      w * h
    Empty ->
      0

max :: Int -> Int -> Int
max a b = if a < b
          then b
          else a

maxBottom :: DOM -> Int
maxBottom d =
  case d of
    Elem _ _ _ _ _ y _ h l r ->
      let here = y + h
      in max here (max (maxBottom l) (maxBottom r))
    Text _ _ _ _ h ->
      h
    Empty ->
      0

countPositioned :: DOM -> Int
countPositioned d =
  case d of
    Elem _ _ style _ _ _ _ _ l r ->
      let here = if (style == 1) then 1 else 0
      in here + countPositioned l + countPositioned r
    Text _ _ _ _ _ ->
      0
    Empty ->
      0

sumTextWidth :: DOM -> Int
sumTextWidth d =
  case d of
    Text _ _ _ w _ ->
      w
    Elem _ _ _ _ _ _ _ _ l r ->
      sumTextWidth l + sumTextWidth r
    Empty ->
      0

-- Vidush This kind of function does not work
-- with the mutable backend and needs to be fixed
-- A map like function that's not tail recursive.
computeWidths :: DOM -> DOM
computeWidths d =
  case d of
    Elem tag cls style cost x y _ h l r ->
      let l' = computeWidths l
          r' = computeWidths r
          w  = max (getWidth l') (getWidth r')
      in Elem tag cls style cost x y w h l' r'
    Text c f col w h ->
      Text c f col w h
    Empty ->
      Empty

getWidth :: DOM -> Int
getWidth d =
  case d of
    Elem _ _ _ _ _ _ w _ _ _ -> w
    Text _ _ _ w _ -> w
    Empty -> 0

scaleLayout :: DOM -> Int -> DOM
scaleLayout d k =
  case d of
    Elem tag cls style cost x y w h l r ->
      Elem tag cls style cost
           (x * k) (y * k)
           (w * k) (h * k)
           (scaleLayout l k)
           (scaleLayout r k)
    Text c f col w h ->
      Text c f col (w * k) (h * k)
    Empty ->
      Empty

gibbon_main =
  let _ = printsym (quote "Running program DomTree: ")
      _ = printsym (quote "NEWLINE")
      tree   = buildRenderTree 23
      tree_smaller = buildRenderTree 20
      _ = printsym (quote "Running pass SumArea (fold, uses=6): ")
      _ = printsym (quote "NEWLINE")
      area   = iterate (sumArea tree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass find max Bottom (fold, uses=5): ")
      _ = printsym (quote "NEWLINE")
      bottom = iterate (maxBottom tree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass count styled (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      styled = iterate (countPositioned tree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass sumTextWidth (fold, uses=3): ")
      _ = printsym (quote "NEWLINE")
      textW  = iterate (sumTextWidth tree)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass computeWidths (map, uses=14): ")
      _ = printsym (quote "NEWLINE")
      tree'  = iterate (computeWidths tree_smaller)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      _ = printsym (quote "Running pass scaleLayout (map, uses=15): ")
      _ = printsym (quote "NEWLINE")
      tree'' = iterate (scaleLayout tree' 2)
      _ = printsym (quote "End")
      _ = printsym (quote "NEWLINE")
      --_      = printPacked tree''
      --_      = printsym (quote "NEWLINE")
  in (area, bottom, styled, textW)
