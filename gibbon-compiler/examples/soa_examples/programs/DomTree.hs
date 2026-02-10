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

{-# ANN type DOM "Linear" #-}

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
  let tree   = buildRenderTree 23
      area   = iterate (sumArea tree)
      bottom = iterate (maxBottom tree)
      styled = iterate (countPositioned tree)
      textW  = iterate (sumTextWidth tree)
      tree'  = iterate (computeWidths tree)
      tree'' = iterate (scaleLayout tree' 2)
      _      = printPacked tree''
      _      = printsym (quote "NEWLINE")
  in (area, bottom, styled, textW)


