data DOM
  = Elem Int   -- tag id
         Int   -- class id
         Int   -- style flags
         Int   -- layout cost
         DOM
         DOM
  | Text Int   -- char count
         Int   -- font size
         Int   -- color
  | Empty

{-# ANN type DOM "Linear" #-}

buildDOMWithText :: Int -> DOM
buildDOMWithText n = if n <= 0
                     then Text 5 13 (0xFF0000)
                     else Elem (mod n 5)
                               -- style goes from 0 to 2
                               (mod n 3)
                               (mod (n*7) 16)
                               (n*10)
                               (buildDOMWithText (n-1))
                               (buildDOMWithText (n-1))

-- Rendering / layout estimation pass
-- Reads ONLY layout cost field
sumLayout :: DOM -> Int
sumLayout d =
  case d of
    Elem _ _ _ cost l r -> cost + sumLayout l + sumLayout r
    Text _ _ _ -> 0
    Empty -> 0

-- CSS matching statistics
-- Reads ONLY style flags
countStyled :: DOM -> Int -> Int
countStyled d mask =
  case d of
    Elem _ _ style _ l r ->
      let here = if (style == mask) then 1 else 0
      in here + countStyled l mask + countStyled r mask
    Text _ _ _ -> 0
    Empty -> 0

-- Text measurement pass
-- Used during layout and rendering
-- Ignores all element fields
sumTextChars :: DOM -> Int
sumTextChars d =
  case d of
    Text chars _ _ -> chars
    Elem _ _ _ _ l r -> sumTextChars l + sumTextChars r
    Empty -> 0

-- DOM analytics / instrumentation
-- Counts how often a tag appears
countTag :: DOM -> Int -> Int
countTag d wanted =
  case d of
    Elem tag _ _ _ l r -> let here = if (tag == wanted) then 1 else 0
                           in here + countTag l wanted + countTag r wanted
    Text _ _ _ -> 0
    Empty -> 0

-- Layout adjustment pass
-- Updates ONLY layout cost
scaleLayout :: DOM -> Int -> DOM
scaleLayout d k =
  case d of
    Elem tag cls style cost l r -> Elem tag cls style (cost * k) (scaleLayout l k) (scaleLayout r k)
    Text c f col -> Text c f col
    Empty -> Empty

-- Style recomputation pass
-- Resets style field only
clearStyles :: DOM -> DOM
clearStyles d =
  case d of
    Elem tag cls _ cost l r ->
      Elem tag cls 0 cost
           (clearStyles l)
           (clearStyles r)
    Text c f col ->
      Text c f col
    Empty ->
      Empty


gibbon_main =
            let dTree = buildDOMWithText 23
                suml = iterate (sumLayout dTree)
                csty = iterate (countStyled dTree 0)
                sText = iterate (sumTextChars dTree)
                cTag = iterate (countTag dTree 2)
                dTree' = iterate (scaleLayout dTree 10)
                dTree'' = iterate (clearStyles dTree')
                _ = printPacked dTree''
                _  = printsym (quote "NEWLINE")
                _  = printsym (quote "NEWLINE")
            in (suml, csty, sText, cTag)











