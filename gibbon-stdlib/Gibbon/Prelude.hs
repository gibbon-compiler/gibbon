module Gibbon.Prelude where

-- -- haskell-src-exts can't parse this.
-- #if MIN_VERSION_GLASGOW_HASKELL(8,4,4,0)
-- import Gibbon.Prim
-- #endif

--------------------------------------------------------------------------------

maxInt :: Int -> Int -> Int
maxInt a b = if a > b then a else b

minInt :: Int -> Int -> Int
minInt a b = if a < b then a else b

maxFloat :: Float -> Float -> Float
maxFloat a b = if a .>. b then a else b

minFloat :: Float -> Float -> Float
minFloat a b = if a .<. b then a else b

float_abs :: Float -> Float
float_abs f =
    if f .<. 0.0
    then f .*. (0.0 .-. 1.0)
    else f

print_check :: Bool -> ()
print_check b =
    if b
    then let _ = printsym (quote "OK\n")
         in ()
    else let _ = printsym (quote "Err\n")
         in ()
