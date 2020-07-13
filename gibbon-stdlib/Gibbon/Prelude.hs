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
