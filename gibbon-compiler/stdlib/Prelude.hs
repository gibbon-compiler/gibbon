module Gibbon.Prelude where

--------------------------------------------------------------------------------

maxInt :: Int -> Int -> Int
maxInt a b = if a > b then a else b

minInt :: Int -> Int -> Int
minInt a b = if a < b then a else b

maxFloat :: Float -> Float -> Float
maxFloat a b = if a .>. b then a else b

minFloat :: Float -> Float -> Float
minFloat a b = if a .<. b then a else b
