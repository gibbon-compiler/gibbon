-- MultiBuf: T (Factored), a tag buffer plus Int8 and Int64 buffers.  idT shares
-- the whole value; passT shares each right child.

module MultiBuf where

data T = L | N Int8 Int64 T T
{-# ANN type T "Factored" #-}

mkT :: Int -> Int -> T
mkT k n = if n <= 0 then L
          else N (toInt8 (mod k 100)) (toInt64 (k * 1000)) (mkT (k * 2) (n - 1)) (mkT ((k * 2) + 1) (n - 1))

idT :: T -> T
idT t = t

passT :: T -> T
passT t = case t of
  L -> L
  N a b l r -> N a b (passT l) r

sumT :: T -> Int
sumT t = case t of
  L -> 0
  N a b l r -> toInt64 a + b + sumT l + (3 * sumT r)

gibbon_main = (sumT (idT (mkT 1 5)), sumT (passT (passT (mkT 1 9))))
