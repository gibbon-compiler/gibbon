-- SwapWriter: h, a recursive writer, builds Node (h b) (h a), so it reaches b
-- by traversing a first.

module SwapWriter where
data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}
mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))
sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node a b -> sumTree a + (2 * sumTree b)
h :: Tree -> Tree
h t = case t of
  Leaf x -> Leaf (x + 1)
  Node a b -> Node (h b) (h a)
gibbon_main = sumTree (h (mkTree 1 14))
