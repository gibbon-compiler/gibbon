data PList a = Nil | Cons a (PList a) deriving Show
data BinTree a b = Cell a | Node b (BinTree a b) (BinTree a b) deriving Show

f :: BinTree b c -> BinTree (b, b) (c, c)
f bt = case bt of 
  Cell x -> Cell (x, x)
  Node x lt rt -> Node (x, x) (f lt) (f rt)

-- >>> gibbon_main
-- Node (((10,10),(10,10)),((10,10),(10,10))) (Cell (((5,5),(5,5)),((5,5),(5,5)))) (Cell (((2,2),(2,2)),((2,2),(2,2))))
gibbon_main = 
  let bt = Node 10 (Cell 5) (Cell 2) -- :: BinTree Int Int
  in  f (f (f bt))
