module Add1 where

data Tree = Leaf Int | Node Tree Tree

add1 :: Tree -> Tree
add1 t = case t of
           Leaf x     -> Leaf (x + 1)
           Node x1 x2 -> Node (add1 x1) (add1 x2)

gibbon_main :: Tree
gibbon_main = add1 (Node (Leaf 1) (Leaf 2))

main :: IO ()
main = print gibbon_main
