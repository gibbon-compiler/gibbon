data Tree = Leaf Int | Node Int Tree Tree

add1 :: Tree -> Tree
add1 t = case t of
           Leaf x     -> Leaf (x + 1)
           Node val x1 x2 -> Node (val+1) (add1 x1) (add1 x2)

main :: Tree
main = add1 (Node 0 (Leaf 1) (Leaf 2))
