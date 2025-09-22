data Tree = Node Int Tree Tree | Leaf Int

foo :: Int -> Tree
foo i = let tree = Node i (Leaf i) (Leaf (i+1))
         in tree

make_node :: Tree -> Tree -> Tree
make_node t1 t2 = Node 10 t1 t2

foo' :: Tree -> Tree
foo' tree = case tree of 
                 Leaf v -> tree
                 Node i x y -> tree

gibbon_main = 
      let t1 = foo 20
          t2 = foo 50
          t3 = make_node t1 t2
          t4 = foo' t3
          t5 = Node 12 t4 (Node 12 (Leaf 1) (Leaf 2))
        in printPacked t5

 
