data List = Cons Int List | Nil
data Tree = Node List Tree Tree | Leaf


mkList :: Int -> List 
mkList len = if len <= 0 
             then Nil
             else Cons len (mkList (len - 1))

mkTree :: Int -> Tree
mkTree d = if (d <= 0)
	   then Leaf
           else Node (mkList 2) (mkTree (d - 1)) (mkTree (d - 1))

add1List :: List -> List
add1List lst = case lst of 
		 Nil -> Nil 
		 Cons x rst -> Cons (x+1) (add1List rst)

add1Tree :: Tree -> Tree
add1Tree tree = case tree of 
		     Leaf -> Leaf
                     Node lst l r -> Node (add1List lst) (add1Tree l) (add1Tree r)

gibbon_main = 
      let tree = mkTree 2
          tree' = add1Tree tree
       in printPacked tree'

