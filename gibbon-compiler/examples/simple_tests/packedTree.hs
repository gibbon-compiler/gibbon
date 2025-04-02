data List = Cons Int List | Nil
data Tree = Node Int List Tree Tree | Leaf Int List


mkList :: Int -> List 
mkList len = if len <= 0 
             then Nil
             else Cons len (mkList (len - 1))

mkTree :: Int -> Tree
mkTree d = if (d <= 0)
	   then Leaf d (mkList 2)
           else Node d (mkList 2) (mkTree (d - 1)) (mkTree (d - 1))

gibbon_main = 
      let tree = mkTree 2
       in printPacked tree
