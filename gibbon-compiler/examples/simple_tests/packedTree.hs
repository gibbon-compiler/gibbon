data List = Cons Int List | Nil
data FloatList = FCons Float FloatList | FNil
data Tree = Node Int FloatList List Tree Tree | Leaf


mkList :: Int -> List 
mkList len = if len <= 0 
             then Nil
             else Cons len (mkList (len - 1))

mkFloatList :: Int -> FloatList
mkFloatList len = if len <= 0
                  then FNil 
                  else FCons 1.0 (mkFloatList (len - 1))

mkTree :: Int -> Tree
mkTree d = if (d <= 0)
	   then Leaf
           else Node d (mkFloatList d) (mkList d) (mkTree (d - 1)) (mkTree (d - 1))

add1List :: List -> List
add1List lst = case lst of 
		 Nil -> Nil 
		 Cons x rst -> Cons (x+1) (add1List rst)

add1FloatList :: FloatList -> FloatList
add1FloatList lst = case lst of 
			FNil -> FNil
                        FCons y rst -> FCons (y .+. 1.0) (add1FloatList rst)

add1Tree :: Tree -> Tree
add1Tree tree = case tree of 
		     Leaf -> Leaf
                     Node x flst lst l r -> Node (x+1) (add1FloatList flst) (add1List lst) (add1Tree l) (add1Tree r)

gibbon_main = 
      let tree = mkTree 2
          tree' = add1Tree tree
       in printPacked tree'

