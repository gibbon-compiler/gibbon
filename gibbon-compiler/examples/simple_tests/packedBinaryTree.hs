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
                  else FCons (intToFloat len) (mkFloatList (len - 1))

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


intToFloat :: Int -> Float 
intToFloat val = if (val == 1) 
                 then 1.0 
                 else if (val == 2)
                 then 2.0
                 else if (val == 3)
                 then 3.0 
                 else if (val == 4)
                 then 4.0 
                 else if (val == 5)
                 then 5.0 
                 else if (val == 6)
                 then 6.0 
                 else if (val == 7)
                 then 7.0 
                 else if (val == 8)
                 then 8.0 
                 else if (val == 9)
                 then 9.0 
                 else 10.0

sumTree :: Tree -> Int 
sumTree tree = case tree of 
		    Leaf -> 0 
		    Node x l1 l2 l r -> x + (sumFloatList l1) + (sumIntList l2) + (sumTree l) + (sumTree r)


sumIntList :: List -> Int 
sumIntList lst = case lst of 
                    Nil -> 0
                    Cons x rst -> x + (sumIntList rst)

sumFloatList :: FloatList -> Int
sumFloatList lst = 10

gibbon_main = 
      let tree = mkTree 5
          tree' = add1Tree tree
       in sumTree tree'

