data List = Cons Int List | Nil 
{-# ANN type List "Factored" #-}


mkList :: Int -> List 
mkList length = if length <= 0
		then Nil 
		else
		  let rst = mkList (length - 1) 
                   in Cons length rst 



add1 :: List -> List 
add1 lst = case lst of 
		Nil -> Nil 
		Cons i rst -> let 
				i1 = i + 1
			       in Cons i1 (add1 rst)
                                          

sumList :: List -> Int 
sumList lst = case lst of 
		   Nil -> 0
		   Cons i rst -> let sumRst = sumList rst 
                                  in i + sumRst

id :: List -> List 
id lst = lst

gibbon_main = let 
		lst = mkList 10000000
                --lst' = add1 lst
                lst' = iterate (add1 lst)
	        --sum = iterate (sumList lst')
               in sumList lst'




 
