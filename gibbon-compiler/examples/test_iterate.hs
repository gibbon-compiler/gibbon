

data List = Cons Int List | Nil 

addOneList :: List -> List 
addOneList lst = case lst of 
		Nil -> Nil 
		Cons x rst -> let newVal = iterate (addOne x)  
 				  newRst = addOneList rst  
                                in Cons newVal newRst   


length :: List -> Int 
length lst = case lst of 
		Nil -> 0 
		Cons x rst -> 1 + length rst

addOne :: Int -> Int 
addOne x = x + 1


mkList :: Int -> List 
mkList len = if len <= 0 then Nil 
	     else Cons len (mkList (len-1))




gibbon_main = length (addOneList (mkList 10)) 
