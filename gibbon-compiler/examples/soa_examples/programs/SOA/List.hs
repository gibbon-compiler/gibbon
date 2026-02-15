-- @BENCH adt_fields=2
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

sumListAcc :: List -> Int -> Int
sumListAcc lst acc = case lst of
						  Nil -> acc
						  Cons i rst -> sumListAcc rst (acc + i)

id :: List -> List 
id lst = lst

gibbon_main = let
				  _ = printsym (quote "Running program List: ")
				  _ = printsym (quote "NEWLINE")
				  lst = mkList 100000000
				  _ = printsym (quote "Running pass add1 List (map, uses=2): ")
				  _ = printsym (quote "NEWLINE")
				  lst' = iterate (add1 lst)
				  _ = printsym (quote "End")
				  _ = printsym (quote "NEWLINE")
				  _ = printsym (quote "Running pass sumList (fold, uses=2): ")
				  _ = printsym (quote "NEWLINE")
				  sum = iterate (sumList lst')
				  _ = printsym (quote "End")
				  _ = printsym (quote "NEWLINE")
				  _ = printsym (quote "Running pass sumListAcc (fold, uses=2): ")
				  _ = printsym (quote "NEWLINE")
				  sum' = iterate (sumListAcc lst' 0)
				  _ = printsym (quote "End")
				  _ = printsym (quote "NEWLINE")
				in (sum, sum')




 
