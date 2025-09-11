
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


--fieldDep :: List -> (Int, List) 
--fieldDep lst = case lst of 
--		     Nil -> (0, Nil) 
--                     Cons i rst -> let (rv, rst') = fieldDep rst 
--				     in (rv + i, Cons (rv + i) rst')
                                          

sumList :: List -> Int 
sumList lst = case lst of 
		   Nil -> 0
		   Cons i rst -> let sumRst = sumList rst 
                                  in i + sumRst

gibbon_main = let 
<<<<<<< HEAD:gibbon-compiler/examples/soa_examples/list.hs
		lst = mkList 100
                lst' = add1 lst 
	       in sumList lst'
=======
		lst = mkList 20000
                --lst' = iterate (add1 lst)
                _ = printPacked lst
                _ = printsym (quote "NEWLINE")
                --(val, lst'') = fieldDep lst' 
	       in sumList lst --() --printPacked lst' --val --sumList lst'
>>>>>>> f352266b (Hoist BoundsChecking):gibbon-compiler/examples/simple_tests/list.hs




 
