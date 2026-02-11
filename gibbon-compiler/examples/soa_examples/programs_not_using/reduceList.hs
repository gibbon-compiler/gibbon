data ListA = ConsA Int ListA | NilA
data ListB = ConsB Int Int Int Int Int Int ListB | NilB 
data List = Cons Int Int Int Int ListA (List) | Nil 
{-# ANN type ListA "Linear" #-}
{-# ANN type ListB "Linear" #-}
{-# ANN type List "Factored" #-}


mkListA :: Int -> ListA 
mkListA len = if len <= 0 
              then NilA
              else 
                let rst = mkListA (len - 1) 
                 in ConsA len rst 

mkListB :: Int -> ListB
mkListB len = if len <= 0 
              then NilB
              else 
		let rst = mkListB (len - 1)
                 in ConsB len len len len len len rst

mkList :: Int -> List 
mkList len = if len <= 0
             then Nil 
             else 
               let lsta = mkListA 1000
                   rst = mkList (len - 1) 
                 in Cons len len len len lsta rst

reduce :: List -> Int 
reduce lst = case lst of 
                  Nil -> 0 
                  Cons a b c d lsta rst -> a + reduce rst 


reduceB :: ListB -> Int
reduceB lst = case lst of 
		    NilB -> 0
		    ConsB a b c d e f rst -> let val = reduceB rst
                                               in a + val


gibbon_main = 
        let lst = mkListB 1000000 
            i = iterate (reduceB lst) 
         in i

