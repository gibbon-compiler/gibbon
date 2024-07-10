module Map where 


data ConsIntList = Cons Int (ConsIntList) | Nil


mkConsIntList :: Int -> ConsIntList
mkConsIntList len = if len <= 0 
                    then Nil 
                    else let 
                           rst = mkConsIntList (len-1)
                          in Cons len rst


map :: (Int -> Int) -> ConsIntList -> ConsIntList
map f lst = case lst of 
                    Nil -> Nil 
                    Cons x rst -> Cons (f x) (map f rst)
                    
add1 :: Int -> Int 
add1 x = x + 1

checkMapAdd1 :: ConsIntList -> ConsIntList -> Bool 
checkMapAdd1 lst lst' = case lst of 
                            Nil -> case lst' of
                                         Nil -> True 
                                         _ -> False 
                            Cons x rst -> case lst' of 
                                             Nil -> False
                                             Cons x' rst' -> if (x' == x + 1)
                                                             then True && checkMapAdd1 rst rst'
                                                             else False 

gibbon_main = 
    let len = 10000000
        lst = mkConsIntList len 
        lst' = iterate (map add1 lst)
     in checkMapAdd1 lst lst'


