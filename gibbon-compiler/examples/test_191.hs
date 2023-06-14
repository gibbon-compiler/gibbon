data Integer = I Int
data Lst = Cons Int Integer Lst | Nil 

foo :: Lst -> Lst 
foo lst = case lst of 
    Nil -> Nil 
    Cons v1 v2 rst -> if (v1 == 0)
                                 then let val = 10 
                                          rst' = foo rst
                                       in Cons val v2 rst'
                                 else let val = 12
                                          rst' = foo rst
                                       in Cons val v2 rst'

mkList :: Int -> Lst 
mkList len = if len <= 0 
             then Nil 
             else 
                 let rst = mkList (len-1)
                  in Cons len (I len) rst 
                  
gibbon_main = 
    let 
        lst  = mkList 2 
        lst' = foo lst
        _    = printPacked lst'
     in () 
