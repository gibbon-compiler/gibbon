data Foo = A Int Int | B Int | C

-- TODO : process without top level signature

fun1 x = case x of 
    A a b -> a + b 
    _ -> 36 

fun2 x = case x of 
    B e -> e * 4
    _ -> 98

eq :: Foo -> Foo -> Bool
eq x y = case x of 
    A a b -> case y of 
        A c d -> a == c && b == d 
        _     -> False 
    B b -> case y of 
        B c -> b == c 
        _ -> False 
    C -> case y of 
        C -> True 
        _ -> False

not x = if x then False else True

main = print gibbon_main

gibbon_main = 
    let
        x1 =  fun1 (A 2 3) == 5
        x2 =  fun1 (B 5)   == 36 
        x3 =  fun1 (C)     == 36
        x4 =  fun2 (A 3 6) == 98
        x5 =  fun2 (B 9)   == 36 
        x6 =  fun2 (C)     == 98
        x7 =  eq (A 1 2) (A 1 2)
        x9 =  not (eq (A 1 3) (A 1 4))
        x8 =  not (eq (A 1 3) (B 1))
        y1 =  eq (B 6) (B 6)
        y2 =  not (eq (B 2) (B 4))
        y3 =  not (eq (B 4) (C))
        y4 =  eq (C) (C)
        y5 =  not (eq (C) (A 2 4))
    in 
        x1 && x2 && x3 && x4 && x5 && x6 && x7 && x8 && x9 && y1 && y2 && y3 && y4 && y5
    