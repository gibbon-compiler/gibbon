-- Without Arguments
type A = Int

f :: Int -> Int 
f x = x + 1

g :: A -> A 
g x = x + 2

h :: A -> Int 
h x  = x + 3

ff :: Int -> A 
ff x = x + 4 

-- With data arguments
data B a b = B a b 
type C b = B Int b

foo :: C Float -> C Float
foo (B (x, y)) = B (x-1, y+1)

gibbon_main = (f 1, g 2, h 3, ff 4, foo (B (1, 2.2)))