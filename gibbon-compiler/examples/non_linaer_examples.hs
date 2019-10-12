module X where

data List = ListInner Int List | ListEnd
data Tree = Leaf Int | Inner Tree Tree
data ListOfList = LListInner List ListOfList| LListEnd


value :: List -> Int
value ls = case ls of
   ListInner v rem -> v
   ListEnd -> 0

--sum (square list)
nonLinear :: List -> List
nonLinear n = case n of
  ListInner v rem ->   ListInner ((value rem)*v) (nonLinear rem)
  ListEnd -> ListEnd

linear :: List -> List
linear n = case n of
   ListInner v rem  -> ListInner (v*10)  (linear rem)
   ListEnd -> ListEnd

buildList :: Int-> List
buildList n =
  if (n==0)
    then ListEnd
    else ListInner n (buildList (n-1) )

-- -------------------------------------

-- flipTreeAcc :: Tree -> Tree
-- flipTreeAcc zt =
--   case zt of
--     Leaf x ->Leaf x
--     -- we have one call and then
--     Inner l r -> Inner (flipTreeAcc (flipTreeAcc r)) (flipTreeAcc(flipTreeAcc l))

-- ---------------------------------
-- flipTreeReg :: Tree -> Tree
-- flipTreeReg zt =
--   case zt of
--     Leaf x ->Leaf x
--     -- we have one call and then
--     Inner l r -> Inner (flipTreeReg r) (flipTreeReg l)

-- ------------------------------------
-- append :: List -> List -> List
-- append ls1 ls2 = case ls1 of
--     ListInner v tail -> ListInner v (append tail ls2)
--     ListEnd          -> ls2

-- -- non treeless form flatten
-- flatten_1 :: ListOfList -> List
-- flatten_1 lss = case lss of
--   LListInner ls rem -> append ls (flatten_1 rem)
--   LListEnd -> ListEnd


-- flattenTree :: Tree -> List
-- flattenTree tree = case tree of
--   Inner l r -> append (flattenTree l) (flattenTree r)
--   Leaf x -> ListInner x ListEnd



genTree :: Int -> Tree
genTree n =
  if n==0
   then Leaf 1
   else Inner (genTree ( n-1)) (genTree (n-1) )


gibbon_main =
 let list1 = buildList 100 in
 let ex1 = linear (nonLinear list1) in
 let ex2 = nonLinear (linear list1) in
 let ex3 = nonLinear (nonLinear list1) in
 let exp4 = linear (linear list1) in
 (ex1, ex2, ex3, exp4)
