module X where

data List = ListInner Int List | ListEnd
data Tree = Leaf Int | Inner Tree Tree
data ListOfList = LListInner List ListOfList| LListEnd

--sum (square list)
square :: List -> List
square n = case n of
  ListInner v rem ->   ListInner (v*v) (square rem)
  ListEnd -> ListEnd

sumList :: List -> Int
sumList n = case n of
   ListInner v rem  -> v + (sumList rem)
   ListEnd -> 0

buildList :: Int-> List
buildList n =
  if (n==0)
    then ListEnd
    else ListInner n (buildList (n-1) )

-------------------------------------

flipTreeAcc :: Tree -> Tree
flipTreeAcc zt =
  case zt of
    Leaf x ->Leaf x
    -- we have one call and then
    Inner l r -> Inner (flipTreeAcc (flipTreeAcc r)) (flipTreeAcc(flipTreeAcc l))

---------------------------------
flipTreeReg :: Tree -> Tree
flipTreeReg zt =
  case zt of
    Leaf x ->Leaf x
    -- we have one call and then
    Inner l r -> Inner (flipTreeReg r) (flipTreeReg l)

------------------------------------
append :: List -> List -> List
append ls1 ls2 = case ls1 of
    ListInner v tail -> ListInner v (append tail ls2)
    ListEnd          -> ls2

-- non treeless form flatten
flatten_1 :: ListOfList -> List
flatten_1 lss = case lss of
  LListInner ls rem -> append ls (flatten_1 rem)
  LListEnd -> ListEnd


flattenTree :: Tree -> List
flattenTree tree = case tree of
  Inner l r -> append (flattenTree l) (flattenTree r)
  Leaf x -> ListInner x ListEnd

-- tree less form flatten [ no need we want things that done work right?]
-- flatten_2 :: ListOfList -> List
-- flatten_1 lss = case lss of
--   LListInner ls rem ->flatten_3å
--   LListEnd -> LListEnd


-- tree less form flatten I dont
-- flatten_2 :: ListOfList -> List
-- flatten_1 lss = case lss of
--   LListInner ls rem -> flatten_3 ls rem
--   LListEnd -> LListEnd


genTree :: Int -> Tree
genTree n =
  if n==0
   then Leaf 1
   else Inner (genTree ( n-1)) (genTree (n-1) )


gibbon_main =
 let list1 = buildList 100 in
 let list2 = buildList 100 in
 let list3 = buildList 100 in
 let lss = LListInner list1 (LListInner list2 LListEnd) in
 let tree = (genTree 3) in

 let ex1 = sumList (square list1) in
 let ex2 =  flipTreeAcc (flipTreeAcc tree) in -- actual non termination
 let ex3 =  flipTreeReg (flipTreeReg tree) in -- non treeless but terminates
 -- issue
 let ex4 = append (append list1 list2) list3 in
 let ex5 = sumList (flatten_1 lss) in
 let ex6 = sumList (flattenTree tree) in
 (ex1, ex2, ex3, ex4, ex5)
