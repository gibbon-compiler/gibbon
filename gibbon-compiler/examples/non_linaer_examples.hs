module X where

data List = ListInner Int List | ListEnd Int
data Tree = Leaf Int | Inner Int Tree Tree
data ListOfList = LListInner List ListOfList| LListEnd


value :: List -> Int
value ls = case ls of
   ListInner v rem -> v
   ListEnd v -> v

valueT :: Tree -> Int
valueT ls = case ls of
   Inner v l r  -> v
   Leaf v -> v


nonLinear :: List -> List
nonLinear n = case n of
  ListInner v rem ->   ListInner ((value rem)*v) (nonLinear rem)
  ListEnd v -> ListEnd v

linear :: List -> List
linear n = case n of
   ListInner v rem  -> ListInner (v*10)  (linear rem)
   ListEnd v -> ListEnd v

nonLinearT :: Tree -> Tree
nonLinearT n = case n of
  Inner v l r  ->   Inner ((valueT  (nonLinearT l)*v) + (valueT r))   (nonLinearT l)  r
  Leaf v -> Leaf v

linearT :: Tree -> Tree
linearT n = case n of
   Inner v l r  -> Inner (v*10)  (linearT l)  (linearT r)
   Leaf v -> Leaf v

buildList :: Int-> List
buildList n =
  if (n==0)
    then ListEnd 1
    else ListInner n (buildList (n-1) )

buildTree:: Int-> Tree
buildTree n =
  if (n==0)
    then Leaf 1
    else Inner n (buildTree (n-1)) (buildTree (n-1))


fc:: List -> Int
fc ls = case ls of
    ListInner h tail -> h+10
    ListEnd v -> v +10

fa:: List -> List
fa ls = case ls of
    ListInner h tail ->
      let tail' = fa tail in
      let h' = fc tail' in
      ListInner h' tail'
    ListEnd v -> ListEnd v
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



-- genTree :: Int -> Tree
-- genTree n =
--   if n==0
--    then Leaf 1
--    else Inner (genTree ( n-1)) (genTree (n-1) )


-- gibbon_main =
--  let list1 = buildList 100 in
--  let ex1 = linear (nonLinear list1) in
--  let ex2 = nonLinear (linear list1) in
--  let ex3 = nonLinear (nonLinear list1) in
--  let ex4 = linear (linear list1) in
--  (ex1,ex2, ex3, ex4)


gibbon_main =
 let list1 = buildTree 10 in
 let ex1 = linearT (nonLinearT list1) in
 let ex2 = nonLinearT (linearT list1) in
 let ex3 = nonLinearT (nonLinearT list1) in
 let ex4 = linearT (linearT list1) in
 (ex1,ex2, ex3, ex4)