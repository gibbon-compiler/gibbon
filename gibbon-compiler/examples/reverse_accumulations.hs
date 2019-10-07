-- This example is from the paper:
-- A shortcut fusion approach to accumulations

-- cant be handled by original shortcut fusion. not sure about the others

data List = ListInner Int List | ListEnd

append :: List -> List -> List
append ls1 ls2 = case ls1 of
    ListInner v tail -> ListInner v (append tail ls2)
    ListEnd          -> ls2

reverseB :: List  -> List
reverseB ls1  = case ls1 of
    ListInner v tail -> append (reverseB tail) (ListInner v ListEnd)
    ListEnd          -> ListEnd
------------------------------------------------
-- this version is linear and holds the answer in the second parameter
-- so the second parameter is accumulating (growing larger)

reverseA ::  List -> List -> List
reverseA ls1 ls2 = case ls1 of
    ListInner v tail -> reverseA tail (ListInner v ls2)
    ListEnd          -> ls2

addN :: List -> Int -> List
addN ls a =
  case ls of
    ListInner v tail -> ListInner (v+1) (addN tail a)
    ListEnd          -> ListEnd

horner :: List -> Int
horner ls  =
  case ls of
    ListInner v tail -> v+10*(horner tail)
    ListEnd          -> 0

id:: List-> List
id x =
  case x of
   ListEnd ->ListEnd
   ListInner v tail->ListInner v tail


horner_reverseA :: List -> List -> Int
horner_reverseA ls =
  case ls of
      ListInner v tail -> ListInner (v+1) (addN tail a)
      ListEnd          -> horner


buildList :: Int-> List
buildList n =
  if (n==0)
    then ListEnd
    else ListInner n (buildList (n-1))

gibbon_main =
 let list1 = buildList 100 in
 -- accumulation as consumer
 let ex1 = reverseB (reverseB list1) in
 let ex2 = reverseA (reverseA  list1 ListEnd ) ListEnd in
 let ex3 = addN (reverseA  list1 ListEnd ) 3 in
 let ex4 = horner (reverseA  list1 ListEnd )in

 -- accumulation as producer, two types:
    --when the accumulators are used as context parameters to hold auxiliary values that are eventually used in the final


    -- when the intermediate data structure, or part of it, is directly constructed in the accumulators.  --

 (list1, ex1, ex2, ex3, ex4)
