module Main where

import Gibbon.Vector

-- data A = Val Int | Tup A A

-- data MList = ENil | Cons A (MList)

data Plist a = Nil | Cons a (Plist a)  

sndList :: Plist (Int, Int)  -> Plist Int 
sndList tupleList = case tupleList of
                         Nil           ->  Nil
                         Cons aVal rst -> let (a, b) = aVal
                                              in Cons b (sndList rst)  

-- --Map function over a PackedList
-- pmap :: (a -> b) -> Plist a -> Plist b 
-- pmap f a = case a of 
--             Nil -> Nil
--             Cons x rst -> Cons (f x) (pmap f rst)  

-- --second function to get the second element of the tuple
-- snd :: a -> b 
-- snd tuple = let (x, y) = tuple
--                  in y



-- max_A :: A -> A -> A 
-- max_A a b = case a of 
--                Val a' -> case b of 
--                             Val b' -> if (a' >= b') then (Val a') else (Val b')
--                             Tup l m -> b -- error out not support max on tuple case
--                Tup l m -> a -- error out not supporting max on tuple case

max :: Int -> Int -> Int 
max a' b' = if (a' >= b') then a' else b'



-- ifalgb :: Bool -> A -> A -> A 
-- ifalgb tell add max = if (tell) then add else max

ifalgb :: Bool -> Int -> Int -> Int 
ifalgb tell add max = if (tell) then add else max


-- -- Function to make a tuple out of two A values
-- makeTuple :: A -> A -> A 
-- makeTuple val1 val2 = case val1 of 
--                            Val a -> case val2 of 
--                                          Val b     -> (Tup (Val a) (Val b))
--                                          Tup a' b' -> val2 

--                            Tup a' b' -> case val2 of 
--                                              Val b''     -> val1
--                                              Tup a'' b'' -> val2 

algb2 :: Int -> Int -> Int -> Plist (Int, Int) -> Plist (Int, Int)
algb2 x k0j1 k1j1 mList = case mList of 
                            Nil      -> Nil
                            Cons aVal ys -> let (y, k0j) = aVal
                                                kjcurr, addVal, maxVal :: Int
                                                newTup                 :: (Int, Int)
                                                tell   :: Bool 
                                                tell   = (x == y)
                                                addVal = k0j1 + 1
                                                maxVal = max k1j1 k0j 
                                                --_ = printA maxVal
                                                --_   = printsym (quote "\n")
                                                --_ = printA addVal
                                                --_   = printsym (quote "\n")
                                                --_ = printbool tell
                                                --_   = printsym (quote "\n")
                                                kjcurr = ifalgb tell addVal maxVal
                                                --_ = printA kjcurr
                                                --_ = printsym (quote "\n")
                                                newTup = (y, kjcurr)
                                                --_ = printsym (quote "\nPrint newTuple\n")
                                                --_ = printA newTup
                                                --_ = printsym (quote "\nys\n")
                                                --_ = printList ys
                                                --_ = printsym (quote "\nx\n")
                                                --_ = printA x
                                                --_ = printsym (quote "\n")
                                                --_ = printsym (quote "\nk0j\n")
                                                --_ = printA k0j
                                                --_ = printsym (quote "\n")
                                                --_ = printsym (quote "kjcur\n")
                                                --_ = printA kjcurr
                                                --_ = printsym (quote "\n")
                                                --rstPart = (algb2 x k0j kjcurr ys)
                                                --newList = Cons newTup (rstPart)
                                                --_ = printsym (quote "Printing the new List here!\n")
                                                --_       = printList newList
                                                --_ = printsym (quote "\n")
                                                in Cons newTup (algb2 x k0j kjcurr ys)  --  newList


algb1 :: Plist Int -> Plist (Int, Int) -> Plist Int
algb1 list1 ys' = case list1 of 
                       Nil -> sndList ys'
                       Cons x xs -> let recurse = algb1 xs (algb2 x 0 0 ys')
                                                          -- _ = printsym (quote "Print the algb2Part in algb1 here!\n")
                                                          -- _         = printList algb2Part
                                                          -- _ = printsym (quote "\n")
                                                         in recurse                             
                                        

zeroTupleList :: Plist Int  -> Plist (Int, Int)
zeroTupleList list = case list of 
                         Nil -> Nil
                         Cons y rst -> Cons (y, 0) (zeroTupleList rst)


algb :: Plist Int -> Plist Int -> Plist Int
algb xs ys = let leftPart =  Cons 0 (algb1 xs (zeroTupleList ys))
                 --result   =  leftPart
                 --_ = printsym (quote "Print the result in algb here!\n")
                 --_ = printList leftPart
                 --_ = printsym (quote "\n")      
                 in leftPart 


-- mzip :: MList -> MList -> MList
-- mzip list1 list2 = case list1 of
--   ENil -> case list2 of 
--              ENil          -> ENil 
--              Cons aVal rst -> ENil                                            -- should this be an error situation coz lists should technically be of the same length ? 
--   Cons aVal rst -> case list2 of 
--                        ENil           -> ENil                                 -- should this be an error situation coz lists should technically be of the same length ? 
--                        Cons bVal rst' -> Cons (makeTuple aVal bVal)  (mzip rst rst')   -- zip the rest of the lists together


zip :: Plist a -> Plist b -> Plist (a, b) 
zip list1 list2 = case list1 of
  Nil -> case list2 of 
             Nil -> Nil 
             Cons a rst -> Nil                                            -- should this be an error situation coz lists should technically be of the same length ? 
  Cons a rst -> case list2 of 
                       Nil -> Nil                                 -- should this be an error situation coz lists should technically be of the same length ? 
                       Cons b rst' -> Cons (a,b) (zip rst rst')   -- zip the rest of the lists together


-- This function looks correct, return exact copy of the list
m_id :: Plist a -> Plist a 
m_id a = a


-- tested mreverse works, now
mreverse :: Plist Int -> Plist Int -> Plist Int
mreverse xs acc = case xs of
  Nil        -> acc
  Cons z zs  -> mreverse zs (Cons z acc)

-- comp_MList :: MList -> MList -> Bool
-- comp_MList list1 list2 = case list1 of 
--                                  ENil -> case list2 of 
--                                           ENil -> True
--                                           Cons x rst -> False
--                                  Cons x' rst' -> case list2 of
--                                                     ENil         -> False
--                                                     Cons y rst'' -> if (comp_A x' y) then (True && (comp_MList rst' rst'')) else False
-- --Equality operator for type A
-- comp_A :: A -> A -> Bool
-- comp_A a b = case a of 
--              Val x -> case b of 
--                         Val y -> if x == y then True else False
--                         Tup l m -> False 
--              Tup a' b' -> case b of 
--                              Val y' -> False
--                              Tup l' m' -> (comp_A a' l') && (comp_A b' m')

-- --Greater x > y for type A
-- gr_A :: A -> A -> Bool 
-- gr_A a b = case a of 
--              Val x -> case b of 
--                          Val y   -> if (x > y) then True else False
--                          Tup a b -> False -- This should error out find a way to error out in gibbon
--              Tup x y -> case b of 
--                           Val y'  -> False -- This should error out find a way to error out in gibbon
--                           Tup a b -> if (gr_A x a) && (gr_A y b) then True else False  


-- Tested elem it works correctly
elem :: Int -> Plist Int -> Bool
elem a list = case list of 
                   Nil       -> False
                   Cons x rst -> if (x == a) then True else (False || elem a rst) 



-- This works now, tested and degubbed it
take :: Int -> Plist Int -> Plist Int
take num list = case list of 
                   Nil        -> Nil
                   Cons x rst -> if (num > 0) then Cons x (take  (num - 1) rst) else Nil
 

-- This works 
drop :: Int -> Plist Int -> Plist Int
drop num list = case list of 
                    Nil        -> Nil 
                    Cons x rst -> if (num <= 0) then Cons x rst else drop (num - 1) rst

-- add_A :: A -> A -> A
-- add_A v1 v2 = case v1 of 
--                  Val x -> case v2 of 
--                             Val y -> Val (x + y)
--                             Tup a b -> v1          -- This should technically call error saying that can't add Tup and Val kinds but for now can return just v1
--                  Tup x y -> case v2 of 
--                               Tup a b -> Tup (add_A x a) (add_A y b)
--                               Val a'  -> v1        -- This should also technically error out saying that can't add val to Tup but for now this works 

-- sub_A :: A -> A -> A
-- sub_A v1 v2 = case v1 of 
--                  Val x -> case v2 of 
--                             Val y -> Val (x - y)
--                             Tup a b -> v1          -- This should technically call error saying that can't add Tup and Val kinds but for now can return just v1
--                  Tup x y -> case v2 of 
--                               Tup a b -> Tup (sub_A x a) (sub_A y b)
--                               Val a'  -> v1        -- This should also technically error out saying that can't add val to Tup but for now this works 

findk :: Int -> Int -> Int -> Plist (Int, Int) -> Int
findk k km m list = case list of 
                       Nil -> km                 
                       Cons aVal rst -> let (x, y) = aVal
                                            in if ( (x + y) >= m ) then (findk (k + 1) k (x + y) rst) else (findk (k + 1) km m rst)

-- -- The division function works                                                        
-- div_A :: A -> A -> A 
-- div_A a b = case a of 
--                 Val intVal -> case b of 
--                                Val intVal'   -> Val (div intVal intVal')
--                                Tup a' b'     -> a -- this should be error, so handle this later 
--                 Tup a'' b'' -> case b of 
--                                 Val intVal'  -> a -- this should be error, so handle this later
--                                 Tup a' b'    -> Tup (div_A a'' a') (div_A b'' b') 



ifalgc :: Bool -> Plist Int -> Plist Int -> Plist Int
ifalgc check list1 list2 = if (check) then list1 else list2


appendCons :: Int -> Plist Int -> Plist Int
appendCons val tail = Cons val tail

algc :: Int -> Int -> Plist Int -> Plist Int -> Plist Int -> Plist Int
algc m n xs ys ys' = case ys of 
                          Nil       -> m_id ys'
                          Cons x rst -> case xs of 
                                          Nil -> Nil
                                          Cons x' rst' -> case rst' of 
                                                               Nil -> let isElem :: Bool
                                                                          headList, idList :: Plist Int
                                                                          isElem = elem x' ys 
                                                                          headList = appendCons x' ys' 
                                                                          idList   = m_id ys'
                                                                          --_  = printsym  (quote "\n")
                                                                          --_  = printbool isElem 
                                                                          --_  = printsym  (quote "\n")
                                                                          --_  = printsym  (quote "\n")
                                                                          --_  = printsym  (quote "ys'")
                                                                          --_  = printList ys' 
                                                                          --_  = printsym  (quote " || Cons x ys'")
                                                                          --_  = printList headList
                                                                          --_  = printsym  (quote " || x ")
                                                                          --_  = printA x'
                                                                          --_  = printsym  (quote "\n")
                                                                          in (ifalgc isElem headList idList)    
                                                               Cons x'' rst'' -> let m2 = m / 2                                    
                                                                                     xs1 = take m2 xs
                                                                                     xs2 = drop m2 xs
                                                                                     --  _   = printsym (quote "\n")
                                                                                     --  _   = printsym (quote "Print m2 value in algc\n")
                                                                                     --  _   = printA m2
                                                                                     --  _   = printsym (quote "\n")
                                                                                     --  _   = printsym (quote "Print the List xs1 in algc\n")
                                                                                     --  _   = printList xs1
                                                                                     --  _   = printsym (quote "\n")
                                                                                     --  _   = printsym (quote "Print the List xs2 in algc\n")
                                                                                     --  _   = printList xs2
                                                                                     --  _   = printsym (quote "\n")
                                                                                     --  _   = printsym (quote "Print the List ys in algc\n")
                                                                                     --  _   = printList ys
                                                                                     --  _   = printsym (quote "\n")                                                                                              
                                                                                     l1  = algb xs1 ys
                                                                                     l2  = mreverse (algb (mreverse xs2 Nil) (mreverse ys Nil)) Nil
                                                                                     k   = findk 0 0 (-1) (zip l1 l2)
                                                                                     --  _ = printsym (quote "List l1!\n")
                                                                                     --  _ = printList l1
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "List l2!\n")
                                                                                     --  _ = printList l2
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "K in algc!\n")
                                                                                     --  _ = printA k
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "\n")
                                                                                     algc'  = algc (m - m2) (n - k) xs2 (drop k ys) ys'
                                                                                     algc'' = algc m2 k xs1 (take k ys) algc'
                                                                                     --  _ = printsym (quote "List algc'!\n")
                                                                                     --  _ = printList algc'
                                                                                     --  _ = printsym (quote "\n")
                                                                                     --  _ = printsym (quote "List algc''!\n")
                                                                                     --  _ = printList algc''
                                                                                     --  _ = printsym (quote "\n")
                                                                                     -- _  = printsym (quote "\nPrint the variables in algc function\n")
                                                                                     -- _  = printsym (quote "Print m2 value:\n")
                                                                                     -- _   = printA m2
                                                                                     -- _   = printsym (quote "\nPrint the List xs1\n")
                                                                                     -- _   = printList xs1
                                                                                     -- _   = printsym (quote "\nPrint the List xs2\n")
                                                                                     -- _   = printList xs2
                                                                                     -- _   = printsym (quote "\nPrint the List l1\n")
                                                                                     -- _   = printList l1
                                                                                     -- _   = printsym (quote "\nPrint the List l2\n")
                                                                                     -- _   = printList l2
                                                                                     -- _   = printsym (quote "\nPrint the value k\n")
                                                                                     -- _   = printA k
                                                                                     -- _   = printsym (quote "\nPrint the List algc'\n")
                                                                                     -- _   = printList algc'
                                                                                     -- _   = printsym (quote "\nPrint the List algc''\n")
                                                                                     -- _    = printList algc''
                                                                                     in algc''


-- length' :: MList -> A 
-- length' list = case list of 
--                    ENil          -> (Val 0) 
--                    Cons aVal rst -> add_A (Val 1) (length' rst)   


length' :: Plist a -> Int 
length' list = case list of 
                    Nil         -> 0 
                    Cons a rst  -> 1 + (length' rst)   



-- lcss :: MList -> MList -> MList
-- lcss xs ys = algc (length' xs) (length' ys) xs ys ENil           

lcss :: Plist Int -> Plist Int -> Plist Int
lcss xs ys = algc (length' xs) (length' ys) xs ys Nil  


--Make a packed Int List from start index to an end index
makeIntList :: Int -> Int -> Int -> Plist Int
makeIntList start end skipFactor = if (start <= end) then Cons start (makeIntList (start + skipFactor) end skipFactor) else Nil

printIntList :: Plist Int -> ()
printIntList list = case list of 
                      Nil -> 
                        let _ = printsym (quote " Nil " )
                        in ()
                      Cons x rst -> 
                        let _ = printsym (quote " Cons " ) 
                            _ = printint x                           
                            _ = printsym (quote " ->" )
                            _ = printIntList rst
                        in ()

printTupleList :: Plist (Int, Int) -> ()
printTupleList list = case list of 
                      Nil -> 
                        let _ = printsym (quote " Nil " )
                        in ()
                      Cons x rst -> 
                        let _ = printsym (quote " Cons " )
                            (a,b) = x
                            _ = printsym (quote "(") 
                            _ = printint a
                            _ = printsym (quote ",")
                            _ = printint b
                            _ = printsym (quote ")")                           
                            _ = printsym (quote " ->" )
                            _ = printTupleList rst
                        in ()

-- Main program to run longest common subsequence
bench_main :: ()
bench_main = 
  let f :: Vector Int
      a', b', c', d', e', f'  :: Int
      l1, l2, l3              :: Plist Int
      l4                      :: Plist (Int, Int)
      t1, t2                  :: Bool
      f  = readArrayFile Nothing
      --_  = printVec (\i -> printint i) f
      a' = nth f 0
      b' = nth f 1
      c' = nth f 2
      d' = nth f 3
      e' = nth f 4
      f' = nth f 5
      --_  = printsym (quote "\n")
      --_  = printint a'
      --_  = printsym (quote "\n")
      --_  = printint b'
      --_  = printsym (quote "\n")
      --_  = printint c'
      --_  = printsym (quote "\n")
      --_  = printint d'
      --_  = printsym (quote "\n")
      --_  = printint e'
      --_  = printsym (quote "\n")
      --_  = printint f'
      --_  = printsym (quote "\n")
      l1 = makeIntList a' c' (b' - a')
      l2 = makeIntList d' f' (e' - d')
      -- lenth' function looks correct
     -- len  = length' l1
     -- len1 = length' l2 
      -- m_id function looks correct
     -- l3  = m_id l1                 
     -- _   = printsym (quote "Print the list lengths!!\n")
     -- _   = printA len
     -- _   = printsym (quote "\n")
     -- _   = printA len1
     -- _   = printsym (quote "\n")
      --_   = printsym (quote "Print int List l1!\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printIntList l1
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "Print int List l2!\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printIntList l2
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --t1  = comp_A len len1 
      --_   = printbool t1
      --_   = printsym (quote "\n")
      --t2  = comp_MList l1 l2
      --_   = printbool t2
      --_   = printsym (quote "\n")
      --chelem = (Val 2)
      --t2     = elem chelem l1
      --_   = printbool t2
      --_   = printsym (quote "Check Arithmetic!\n") 
      --t1 = (gr_A (Val 0) (Val 0)) || (comp_A (Val 0) (Val 0))
      --t1 = comp_MList ENil ENil 
      --_   = printbool t1
      --chelem = max_A (Val 100) (Val 2)
     -- _   = printsym (quote "\nPrint the max function out\n")
     -- _   = printA chelem 
     -- _   = printsym (quote "\n")
      --n1  = (Val 1)
      --_   = printA n1 
      --_   = printsym (quote "Result of take\n")
      --l4  = drop n1 l1
      --_   = printList l4
      --_   = printsym (quote "Check reverse List!\n")
      --l4  = mreverse l1 ENil
      --_   = printList l4
      --_   = printsym (quote "\n")
      --_   = printsym (quote "Check zip List!\n")
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --l4  = zip l1 l2
      --_   = printsym (quote "\n")
      --_   = printsym (quote "\n")
      --_   = printTupleList l4
      --_   = printsym (quote "\n")
      --_   = printsym (quote "Print output of zero tuple list\n")
      --l4 = zeroTupleList l1
      --l4  = sndList l4
      --_   = printList l4
      --_   = printsym (quote "\n")
      --chelem = add_A len len1
      --_   = printA chelem
      --_   = printsym (quote "\n")
      l3  = lcss l1 l2
      --_   = printsym (quote "\n")
      _   = printsym (quote "The final output produced is:\n")
      _   = printIntList l3
      _   = printsym (quote "\n")

  in ()

gibbon_main = bench_main


-- Instructions to run

-- Command use to run 
-- gibbon --packed --to-exe lcss.hs; ./lcss.exe --array-input-length 6 --array-input lcss.txt 
-- Modify lcss.txt file for 3 cases like so: 

-- 1.) Fast   Case  -> 1 
--                     2
--                     2000
--                     1000
--                     1001
--                     2000

-- 2.) Slow   Case  -> 1
--                     2
--                     2000
--                     1000
--                     1001
--                     4000 

-- 3.) Normal Case  -> 1
--                     2 
--                     4000
--                     1000
--                     1001
--                     4000
