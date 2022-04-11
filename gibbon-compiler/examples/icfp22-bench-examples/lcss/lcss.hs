module Main where

import Gibbon.Vector

data Plist a = Nil | Cons a (Plist a)  

sndList :: Plist (Int, Int)  -> Plist Int 
sndList tupleList = case tupleList of
                         Nil           ->  Nil
                         Cons aVal rst -> let (a, b) = aVal
                                              in Cons b (sndList rst)  

max :: Int -> Int -> Int 
max a' b' = if (a' >= b') then a' else b'

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
                                                kjcurr = if (tell) then addVal else maxVal
                                                newTup = (y, kjcurr)
                                                in Cons newTup (algb2 x k0j kjcurr ys) 


algb1 :: Plist Int -> Plist (Int, Int) -> Plist Int
algb1 list1 ys' = case list1 of 
                       Nil -> sndList ys'
                       Cons x xs -> let recurse = algb1 xs (algb2 x 0 0 ys')
                                                         in recurse                             
                                        

zeroTupleList :: Plist Int  -> Plist (Int, Int)
zeroTupleList list = case list of 
                         Nil -> Nil
                         Cons y rst -> Cons (y, 0) (zeroTupleList rst)


algb :: Plist Int -> Plist Int -> Plist Int
algb xs ys = let leftPart =  Cons 0 (algb1 xs (zeroTupleList ys))   
                 in leftPart 


zip :: Plist a -> Plist b -> Plist (a, b) 
zip list1 list2 = case list1 of
  Nil -> case list2 of 
             Nil -> Nil 
             Cons a rst -> Nil                                          
  Cons a rst -> case list2 of 
                       Nil -> Nil                                
                       Cons b rst' -> Cons (a,b) (zip rst rst')  


m_id :: Plist a -> Plist a 
m_id a = a


mreverse :: Plist Int -> Plist Int -> Plist Int
mreverse xs acc = case xs of
  Nil        -> acc
  Cons z zs  -> mreverse zs (Cons z acc)


elem :: Int -> Plist Int -> Bool
elem a list = case list of 
                   Nil       -> False
                   Cons x rst -> if (x == a) then True else (False || elem a rst) 

take :: Int -> Plist Int -> Plist Int
take num list = case list of 
                   Nil        -> Nil
                   Cons x rst -> if (num > 0) then Cons x (take  (num - 1) rst) else Nil
 

drop :: Int -> Plist Int -> Plist Int
drop num list = case list of 
                    Nil        -> Nil 
                    Cons x rst -> if (num <= 0) then Cons x rst else drop (num - 1) rst

findk :: Int -> Int -> Int -> Plist (Int, Int) -> Int
findk k km m list = case list of 
                       Nil -> km                 
                       Cons aVal rst -> let (x, y) = aVal
                                            in if ( (x + y) >= m ) then (findk (k + 1) k (x + y) rst) else (findk (k + 1) km m rst)



{- # INLINE # -}
ifalgc :: Bool -> Plist Int -> Plist Int -> Plist Int
ifalgc check list1 list2 = if (check) then list1 else list2

algc :: Int -> Int -> Plist Int -> Plist Int -> Plist Int -> Plist Int
algc m n xs ys ys' = case ys of 
                          Nil       -> m_id ys'
                          Cons x rst -> case xs of 
                                          Nil -> Nil
                                          Cons x' rst' -> case rst' of 
                                                               Nil -> let isElem :: Bool
                                                                          headList, idList :: Plist Int
                                                                          isElem = elem x' ys 
                                                                          headList = Cons x' ys' 
                                                                          idList   = m_id ys'
                                                                          in (ifalgc isElem headList idList)    
                                                               Cons x'' rst'' -> let m2 = m / 2                                    
                                                                                     xs1 = take m2 xs
                                                                                     xs2 = drop m2 xs                                                                 
                                                                                     l1  = algb xs1 ys
                                                                                     l2  = mreverse (algb (mreverse xs2 Nil) (mreverse ys Nil)) Nil
                                                                                     k   = findk 0 0 (-1) (zip l1 l2)
                                                                                     algc'  = algc (m - m2) (n - k) xs2 (drop k ys) ys'
                                                                                     algc'' = algc m2 k xs1 (take k ys) algc'
                                                                                     in algc''


length' :: Plist a -> Int 
length' list = case list of 
                    Nil         -> 0 
                    Cons a rst  -> 1 + (length' rst)         

lcss :: Plist Int -> Plist Int -> Plist Int
lcss xs ys = algc (length' xs) (length' ys) xs ys Nil  

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


unitTestListComp :: Plist Int -> Plist Int -> Bool 
unitTestListComp list1 list2 = case list1 of 
                               Nil -> case list2 of
                                      Nil -> True  
                                      Cons x rst -> False 
                               Cons x rst -> case list2 of
                                             Nil -> False  
                                             Cons x' rst' -> if x == x' then True && (unitTestListComp rst rst') else False 

-- Main program to run longest common subsequence
bench_main :: ()
bench_main = 
  let f :: Vector Int
      a', b', c', d', e', f'  :: Int
      l1, l2, l3, l4          :: Plist Int
      t1                      :: Bool
      f        = readArrayFile Nothing
      a' = nth f 0
      b' = nth f 1
      c' = nth f 2
      d' = nth f 3
      e' = nth f 4
      f' = nth f 5
      l1 = makeIntList a' c' (b' - a')
      l2 = makeIntList d' f' (e' - d')
      _ = printsym (quote "\n" )
      _ = printsym (quote "The output list produced is\n" )
      l3  = lcss l1 l2
      _   = printIntList l3
      -- for sanity checking, make list l4 and use unitTestListComp function
      l4 = makeIntList (nth f 6) (nth f ((length f) - 1)) ((nth f 7) - (nth f 6))
      t1 = unitTestListComp l3 l4
      _ = printsym (quote "\n" )
      _ = printsym (quote "The result of checking the output produced by gibbon lcss is\n" )
      _ = printbool t1
      _ = printsym (quote "\n" )

  in ()

gibbon_main = bench_main


-- Instructions to run

-- Command use to run 

-- 1.) Fast: gibbon --packed --to-exe lcss.hs; ./lcss.exe --array-input-length 1007 --array-input lcss.faststdin
-- 2.) Norm: gibbon --packed --to-exe lcss.hs; ./lcss.exe --array-input-length 1007 --array-input lcss.normstdin  
-- 3.) Slow: gibbon --packed --to-exe lcss.hs; ./lcss.exe --array-input-length 3007 --array-input lcss.slowstdin