{-# LANGUAGE TemplateHaskell #-}
module TestCopyPackedCalls where

import Gibbon.Prelude 
import Gibbon.Vector 


data R1 = A Int (R1) | AE

data S1 = B (Vector Char)

data TestCopyPacked =   T1 R1 S1 TestCopyPacked
                      | T2 R1 TestCopyPacked S1
                      | T3 S1 R1 TestCopyPacked 
                      | T4 S1 TestCopyPacked R1 
                      | T5 TestCopyPacked R1 S1 
                      | T6 TestCopyPacked S1 R1
                      | Nil


mkR1 :: Int -> R1 
mkR1 len = if len <= 0 
            then AE 
           else A len (mkR1 (len - 1))                      

mkS1 :: S1 
mkS1 = let 
         vec :: Vector Char
         vec = "init"
        in B vec

processR1 :: R1 -> R1 
processR1 r1 = case r1 of 
                   AE        -> AE 
                   A val rst -> A (val+1) (processR1 rst)
                   
                   
                   
processS1 :: S1 -> S1 
processS1 s1 = case s1 of 
                 B vec -> B "blah" 



traversal1 :: TestCopyPacked -> TestCopyPacked 
traversal1 t1 = case t1 of
                    Nil -> Nil 
                    T1 r1 s1 rst -> let  r1'  = processR1 r1
                                         rst' = traversal1 rst 
                                       in T1 r1' s1 rst'

                              

traversal2 :: TestCopyPacked -> TestCopyPacked 
traversal2 t1 = case t1 of
                    Nil -> Nil 
                    T1 r1 s1 rst -> let  r1'  = processR1 r1
                                         rst' = traversal2 rst 
                                       in T2 r1' rst' s1


traversal3 :: TestCopyPacked -> TestCopyPacked
traversal3 t1 = case t1 of 
                     Nil -> Nil
                     T1 r1 s1 rst -> let r1'  = processR1 r1 
                                         s1'  = processS1 s1
                                         rst' = traversal3 rst 
                                       in T3 s1' r1' rst' 

traversal4 :: TestCopyPacked -> TestCopyPacked
traversal4 t1 = case t1 of 
                     Nil -> Nil
                     T1 r1 s1 rst -> let r1'  = processR1 r1 
                                         rst' = traversal4 rst 
                                       in T3 s1 r1' rst' 



traversal5 :: TestCopyPacked -> TestCopyPacked 
traversal5 t1 = case t1 of 
                     Nil -> Nil 
                     T1 r1 s1 rst -> let r1'  = processR1 r1
                                         rst' = traversal5 rst
                                       in T4 s1 rst' r1' 


traversal6 :: TestCopyPacked -> TestCopyPacked 
traversal6 t1 = case t1 of 
                    Nil -> Nil 
                    T1 r1 s1 rst -> let r1'  = processR1 r1 
                                        rst' = traversal5 rst
                                      in T5 rst' r1' s1


traversal7 :: TestCopyPacked -> TestCopyPacked 
traversal7 t1 = case t1 of 
                     Nil -> Nil 
                     T1 r1 s1 rst -> let r1'  = processR1 r1
                                         rst' = traversal7 rst
                                       in T6 rst' s1 r1' 
  

gibbon_main = let
                t1  = (T1 (mkR1 1) (mkS1) (T1 (mkR1 1) (mkS1) Nil))
                t1' = traversal1 t1
                t2' = traversal2 t1
                t3' = traversal3 t1
                t4' = traversal4 t1
                t5' = traversal5 t1
                t6' = traversal6 t1
                t7' = traversal7 t1
                _  = printPacked t1
                _  = printsym (quote "")
                _  = printPacked t1'
                _  = printsym (quote "NEWLINE")
                _  = printPacked t2'
                _  = printsym (quote "NEWLINE")
                _  = printPacked t3'
                _  = printsym (quote "NEWLINE")
                -- -- ERROR
                -- _  = printPacked t4'
                -- _  = printsym (quote "NEWLINE")
                _  = printPacked t5'
                _  = printsym (quote "NEWLINE")
                _  = printPacked t6'
                _  = printsym (quote "NEWLINE")
                _  = printPacked t7'
                _  = printsym (quote "NEWLINE")
               in ()
