module Main where

import Strings
import Contents
import Adts                             

-- Recursive function to get length
getLength :: Adt -> Int
getLength adt = case adt of 
                     Nil              -> 0
                     CA content next  -> 1 + getLength next
                                         

-- Tail recursice function to get length, using the tail recursice version
getLengthTR :: Adt -> Int -> Int
getLengthTR adt accumulator = case adt of 
                                         Nil -> accumulator
                                         CA content next -> getLengthTR next (1+accumulator)
                            


-- This is an example testing the performance of the CA layout
-- CA -> Content comes first, next Adt comes after the content
-- This example counts the length of the CA abstract data type
-- The Adt layout CA is supposed to have a slower performence since it has to chase pointers to the next Adt to skip the content and traverse the complete list to get to Nil
                            
gibbon_main = 
    let ca = mkCAList 100 10
        count2 = getLengthTR ca 0
    in count2 == 100
