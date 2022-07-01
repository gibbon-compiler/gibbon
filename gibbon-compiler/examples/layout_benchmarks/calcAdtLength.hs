module Main where

import Strings
import Contents
import Adts                            

-- Recursive function to get length
getLength :: Adt -> Int
getLength adt = case adt of 
                     Nil              -> 0
                     CA content next  -> 1 + getLength next
                     AC next content  -> 1 + getLength next
                                         

-- Tail recursice function to get length, using the tail recursice version
getLengthTR :: Adt -> Int -> Int
getLengthTR adt accumulator = case adt of 
                                         Nil -> accumulator
                                         CA content next -> getLengthTR next (1+accumulator)
                                         AC next content -> getLengthTR next (1+accumulator)
                            


-- This is an example comparing the performance of 2 Adts AC and CA
-- AC -> next Adt first, Content after
-- CA -> Content first, next Adt after
-- This example counts the length of the adt
-- The Adt layout AC is theoretically suppoed to be faster since that layout will traverse a much smaller part of the list
-- The Adt layout CA on the other hand will have to chase pointers to the next Adt to skip the content and traverse the complete list to get to Nil
                            
gibbon_main = 
    let ac = mkACList 1000000 100
        ca = mkCAList 1000000 100
        --_     = printAdt ac
        --_     = printsym (quote "NEWLINE")
        --_     = printAdt ca
        --_     = printsym (quote "NEWLINE")
        _     = printsym (quote "Time for Adt: AC")
        _     = printsym (quote "NEWLINE")
        count1 = iterate (getLengthTR ac 0)
        _     = printsym (quote "Count of Adt AC is: ")
        _     = printint count1
        _     = printsym (quote "NEWLINE")
        _     = printsym (quote "NEWLINE")
        _     = printsym (quote "Time for Adt: CA")
        _     = printsym (quote "NEWLINE")
        count2 = iterate (getLengthTR ca 0)
        _     = printsym (quote "Count of Adt CA is: ")
        _     = printint count2
        _     = printsym (quote "NEWLINE")
    in ()
