module Main where

import Strings
import Contents
import Adts
         
processAdt :: Adt -> Adt
processAdt adt = case adt of 
                          Nil -> Nil
                          CA content rst -> 
                            let newContent  = processContent content 
                                newRst      = processAdt rst
                            in CA newContent newRst


processAdtTR :: Adt -> Adt -> Adt
processAdtTR adt accumulator = case adt of 
                                Nil -> accumulator
                                CA content rst -> 
                                    let newContent  = processContent content 
                                        append      = CA newContent accumulator
                                    in processAdtTR rst accumulator

loop :: Adt -> Int -> Adt 
loop adtIn iters = if (iters <= 0)
                   then adtIn
                   else let newAdt = processAdt adtIn
                        in loop adtIn (iters-1)

                


gibbon_main = 
    let len_list           = 80000
        len_string         = 100
        ca            = mkCAList len_list len_string
        -- _             = printsym (quote "CA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printAdt ca
        -- _             = printsym (quote "NEWLINE")
        ca_new        = iterate (loop ca 200)
        -- _             = printsym (quote "New CA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printAdt ca_new
        -- _             = printsym (quote "NEWLINE")
        
    in ()
