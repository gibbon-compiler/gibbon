module Main where

import Strings
import Contents
import Adts
         
processAdt :: Adt -> Adt
processAdt adt = case adt of 
                    Nil -> Nil
                    AC rst content  -> let newContent = processContent content 
                                           newRst     = processAdt rst
                                       in AC newRst (copyPacked newContent)


--loop :: Adt -> Int -> Adt 
--loop adtIn iters = if (iters <= 0)
--                   then adtIn
--                   else let newAdt = processAdt adtIn
--                        in loop adtIn (iters-1)                                 

--processAdtTR :: Adt -> Adt -> Adt
--processAdtTR adt accumulator = case adt of
--                                Nil -> accumulator
--                                AC rst content ->
--                                    let newContent  = processContent content
--                                        append      = AC accumulator newContent
--                                    in processAdtTR rst append

gibbon_main = 
    let ac            = mkACList 3000000 10
        -- _             = printsym (quote "AC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked ac
        -- _             = printsym (quote "NEWLINE")
        -- _             = printsym (quote "CA Adt Time to process content: ")
        -- _             = printsym (quote "NEWLINE")
        ac_new        = iterate (processAdt ac)
        -- _             = printsym (quote "New AC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked ac_new
        -- _             = printsym (quote "NEWLINE")
    in ()
