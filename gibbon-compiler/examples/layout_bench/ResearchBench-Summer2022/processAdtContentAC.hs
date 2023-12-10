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

gibbon_main = 
    let ac            = mkACList 300 10
        ac_new        = processAdt ac
    in lengthAdt ac_new == lengthAdt ac
