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


gibbon_main = 
    let len_list           = 300
        len_string         = 10
        ca            = mkCAList len_list len_string
        ca_new        = processAdt ca
     in lengthAdt ca_new == lengthAdt ca
