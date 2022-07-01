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
                          AC rst content  -> 
                            let newContent = processContent content 
                                newRst     = processAdt rst
                            in AC newRst ( copyPacked newContent )
    
processContent :: Content -> Content
processContent content = case content of 
                              Image x -> Image (processString x)
                              Text  y -> Text  (processString y)

processString :: String -> String 
processString string = case string of
                            End -> End
                            Char val rst -> let addVal = val + 10
                                                mulVal = addVal * 10
                                                divVal = mulVal / 2
                                                modVal = mod divVal 128
                                            in Char modVal (processString rst)
                                    


gibbon_main = 
    let ca            = mkCAList 2000000 50
        --_             = printsym (quote "CA Adt: ")
        --_             = printsym (quote "NEWLINE")
        --_             = printAdt ca
        --_             = printsym (quote "NEWLINE")
        ac            = mkACList 2000000 50
        --_             = printsym (quote "AC Adt: ")
        --_             = printsym (quote "NEWLINE")
        --_             = printAdt ac
        --_             = printsym (quote "NEWLINE")
        _               = printsym (quote "CA Adt Time to process content: ")
        _               = printsym (quote "NEWLINE")
        ca_new        = iterate (processAdt ca)
        --_             = printsym (quote "New CA Adt: ")
        --_             = printsym (quote "NEWLINE")
        --_             = printAdt ca_new
        --_             = printsym (quote "NEWLINE")
        _               = printsym (quote "AC Adt Time to process content: ")
        _               = printsym (quote "NEWLINE")
        ac_new        = iterate (processAdt ac)
        --_             = printsym (quote "New AC Adt: ")
        --_             = printsym (quote "NEWLINE")
        --_             = printAdt ac_new
        --_             = printsym (quote "NEWLINE")
        
    in ()
