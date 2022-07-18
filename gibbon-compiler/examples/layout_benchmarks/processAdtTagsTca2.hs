module Main where

import Strings
import Contents
import Adts
import Tags
 
-- searchTagsAdt :: Adt -> Tags -> Adt
-- searchTagsAdt adt tag = case adt of
--                              Nil -> Nil
--                              TCA tags content rst -> let present = searchTag tag tags
--                                                          newRst  = searchTagsAdt rst tag
--                                                      in if (present) then TCA tags content newRst else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             TCA tags content rst -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in TCA newTags ( copyPacked content) ( copyPacked newRst)

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let tca = mkTCAList 100000 10 2000
        -- _             = printsym (quote "TCA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked tca
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_tca    = iterate (searchTagsAdt tca tag)
        -- _             = printsym (quote "TCA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_tca
        -- _             = printsym (quote "NEWLINE")
        -- _             = printsym (quote "==============================================================================================================================")
        -- _             = printsym (quote "NEWLINE")
        add_tca    = iterate (addValTagsAdt tca)
        -- _             = printsym (quote "TCA Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_tca
        -- _             = printsym (quote "NEWLINE")
    in ()
