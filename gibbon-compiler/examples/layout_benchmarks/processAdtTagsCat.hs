module Main where

import Strings
import Contents
import Adts
import Tags
 
searchTagsAdt :: Adt -> Tags -> Adt
searchTagsAdt adt tag = case adt of
                             Nil -> Nil
                             CAT content rst tags -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then CAT content newRst tags else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             CAT content rst tags -> let newTags = addValTag tags 10
                                                         newRst  = addValTagsAdt rst 
                                                     in CAT content newRst ( copyPacked newTags)

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let cat = mkCATList 100000 10 2000
        -- _             = printsym (quote "CAT Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked cat
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_cat    = iterate (searchTagsAdt cat tag) 
        -- _             = printsym (quote "CAT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_cat
        -- _             = printsym (quote "NEWLINE")
        -- _             = printsym (quote "==============================================================================================================================")
        -- _             = printsym (quote "NEWLINE")
        add_cat       = iterate (addValTagsAdt cat)
        -- _             = printsym (quote "CAT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_cat
        -- _             = printsym (quote "NEWLINE")
    in ()
