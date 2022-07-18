module Main where

import Strings
import Contents
import Adts
import Tags
 
-- searchTagsAdt :: Adt -> Tags -> Adt
-- searchTagsAdt adt tag = case adt of
--                              Nil -> Nil
--                              ACT rst content tags -> let present = searchTag tag tags
--                                                          newRst  = searchTagsAdt rst tag
--                                                      in if (present) then ACT newRst ( copyPacked content) tags else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             ACT rst content tags -> let newTags = addValTag tags 10
                                                         newRst  = addValTagsAdt rst 
                                                     in ACT newRst ( copyPacked content) ( copyPacked newTags)


-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let act = mkACTList 100000 10 2000
        -- _             = printsym (quote "ACT Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked act
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_act    = iterate (searchTagsAdt act tag)
        -- _             = printsym (quote "ACT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_act
        -- _             = printsym (quote "NEWLINE")
        -- _             = printsym (quote "==============================================================================================================================")
        -- _             = printsym (quote "NEWLINE")
        add_act    = iterate (addValTagsAdt act)
        -- _             = printsym (quote "ACT Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_act
        -- _             = printsym (quote "NEWLINE")
    in ()
