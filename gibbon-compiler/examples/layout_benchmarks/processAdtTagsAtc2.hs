module Main where

import Strings
import Contents
import Adts
import Tags
 
-- searchTagsAdt :: Adt -> Tags -> Adt
-- searchTagsAdt adt tag = case adt of
--                              Nil -> Nil
--                              ATC rst tags content -> let present = searchTag tag tags
--                                                          newRst  = searchTagsAdt rst tag
--                                                      in if (present) then ATC newRst ( copyPacked tags ) content else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             ATC rst tags content -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in ATC newRst (newTags) content
                                                    


-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let atc = mkATCList 100000 10 2000
        -- _             = printsym (quote "ATC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked atc
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_atc    = iterate (searchTagsAdt atc tag)
        -- _             = printsym (quote "ATC Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_atc
        -- _             = printsym (quote "NEWLINE")
        -- _             = printsym (quote "==============================================================================================================================")
        -- _             = printsym (quote "NEWLINE")
        add_atc    = iterate (addValTagsAdt atc)
        -- _             = printsym (quote "ATC Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_atc
        -- _             = printsym (quote "NEWLINE")
    in ()
