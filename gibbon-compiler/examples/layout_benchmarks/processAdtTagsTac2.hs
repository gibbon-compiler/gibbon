module Main where

import Strings
import Contents
import Adts
import Tags
 
-- searchTagsAdt :: Adt -> Tags -> Adt
-- searchTagsAdt adt tag = case adt of
--                              Nil -> Nil
--                              TAC tags rst content -> let present = searchTag tag tags
--                                                          newRst  = searchTagsAdt rst tag
--                                                      in if (present) then TAC tags newRst content else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             TAC tags rst content -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in TAC newTags (copyPacked newRst) content

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let tac = mkTACList 100000 10 2000
        -- _             = printsym (quote "TAC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked tac
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_tac    = iterate (searchTagsAdt tac tag)
        -- _             = printsym (quote "TAC Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_tac
        -- _             = printsym (quote "NEWLINE")
        --_             = printsym (quote "==============================================================================================================================")
        --_             = printsym (quote "NEWLINE")
        add_tac    = iterate (addValTagsAdt tac)
        -- _             = printsym (quote "TAC Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_tac
        -- _             = printsym (quote "NEWLINE")
    in ()
