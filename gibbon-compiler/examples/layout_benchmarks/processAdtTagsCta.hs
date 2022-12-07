module Main where

import Strings
import Contents
import Adts
import Tags
 
-- searchTagsAdt :: Adt -> Tags -> Adt
-- searchTagsAdt adt tag = case adt of
--                              Nil -> Nil
--                              CTA content tags rst -> let present = searchTag tag tags
--                                                          newRst  = searchTagsAdt rst tag
--                                                      in if (present) then CTA content tags newRst else newRst
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             CTA content tags rst -> let newTags = addValTag tags 10
                                                         newRst  = addValTagsAdt rst
                                                     in CTA content newTags newRst
                                                     
{-
sumTagsAdt :: Adt -> Tags -> Adt
sumTagsAdt adt tag = case adt of
                             Nil -> Nil
                             TCA tags content rst -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then TCA tags content newRst else newRst
                             ACT rst content tags -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then ACT newRst content tags else newRst
                             TAC tags rst content -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then TAC tags newRst content else newRst
                             ATC rst tags content -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then ATC newRst tags content else newRst
                             CTA content tags rst -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then CTA content tags newRst else newRst-}

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let cta = mkCTAList 100000 10 2000
        -- _             = printsym (quote "CTA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked cta
        -- _             = printsym (quote "NEWLINE")
        --tag = Tag 1000000 Nul        
        --search_cta    = iterate (searchTagsAdt cta tag) 
        -- _             = printsym (quote "CTA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_cta
        -- _             = printsym (quote "NEWLINE")
        --_             = printsym (quote "==============================================================================================================================")
        --_             = printsym (quote "NEWLINE")
        add_cta    = iterate (addValTagsAdt cta) 
        -- _             = printsym (quote "CTA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_cta
        -- _             = printsym (quote "NEWLINE")
    in ()
