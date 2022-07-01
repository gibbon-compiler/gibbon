module Main where

import Strings
import Contents
import Adts
import Tags

searchTagsAdt :: Adt -> Tags -> Adt
searchTagsAdt adt tag = case adt of
                             Nil -> Nil
                             TCA tags content rst -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then TCA tags content newRst else newRst
                             ACT rst content tags -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then ACT newRst ( copyPacked content) tags else newRst
                             TAC tags rst content -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then TAC tags newRst content else newRst
                             ATC rst tags content -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then ATC newRst ( copyPacked tags ) content else newRst
                             CTA content tags rst -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then CTA content tags newRst else newRst
                                                     
                                                     
add1TagsAdt :: Adt ->  Adt
add1TagsAdt adt = case adt of
                             Nil -> Nil
                             TCA tags content rst -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
                                                     in TCA newTags ( copyPacked content) ( copyPacked newRst)
                             ACT rst content tags -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
                                                     in ACT newRst ( copyPacked content) ( copyPacked newTags)
                             TAC tags rst content -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
                                                     in TAC newTags newRst content
                             ATC rst tags content -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
                                                     in ATC newRst ( copyPacked newTags ) content
                             CTA content tags rst -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
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
    let tca = mkTCAList 1000 10 10000 
--         _             = printsym (quote "TCA Adt: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt tca
--         _             = printsym (quote "NEWLINE")
        act = mkACTList 1000 10 10000 
--         _             = printsym (quote "ACT Adt: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt act
--         _             = printsym (quote "NEWLINE")
        tac = mkTACList 1000 10 10000 
--         _             = printsym (quote "TAC Adt: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt tac
--         _             = printsym (quote "NEWLINE")
        atc = mkATCList 1000 10 10000 
--         _             = printsym (quote "ATC Adt: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt atc
--         _             = printsym (quote "NEWLINE")
        cta = mkCTAList 1000 10 10000 
--         _             = printsym (quote "CTA Adt: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt cta
--         _             = printsym (quote "NEWLINE")
        tag           = Tag 1000000 Nul        
--        search_tca    = iterate (searchTagsAdt tca tag)
--         _             = printsym (quote "TCA Adt after search tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt search_tca
--         _             = printsym (quote "NEWLINE")
--        search_act    = iterate (searchTagsAdt act tag)
--         _             = printsym (quote "ACT Adt after search tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt search_act
--         _             = printsym (quote "NEWLINE")
--        search_tac    = iterate (searchTagsAdt tac tag)
--         _             = printsym (quote "TAC Adt after search tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt search_tac
--         _             = printsym (quote "NEWLINE")
--        search_atc    = iterate (searchTagsAdt atc tag)
--         _             = printsym (quote "ATC Adt after search tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt search_atc
--         _             = printsym (quote "NEWLINE")
--        search_cta    = iterate (searchTagsAdt cta tag) 
--         _             = printsym (quote "CTA Adt after search tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt search_cta
--         _             = printsym (quote "NEWLINE")   

        add_tca    = iterate (add1TagsAdt tca)
--         _             = printsym (quote "TCA Adt after add tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt add_tca
--         _             = printsym (quote "NEWLINE")
        add_act    = iterate (add1TagsAdt act)
--         _             = printsym (quote "ACT Adt after add tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt add_act
--         _             = printsym (quote "NEWLINE")
        add_tac    = iterate (add1TagsAdt tac)
--         _             = printsym (quote "TAC Adt after add tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt add_tac
--         _             = printsym (quote "NEWLINE")
        add_atc    = iterate (add1TagsAdt atc)
--         _             = printsym (quote "ATC Adt after add tags: ")
--         _             = printsym (quote "NEWLINE")
--         _             = printAdt add_atc
--         _             = printsym (quote "NEWLINE")
        add_cta    = iterate (add1TagsAdt cta) 
      {-  _             = printsym (quote "CTA Adt after search tags: ")
        _             = printsym (quote "NEWLINE")
        _             = printAdt add_cta
        _             = printsym (quote "NEWLINE")     -}   
    in ()
