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
                             CAT content rst tags -> let present = searchTag tag tags
                                                         newRst  = searchTagsAdt rst tag
                                                     in if (present) then CAT content newRst tags else newRst
                                                     
                                                     
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
                             CAT content rst tags -> let newTags = add1Tag tags
                                                         newRst  = add1TagsAdt rst 
                                                     in CAT content newRst ( copyPacked newTags)
                                                     
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
    let tca = mkTCAList 100000 10 20000 
        -- _             = printsym (quote "TCA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked tca
        -- _             = printsym (quote "NEWLINE")
        act = mkACTList 100000 10 20000  
        -- _             = printsym (quote "ACT Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked act
        -- _             = printsym (quote "NEWLINE")
        tac = mkTACList 100000 10 20000 
        -- _             = printsym (quote "TAC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked tac
        -- _             = printsym (quote "NEWLINE")
        atc = mkATCList 100000 10 20000 
        -- _             = printsym (quote "ATC Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked atc
        -- _             = printsym (quote "NEWLINE")
        cta = mkCTAList 100000 10 20000
        -- _             = printsym (quote "CTA Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked cta
        -- _             = printsym (quote "NEWLINE")
        cat = mkCATList 100000 10 20000
        -- _             = printsym (quote "CAT Adt: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked cat
        -- _             = printsym (quote "NEWLINE")
        tag = Tag 1000000 Nul        
        search_tca    = iterate (searchTagsAdt tca tag)
        -- _             = printsym (quote "TCA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_tca
        -- _             = printsym (quote "NEWLINE")
        search_act    = iterate (searchTagsAdt act tag)
        -- _             = printsym (quote "ACT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_act
        -- _             = printsym (quote "NEWLINE")
        search_tac    = iterate (searchTagsAdt tac tag)
        -- _             = printsym (quote "TAC Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_tac
        -- _             = printsym (quote "NEWLINE")
        search_atc    = iterate (searchTagsAdt atc tag)
        -- _             = printsym (quote "ATC Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_atc
        -- _             = printsym (quote "NEWLINE")
        search_cta    = iterate (searchTagsAdt cta tag) 
        -- _             = printsym (quote "CTA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_cta
        -- _             = printsym (quote "NEWLINE")
        search_cat    = iterate (searchTagsAdt cat tag) 
        -- _             = printsym (quote "CAT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked search_cat
        -- _             = printsym (quote "NEWLINE")
        _             = printsym (quote "==============================================================================================================================")
        _             = printsym (quote "NEWLINE")
        add_tca    = iterate (add1TagsAdt tca)
        -- _             = printsym (quote "TCA Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_tca
        -- _             = printsym (quote "NEWLINE")
        add_act    = iterate (add1TagsAdt act)
        -- _             = printsym (quote "ACT Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_act
        -- _             = printsym (quote "NEWLINE")
        add_tac    = iterate (add1TagsAdt tac)
        -- _             = printsym (quote "TAC Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_tac
        -- _             = printsym (quote "NEWLINE")
        add_atc    = iterate (add1TagsAdt atc)
        -- _             = printsym (quote "ATC Adt after add tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_atc
        -- _             = printsym (quote "NEWLINE")
        add_cta    = iterate (add1TagsAdt cta) 
        -- _             = printsym (quote "CTA Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_cta
        -- _             = printsym (quote "NEWLINE")
        add_cat       = iterate (add1TagsAdt cat)
        -- _             = printsym (quote "CAT Adt after search tags: ")
        -- _             = printsym (quote "NEWLINE")
        -- _             = printPacked add_cat
        -- _             = printsym (quote "NEWLINE")
    in ()
