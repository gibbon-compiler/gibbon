module Main where

import Strings
import Contents
import Adts
import Tags
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             ATC rst tags content -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in ATC newRst (newTags) content
                                                    


-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let atc = mkATCList 100 10 0
        add_atc    = addValTagsAdt atc
    in lengthAdt add_atc == lengthAdt atc
