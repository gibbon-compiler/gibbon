module Main where

import Strings
import Contents
import Adts
import Tags
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             CAT content rst tags -> let newRst  = addValTagsAdt rst 
                                                         newTags = addValTag tags 10
                                                     in CAT content newRst (newTags)

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let cat = mkCATList 100 10 20
        add_cat       = addValTagsAdt cat
    in lengthAdt add_cat == lengthAdt cat
