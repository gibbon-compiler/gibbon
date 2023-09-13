module Main where

import Strings
import Contents
import Adts
import Tags
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             ACT rst content tags -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in ACT newRst (copyPacked content) (copyPacked newTags)


-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let act = mkACTList 100 10 20
        add_act    = addValTagsAdt act
    in lengthAdt add_act == lengthAdt act
