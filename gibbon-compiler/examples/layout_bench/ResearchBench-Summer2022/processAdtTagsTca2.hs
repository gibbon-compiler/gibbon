module Main where

import Strings
import Contents
import Adts
import Tags
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             TCA tags content rst -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in TCA newTags ( copyPacked content) ( copyPacked newRst)

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let tca = mkTCAList 100 10 20
        add_tca    = addValTagsAdt tca
    in lengthAdt add_tca == lengthAdt tca
