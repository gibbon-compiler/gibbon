module Main where

import Strings
import Contents
import Adts
import Tags
 
                                                  
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             TAC tags rst content -> let newRst  = addValTagsAdt rst
                                                         newTags = addValTag tags 10 
                                                     in TAC newTags (copyPacked newRst) content

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let tac = mkTACList 100 10 20
        add_tac    = addValTagsAdt tac
    in lengthAdt add_tac == lengthAdt tac
