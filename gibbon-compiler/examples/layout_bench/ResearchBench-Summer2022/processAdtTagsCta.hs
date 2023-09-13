module Main where

import Strings
import Contents
import Adts
import Tags
                                                     
                                                     
addValTagsAdt :: Adt ->  Adt
addValTagsAdt adt = case adt of
                             Nil -> Nil
                             CTA content tags rst -> let newTags = addValTag tags 10
                                                         newRst  = addValTagsAdt rst
                                                     in CTA content newTags newRst
                                                     

-- mk for 3 parameter Adt take, len, tagLen, strLen
gibbon_main =
    let cta = mkCTAList 100 10 20
        add_cta    = addValTagsAdt cta 
    in lengthAdt add_cta == lengthAdt cta
