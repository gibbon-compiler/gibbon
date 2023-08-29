module Adts where

import Strings
import Contents
import Tags
 

data Adt = Nil | CA (Content) (Adt) | AC (Adt) (Content) | TCA (Tags) (Content) (Adt) | ACT (Adt) (Content) (Tags) | TAC (Tags) (Adt) (Content) | ATC (Adt) (Tags) (Content) | CTA (Content) (Tags) (Adt) | CAT (Content) (Adt) (Tags)
    deriving (Show)


-- make list for adt CA Tail recursive
mkCAListTR :: Int -> Int -> Adt -> Adt
mkCAListTR len strLen accumulator = if len <= 0
                  then accumulator
                  else
                    let content = mkContentTextTR strLen
                        append  = CA content accumulator
                    in mkCAListTR (len-1) strLen append

-- make list for adt CA non-tail recursive
mkCAList :: Int -> Int -> Adt
mkCAList len strLen = if len <= 0
                  then Nil 
                  else
                    let content = mkContentText strLen
                        rst     = mkCAList (len-1) strLen
                    in CA content rst                    
                    

-- make list for adt AC
mkACList :: Int -> Int -> Adt
mkACList len strLen = if len <= 0
                  then Nil 
                  else
                    let rst = mkACList (len-1) strLen
                        content = mkContentText strLen
                    in AC rst content 
                    
mkTCAList :: Int -> Int -> Int -> Adt
mkTCAList len tagLen strLen = if (len <= 0)
                                  then Nil
                                  else let
                                           tags    = mkRandomTags tagLen
                                           content = mkContentText strLen
                                           rst     = mkTCAList (len-1) tagLen strLen
                                       in TCA tags content rst
                                       
mkACTList :: Int -> Int -> Int -> Adt
mkACTList len tagLen strLen = if (len <= 0)
                                  then Nil
                                  else let rst     = mkACTList (len-1) tagLen strLen
                                           content = mkContentText strLen
                                           tags    = mkRandomTags tagLen
                                       in ACT rst content tags
                                       
                                       
mkTACList :: Int -> Int -> Int -> Adt
mkTACList len tagLen strLen = if (len <= 0)
                                  then Nil
                                  else let tags    = mkRandomTags tagLen
                                           rst     = mkTACList (len-1) tagLen strLen
                                           content = mkContentText strLen
                                       in TAC tags rst content
                                       
                                       
mkATCList :: Int -> Int -> Int -> Adt
mkATCList len tagLen strLen = if (len <= 0)
                                  then Nil
                                  else let rst     = mkATCList (len-1) tagLen strLen
                                           tags    = mkRandomTags tagLen
                                           content = mkContentText strLen
                                       in ATC rst tags content
                                       
mkCTAList :: Int -> Int -> Int -> Adt
mkCTAList len tagLen strLen = if (len <= 0)
                                  then Nil
                                  else let content = mkContentText strLen
                                           tags    = mkRandomTags tagLen
                                           rst     = mkCTAList (len-1) tagLen strLen                                   
                                       in CTA content tags rst
                    
mkCATList :: Int -> Int -> Int -> Adt 
mkCATList len tagLen strLen = if (len <= 0)
                                    then Nil
                                    else let content = mkContentText strLen
                                             rst     = mkCATList (len-1) tagLen strLen 
                                             tags    = mkRandomTags tagLen 
                                         in CAT content rst tags
                    
printAdt :: Adt -> ()
printAdt adt =
  case adt of
    Nil -> 
        let _ = printsym (quote "Nil")
            _ = printsym (quote "SPACE")
        in ()
    CA a rst ->
      let _ = printsym (quote "(CA ")
          _ = printContent a
          _ = printsym (quote "SPACE")
          _ = printAdt rst
          _ = printsym (quote ")")
          _ = printsym (quote "SPACE")
      in ()
    AC rst a -> 
        let _ = printsym (quote "(AC ")
            _ = printAdt rst
            _ = printContent a
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    TCA tags content rst -> 
        let _ = printsym (quote "(TCA ")
            _ = printTags tags
            _ = printContent content
            _ = printAdt rst
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    ACT rst content tags -> 
        let _ = printsym (quote "(ACT ")
            _ = printAdt rst
            _ = printContent content
            _ = printTags tags
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    TAC tags rst content -> 
        let _ = printsym (quote "(TAC ")
            _ = printTags tags
            _ = printAdt rst
            _ = printContent content
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    ATC rst tags content -> 
        let _ = printsym (quote "(ATC ")
            _ = printAdt rst
            _ = printTags tags
            _ = printContent content
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    CTA content tags rst -> 
        let _ = printsym (quote "(CTA ")
            _ = printContent content
            _ = printTags tags
            _ = printAdt rst
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
    CAT content rst tags ->
        let _ = printsym (quote "(CAT ")
            _ = printContent content
            _ = printAdt rst
            _ = printTags tags
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")          
        in ()
    
lengthAdt :: Adt -> Int
lengthAdt adt =
  case adt of
    Nil -> 0 
    CA a rst -> 1 + lengthAdt rst
    AC rst a -> 1 + lengthAdt rst
    TCA tags content rst -> 1 + lengthAdt rst
    ACT rst content tags -> 1 + lengthAdt rst
    TAC tags rst content -> 1 + lengthAdt rst
    ATC rst tags content -> 1 + lengthAdt rst
    CTA content tags rst -> 1 + lengthAdt rst
    CAT content rst tags -> 1 + lengthAdt rst
        
