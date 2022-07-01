module Adts where

import Strings
import Contents


data Adt = Nil | CA (Content) (Adt) | AC (Adt) (Content)


-- make list for adt CA
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
