module TestMaybe where

import Gibbon.Prelude 
import Gibbon.Maybe 




gibbon_main = 
   let val :: Maybe Int 
       val = Just 10 
       tell_just = isJust val
       tell_not  = isNothing val 
       _ = printsym ( quote "is val just: " )
       _ = printsym ( quote "NEWLINE" )  
       _ = printbool tell_just 
       _ = printsym ( quote "NEWLINE" )
       _ = printsym ( quote "is val nothing: " )
       _ = printsym ( quote "NEWLINE" )
       _ = printbool tell_not 
       _ = printsym ( quote "NEWLINE" )
    in ()

