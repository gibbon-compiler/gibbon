module Contents where

import Strings

-- A datatype for Content
-- Content can be either an Image represented by String or Text represented by String, for now atleast

data Content  = Image String | Text String

 
-- make Image
mkContentImage :: Int -> Content
mkContentImage n = Image (mkString n)
                 
             
-- make Text             
mkContentText :: Int -> Content
mkContentText n = Text (mkString n)


printContent :: Content -> ()
printContent content = 
    case content of 
        Text n -> 
            let _ = printsym (quote "Text ")
                _ = printString n
            in ()
        Image n ->
            let _ = printsym (quote "Image ")
                _ = printString n
            in ()
