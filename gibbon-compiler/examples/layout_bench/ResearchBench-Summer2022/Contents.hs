module Contents where

import Strings

-- A datatype for Content
-- Content can be either an Image represented by String or Text represented by String, for now atleast

data Content  = Image String | Text String

 
-- make Image tail rec
mkContentImageTR :: Int -> Content
mkContentImageTR n = Image (mkStringTR n End)
                 
             
-- make Text tail rc   
mkContentTextTR :: Int -> Content
mkContentTextTR n = Text (mkStringTR n End)

-- make Image
mkContentImage :: Int -> Content
mkContentImage n = Image (mkString n)
                 
             
-- make Text             
mkContentText :: Int -> Content
mkContentText n = Text (mkString n)

-- process content, not dependent on the data layout so okay to make this common. 
processContent :: Content -> Content
processContent content = case content of 
                              Image x -> Image (processString x)
                              Text  y -> Text  (processString y)

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
