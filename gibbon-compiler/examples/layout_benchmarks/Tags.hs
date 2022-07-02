module Tags where

data Tags = Nul | Tag Int (Tags)

searchTag :: Tags -> Tags -> Bool
searchTag tag tagList = case tag of
                              Nul -> case tagList of
                                          Nul         -> True
                                          Tag val rst -> False
                              Tag val rst -> case tagList of
                                                  Nul  -> False
                                                  Tag val' rst' -> if (val == val') then True else (False || searchTag tag rst')
                                                  
                                  
add1Tag :: Tags -> Tags
add1Tag tags = case tags of 
                    Nul -> Nul
                    Tag val rst -> Tag (val+1) (add1Tag rst)
                                                  
countTags :: Tags -> Int
countTags tags = case tags of 
                      Nul -> 0
                      Tag val rst -> 1 + countTags rst
                      
                      
sumTags :: Tags -> Int
sumTags tags = case tags of 
                    Nul -> 0
                    Tag val rst -> val + sumTags rst
                    
mkRandomTags :: Int -> Tags
mkRandomTags len = if (len <= 0)
                      then Nul
                      else let
                               val = 100 --mod rand 1000
                               rst = mkRandomTags (len-1)
                           in Tag val rst
                           
printTags :: Tags -> ()
printTags tags =
    case tags of
        Nul ->
            let _ = printsym (quote "Nul")
                _ = printsym (quote "SPACE")
            in ()
        Tag val rst ->
            let _ = printsym (quote "(Tag ")
                _ = printint val
                _ = printsym (quote "SPACE")
                _ = printTags rst
                _ = printsym (quote ")")
                _ = printsym (quote "SPACE")
            in ()
