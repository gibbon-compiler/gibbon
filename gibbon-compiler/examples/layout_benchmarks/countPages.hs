module Main where

data Content  = Image Int | Text Int
data PageList = Nil  | Cons (Content) (PageList) | Snoc (PageList) (Content) deriving (Show)


countPages :: PageList -> Int
countPages pageList = case pageList of 
                            Nil                    -> 0
                            Cons content nextPage  -> 1 + countPages nextPage
                            Snoc nextPage content  -> 1 + countPages nextPage                            
                            
mkContent :: Int -> Content
mkContent n = if (mod n 2 == 0)
                 then Image n
                 else Text  n
                            
mkConsList :: Int -> PageList
mkConsList numPages = if numPages <= 0 
                         then Nil
                         else 
                            let content = mkContent numPages 
                                rst     = (mkConsList (numPages - 1))                                
                            in Cons content rst


mkSnocList :: Int -> PageList
mkSnocList numPages = if numPages <= 0 
                         then Nil
                         else 
                            let rst = (mkSnocList (numPages-1))
                                content = mkContent numPages
                            in Snoc rst content

                            
printContent :: Content -> ()
printContent content = 
    case content of 
        Text n -> 
            let _ = printsym (quote "Text ")
                _ = printint n
            in ()
        Image n ->
            let _ = printsym (quote "Image ")
                _ = printint n
            in ()
                            
                            
printSyms :: PageList -> ()
printSyms lst =
  case lst of
    Nil -> 
        let _ = printsym (quote "Nil")
            _ = printsym (quote "SPACE")
        in ()
    Cons a rst ->
      let _ = printsym (quote "(Cons ")
          _ = printContent a
          _ = printsym (quote "SPACE")
          _ = printSyms rst
          _ = printsym (quote ")")
          _ = printsym (quote "SPACE")
      in ()
    Snoc rst a -> 
        let _ = printsym (quote "(Snoc ")
            _ = printSyms rst
            _ = printContent a
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
                           
gibbon_main = 
    let list1 = mkConsList 100
        list2 = mkSnocList 100
        _     = printSyms list1
        _     = printsym (quote "NEWLINE")
        _     = printSyms list2
        _     = printsym (quote "NEWLINE")
        count1 = timeit (countPages list1)
        count2 = timeit (countPages list2)
    in ()
