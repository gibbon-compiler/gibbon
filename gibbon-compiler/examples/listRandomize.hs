module Main where

{- Defining List type. -}

data List = Nil | Cons Int (List) | Snoc (List) Int deriving (Show)


randomizeList :: List -> List
randomizeList list = case list of
                      Nil-> Nil
                      Cons a rst -> if (mod rand 2 == 0)
                                       then Cons a (randomizeList rst) 
                                       else Snoc (randomizeList rst) a
                      Snoc rst a -> if (mod rand 2 == 0)
                                       then Cons a (randomizeList rst)
                                       else Snoc (randomizeList rst) a

mkList :: Int -> List
mkList len = 
    if len <= 0
       then Nil
       else
            let rst = (mkList (len - 1)) 
            in Cons len rst
            
sumList :: List -> Int
sumList list = case list of 
                    Nil -> 0
                    Cons a rst -> a + (sumList rst)
                    Snoc rst a -> (sumList rst) + a
                    
printSyms :: List -> ()
printSyms lst =
  case lst of
    Nil -> 
        let _ = printsym (quote "Nil")
            _ = printsym (quote "SPACE")
        in ()
    Cons a rst ->
      let _ = printsym (quote "(Cons ")
          _ = printint a
          _ = printsym (quote "SPACE")
          _ = printSyms rst
          _ = printsym (quote ")")
          _ = printsym (quote "SPACE")
      in ()
    Snoc rst a -> 
        let _ = printsym (quote "(Snoc ")
            _ = printSyms rst
            _ = printint a
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()
                    
gibbon_main = 
    let step1 = printsym (quote "--- Start of Program ---\n")
        step2 = printsym (quote "--- Print the original List ---\n")
        step3 = printSyms (mkList 100)
        step4 = printsym (quote "NEWLINE")
        step5 = printsym (quote "--- Print the random List ---\n")
        step6 = printSyms (randomizeList (mkList 100))
        step7 = printsym (quote "NEWLINE")
        step8 = printsym (quote "--- End of Program ---\n")
    in ()
