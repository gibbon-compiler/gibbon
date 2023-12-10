type Text = Vector Char

data Content = Str Text Content
             | End

data List = Cons Content (List)
          | Nil


mkContent :: Int -> Content
mkContent len = if len <= 0 then End
                            else Str "abcdef" (mkContent (len - 1))


mkConsList :: Int -> List
mkConsList len = if len <= 0
                 then Nil
                 else let
                          --val = mkContent 100
			  rst = mkConsList (len - 1)
                          val = mkContent 100
                        in Cons val rst

getLengthCons :: List -> Int
{-# ANN getLengthCons Cons #-}
getLengthCons lst = case lst of
                        Cons val rst ->  getLengthCons rst + 1
                        Nil          -> 0



gibbon_main =
        let --snocList = mkSnocList 90000
            consList = mkConsList 3000000
            --l1       = getLengthSnoc snocList
            l2       = iterate (getLengthCons consList)
            --_        = printsym (quote "Length Snoc: ")
            --_        = printint l1
            --_        = printsym (quote "NEWLINE")
            _        = printsym (quote "Length Cons: ")
            _        = printint l2
            _        = printsym (quote "NEWLINE")
         in ()
