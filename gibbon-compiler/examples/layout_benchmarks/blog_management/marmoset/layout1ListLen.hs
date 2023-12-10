type Text = Vector Char

data Content =   Str Text Content
               | End

data List =   Snoc (List) Content
            | Nil


mkContent :: Int -> Content
mkContent len = if len <= 0 then End
                            else Str "abcdef" (mkContent (len - 1))


mkSnocList :: Int -> List
mkSnocList len = if len <= 0
                 then Nil
                 else let
                          rst = mkSnocList (len - 1)
                          val = mkContent 100
                       in Snoc rst val

getLengthSnoc :: List -> Int
{-# ANN getLengthSnoc Snoc #-}
getLengthSnoc lst = case lst of
                        Snoc rst val -> 1 + getLengthSnoc rst
                        Nil          -> 0


gibbon_main =
        let snocList = mkSnocList 1000000
            --consList = mkConsList 100000
            l1       = iterate (getLengthSnoc snocList)
            --l2       = getLengthCons consList
            _        = printsym (quote "Length Snoc: ")
            _        = printint l1
            _        = printsym (quote "NEWLINE")
            --_        = printsym (quote "Length Cons: ")
            --_        = printint l2
            --_        = printsym (quote "NEWLINE")
         in ()
