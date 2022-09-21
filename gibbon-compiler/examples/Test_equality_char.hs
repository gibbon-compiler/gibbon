module Test_equality_char where

head :: Vector Char -> Char
head vec = vnth vec 0

gibbon_main = 
    let a :: Vector Char 
        b :: Vector Char 
        a     = "G"
        b     = "G"
        _     = printsym (quote "Print output when we compare same characters: ")
        equal = ((head a) *==* (head b))
        _     = printbool equal
        _     = printsym (quote "NEWLINE")
        b     = "A"
        _     = printsym (quote "Print output when we compare dissimilar characters: ")
        noeq  = ((head a) *==* (head b))
        _     = printbool noeq
        _     = printsym (quote "NEWLINE")
    in ()
