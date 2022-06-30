module Main where

data PageList = Nil | Cons (Content) (PageList) | Snoc (PageList) (Content) deriving (Show)
data String   = End | C Int (String)
data Content  = Image String | Text String

asciiInvertPageList :: PageList -> PageList
asciiInvertPageList list = case list of 
    Nil -> Nil
    Cons a rst -> 
        let newCont = takeAsciiInverseContent a
            newRst  = asciiInvertPageList rst 
        in Cons newCont newRst
    Snoc rst a ->
        let newRst  = asciiInvertPageList rst
            newCont = takeAsciiInverseContent a            
        in Snoc newRst newCont

takeAsciiInverseContent :: Content -> Content
takeAsciiInverseContent content = case content of 
    Image x -> Image (takeAsciiInverseString x) 
    Text  y -> Text  (takeAsciiInverseString y)

takeAsciiInverseString :: String -> String
takeAsciiInverseString string = case string of 
    End -> End
    C val rst -> let newVal = 0
                     --addVal = newVal + 10
                     --mulVal = addVal * 10
                     --divVal = mulVal / 5
                     --modVal = mod divVal 128
                 in C newVal (takeAsciiInverseString rst)
                 
                 
-- make String type of a random length
-- set max value to 128, using mod function to emulate ascii table                            
mkString :: Int -> String
mkString len = if len <= 0
                    then End
                    else 
                        let randomChar = mod 1234 128
                            rst = mkString (len - 1)
                        in C randomChar rst

-- make a Snoc style page list with random text
mkSnocRandomTextPageList :: Int -> Int -> PageList
mkSnocRandomTextPageList len strSize = if len <= 0
                                          then Nil 
                                          else
                                            let rst     = mkSnocRandomTextPageList (len-1) strSize
                                                text    = mkString strSize
                                                content = Text text
                                            in Snoc rst content   

-- make a Cons style page list with random text
mkConsRandomTextPageList :: Int -> Int -> PageList
mkConsRandomTextPageList len strSize = if len <= 0
                                         then Nil 
                                         else
                                           let text    = mkString strSize
                                               content = Text text
                                               rst     = mkConsRandomTextPageList (len-1) strSize
                                           in Cons content rst



loop :: (PageList -> PageList) -> PageList -> Int -> PageList
loop function list iters = if iters <= 0 
                                then list
                                else
                                    let newList = function list 
                                    in loop function list (iters - 1)
                                    

-----------Print utilities, print ascii, print string, print content, print pagelist -----------------------------------

printAscii :: Int -> ()
printAscii decimal =  
        if decimal == 0 then
            let _ = printsym (quote "NUL")
            in ()
        else if decimal == 1 then
            let _ = printsym (quote "SOH")
            in ()
        else if decimal == 2 then
            let _ = printsym (quote "STX")
            in ()
        else if decimal == 3 then
            let _ = printsym (quote "ETX")
            in ()
        else if decimal == 4 then
            let _ = printsym (quote "EOT")
            in ()
        else if decimal == 5 then
            let _ = printsym (quote "ENQ")
            in ()
        else if decimal == 6 then
            let _ = printsym (quote "ACK")
            in ()
        else if decimal == 7 then
            let _ = printsym (quote "BEL")
            in ()
        else if decimal == 8 then
            let _ = printsym (quote "BS")
            in ()
        else if decimal == 9 then
            let _ = printsym (quote "TAB")
            in ()
        else if decimal == 10 then
            let _ = printsym (quote "LF")
            in ()
        else if decimal == 11 then
            let _ = printsym (quote "VT")
            in ()
        else if decimal == 12 then
            let _ = printsym (quote "FF")
            in ()
        else if decimal == 13 then
            let _ = printsym (quote "CR")
            in ()
        else if decimal == 14 then
            let _ = printsym (quote "SO")
            in ()
        else if decimal == 15 then
            let _ = printsym (quote "SI")
            in ()
        else if decimal == 16 then
            let _ = printsym (quote "DLE")
            in ()
        else if decimal == 17 then
            let _ = printsym (quote "DCI")
            in ()
        else if decimal == 18 then
            let _ = printsym (quote "DC2")
            in ()
        else if decimal == 19 then
            let _ = printsym (quote "DC3")
            in ()    
        else if decimal == 20 then
            let _ = printsym (quote "DC4")
            in ()
        else if decimal == 21 then
            let _ = printsym (quote "NAK")
            in ()
        else if decimal == 22 then
            let _ = printsym (quote "SYN")
            in ()
        else if decimal == 23 then
            let _ = printsym (quote "ETB")
            in ()
        else if decimal == 24 then
            let _ = printsym (quote "CAN")
            in ()
        else if decimal == 25 then
            let _ = printsym (quote "EM")
            in ()
        else if decimal == 26 then
            let _ = printsym (quote "SUB")
            in ()
        else if decimal == 27 then
            let _ = printsym (quote "ESC")
            in ()
        else if decimal == 28 then
            let _ = printsym (quote "FS")
            in ()
        else if decimal == 29 then
            let _ = printsym (quote "GS")
            in ()
        else if decimal == 30 then
            let _ = printsym (quote "RS")
            in ()
        else if decimal == 31 then
            let _ = printsym (quote "US")
            in ()
        else if decimal == 32 then
            let _ = printsym (quote "SPACE")
            in ()
        else if decimal == 33 then
            let _ = printsym (quote "!")
            in ()
        else if decimal == 34 then
            let _ = printsym (quote "\"")
            in ()
        else if decimal == 35 then
            let _ = printsym (quote "#")
            in ()
        else if decimal == 36 then
            let _ = printsym (quote "$")
            in ()
        else if decimal == 37 then
            let _ = printsym (quote "%")
            in ()
        else if decimal == 38 then
            let _ = printsym (quote "&")
            in ()
        else if decimal == 39 then
            let _ = printsym (quote "'")
            in ()
        else if decimal == 40 then
            let _ = printsym (quote "(")
            in ()
        else if decimal == 41 then
            let _ = printsym (quote ")")
            in ()
        else if decimal == 42 then
            let _ = printsym (quote "*")
            in ()
        else if decimal == 43 then
            let _ = printsym (quote "+")
            in ()
        else if decimal == 44 then
            let _ = printsym (quote ",")
            in ()
        else if decimal == 45 then
            let _ = printsym (quote "-")
            in ()
        else if decimal == 46 then
            let _ = printsym (quote ".")
            in ()
        else if decimal == 47 then
            let _ = printsym (quote "/")
            in ()
        else if decimal == 48 then
            let _ = printsym (quote "0")
            in ()
        else if decimal == 49 then
            let _ = printsym (quote "1")
            in ()             
        else if decimal == 50 then
            let _ = printsym (quote "2")
            in ()
        else if decimal == 51 then
            let _ = printsym (quote "3")
            in ()
        else if decimal == 52 then
            let _ = printsym (quote "4")
            in ()
        else if decimal == 53 then
            let _ = printsym (quote "5")
            in ()
        else if decimal == 54 then
            let _ = printsym (quote "6")
            in ()
        else if decimal == 55 then
            let _ = printsym (quote "7")
            in ()
        else if decimal == 56 then
            let _ = printsym (quote "8")
            in ()
        else if decimal == 57 then
            let _ = printsym (quote "9")
            in ()
        else if decimal == 58 then
            let _ = printsym (quote ":")
            in ()
        else if decimal == 59 then
            let _ = printsym (quote ";")
            in ()
        else if decimal == 60 then
            let _ = printsym (quote "<")
            in ()
        else if decimal == 61 then
            let _ = printsym (quote "=")
            in ()
        else if decimal == 62 then
            let _ = printsym (quote ">")
            in ()
        else if decimal == 63 then
            let _ = printsym (quote "?")
            in ()
        else if decimal == 64 then
            let _ = printsym (quote "@")
            in ()
        else if decimal == 65 then
            let _ = printsym (quote "A")
            in ()
        else if decimal == 66 then
            let _ = printsym (quote "B")
            in ()
        else if decimal == 67 then
            let _ = printsym (quote "C")
            in ()
        else if decimal == 68 then
            let _ = printsym (quote "D")
            in ()
        else if decimal == 69 then
            let _ = printsym (quote "E")
            in ()
        else if decimal == 70 then
            let _ = printsym (quote "F")
            in ()
        else if decimal == 71 then
            let _ = printsym (quote "G")
            in ()
        else if decimal == 72 then
            let _ = printsym (quote "H")
            in ()
        else if decimal == 73 then
            let _ = printsym (quote "I")
            in ()
        else if decimal == 74 then
            let _ = printsym (quote "J")
            in ()
        else if decimal == 75 then
            let _ = printsym (quote "K")
            in ()
        else if decimal == 76 then
            let _ = printsym (quote "L")
            in ()
        else if decimal == 77 then
            let _ = printsym (quote "M")
            in ()
        else if decimal == 78 then
            let _ = printsym (quote "N")
            in ()
        else if decimal == 79 then
            let _ = printsym (quote "O")
            in ()
        else if decimal == 80 then
            let _ = printsym (quote "P")
            in ()
        else if decimal == 81 then
            let _ = printsym (quote "Q")
            in ()
        else if decimal == 82 then
            let _ = printsym (quote "R")
            in ()
        else if decimal == 83 then
            let _ = printsym (quote "S")
            in ()
        else if decimal == 84 then
            let _ = printsym (quote "T")
            in ()
        else if decimal == 85 then
            let _ = printsym (quote "U")
            in ()
        else if decimal == 86 then
            let _ = printsym (quote "V")
            in ()
        else if decimal == 87 then
            let _ = printsym (quote "W")
            in ()
        else if decimal == 88 then
            let _ = printsym (quote "X")
            in ()
        else if decimal == 89 then
            let _ = printsym (quote "Y")
            in ()    
        else if decimal == 90 then
            let _ = printsym (quote "Z")
            in ()
        else if decimal == 91 then
            let _ = printsym (quote "[")
            in ()
        else if decimal == 92 then
            let _ = printsym (quote "\\")
            in ()
        else if decimal == 93 then
            let _ = printsym (quote "]")
            in ()
        else if decimal == 94 then
            let _ = printsym (quote "^")
            in ()
        else if decimal == 95 then
            let _ = printsym (quote "_")
            in ()
        else if decimal == 96 then
            let _ = printsym (quote "`")
            in ()
        else if decimal == 97 then
            let _ = printsym (quote "a")
            in ()
        else if decimal == 98 then
            let _ = printsym (quote "b")
            in ()
        else if decimal == 99 then
            let _ = printsym (quote "c")
            in ()
        else if decimal == 100 then
            let _ = printsym (quote "d")
            in ()
        else if decimal == 101 then
            let _ = printsym (quote "e")
            in ()
        else if decimal == 102 then
            let _ = printsym (quote "f")
            in ()
        else if decimal == 103 then
            let _ = printsym (quote "g")
            in ()
        else if decimal == 104 then
            let _ = printsym (quote "h")
            in ()
        else if decimal == 105 then
            let _ = printsym (quote "i")
            in ()
        else if decimal == 106 then
            let _ = printsym (quote "j")
            in ()
        else if decimal == 107 then
            let _ = printsym (quote "k")
            in ()
        else if decimal == 108 then
            let _ = printsym (quote "l")
            in ()
        else if decimal == 109 then
            let _ = printsym (quote "m")
            in ()
        else if decimal == 110 then
            let _ = printsym (quote "n")
            in ()
        else if decimal == 111 then
            let _ = printsym (quote "o")
            in ()
        else if decimal == 112 then
            let _ = printsym (quote "p")
            in ()
        else if decimal == 113 then
            let _ = printsym (quote "q")
            in ()
        else if decimal == 114 then
            let _ = printsym (quote "r")
            in ()
        else if decimal == 115 then
            let _ = printsym (quote "s")
            in ()
        else if decimal == 116 then
            let _ = printsym (quote "t")
            in ()
        else if decimal == 117 then
            let _ = printsym (quote "u")
            in ()
        else if decimal == 118 then
            let _ = printsym (quote "v")
            in ()
        else if decimal == 119 then
            let _ = printsym (quote "w")
            in ()
        else if decimal == 120 then
            let _ = printsym (quote "x")
            in ()
        else if decimal == 121 then
            let _ = printsym (quote "y")
            in ()
        else if decimal == 122 then
            let _ = printsym (quote "z")
            in ()
        else if decimal == 123 then
            let _ = printsym (quote "{")
            in ()
        else if decimal == 124 then
            let _ = printsym (quote "|")
            in ()
        else if decimal == 125 then
            let _ = printsym (quote "}")
            in ()
        else if decimal == 126 then
            let _ = printsym (quote "~")
            in ()
        else
            let _ = printsym (quote "DEL")
            in ()

printString :: String -> ()
printString string = 
    case string of 
        End -> 
            let _ = printsym (quote "End")
            in ()
        C val rst -> 
            let _ = printsym (quote "(C ")
                _ = printAscii val
                _ = printsym (quote "SPACE")
                _ = printString rst
                _ = printsym (quote ")")
            in ()

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
            

printPageList :: PageList -> ()
printPageList lst =
  case lst of
    Nil -> 
        let _ = printsym (quote "Nil")
            _ = printsym (quote "SPACE")
        in ()
    Cons a rst ->
      let _ = printsym (quote "(Cons ")
          _ = printContent a
          _ = printsym (quote "SPACE")
          _ = printPageList rst
          _ = printsym (quote ")")
          _ = printsym (quote "SPACE")
      in ()
    Snoc rst a -> 
        let _ = printsym (quote "(Snoc ")
            _ = printPageList rst
            _ = printContent a
            _ = printsym (quote "SPACE")
            _ = printsym (quote ")")
            _ = printsym (quote "SPACE")
        in ()

-------------------------------- Print functions end here -----------------------------------



gibbon_main = 
    let cons_list     = (mkConsRandomTextPageList 30000 500)
        --_             = printPageList cons_list
        --_             = printsym (quote "SPACE")
        snoc_list     = (mkSnocRandomTextPageList 30000 500)
        --_             = printPageList snoc_list
        --_             = printsym (quote "SPACE")
        cons_new_list = iterate (asciiInvertPageList cons_list)
        --_             = printPageList cons_new_list
        --_             = printsym (quote "SPACE")
        snoc_new_list = iterate (asciiInvertPageList snoc_list)
        --_             = printPageList snoc_new_list
        --_             = printsym (quote "SPACE")
        
    in ()
