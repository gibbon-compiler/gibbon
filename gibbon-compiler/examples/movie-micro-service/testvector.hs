module Tv where 
import Gibbon.Vector
import Gibbon.Prelude
import Gibbon.Maybe
import Gibbon.Prim

type Text = Vector Char

testf :: Text -> Char
testf t = head t 
-- intToChar :: Int -> Char 
-- intToChar i = case i of 
--             -- 0 -> '0'
--             1 -> '1'
--             2 -> '2'
--             3 -> '3'
--             4 -> '4'
--             5 -> '5'
--             6 -> '6'
--             7 -> '7' 
--             8 -> '8'
--             9 -> '9'
gibbon_main = 
    let 
      x = (quote "hello")
      y = empty_hash
      z = insert_hash y x (quote "world")
  in if eqsym (lookup_hash z (quote "hello")) (quote "world")
     then 42
     else 0