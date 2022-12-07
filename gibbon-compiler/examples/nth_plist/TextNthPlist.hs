module TextNthPlist where 

import Gibbon.PList 
import Gibbon.Maybe
import Gibbon.Prelude


make_plist :: Int -> Int -> PList Int 
make_plist len start = if len <= 0 then Nil 
		       else Cons start (make_plist (len-1) (start+1))


gibbon_main =
	let list :: PList Int 
            list = make_plist 100 0 
            value = nth_plist list Nothing 10 
            _     = printPacked value
            _     = printsym (quote "NEWLINE")
           in ()
