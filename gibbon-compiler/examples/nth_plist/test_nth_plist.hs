import Gibbon.PList 
import Gibbon.Prelude


make_plist :: Int -> Int -> PList Int 
make_plist len start = if len <= 0 then Nil 
		       else Cons start (make_plist (len-1) (start+1))


gibbon_main =
	let list :: PList Int 
            list = make_plist 100 0 
            value = nth_plist list 0 10 0 
            _     = printint value
            _     = printsym (quote "NEWLINE")
           in ()
