
data List = Nil | Cons Int List
data FList = FNil | FCons Float FList

data Adt = None | B List FList Adt | A FList List Adt


mkList :: Int -> List 
mkList len = if len <= 0 
             then Nil
             else let rst = mkList (len - 1)
                    in Cons len rst


mkFList :: Int -> FList
mkFList len = if len <= 0
              then FNil
              else let rst = mkFList (len - 1)
                    in FCons 0.0 rst


mkAdt :: Int -> Adt 
mkAdt len = if len <= 0 
            then None 
            else let l1 = mkList 10 
                     l2 = mkFList 10
                     rst = mkAdt (len - 1) 
                  in B l1 l2 rst


gibbon_main = 
            let adt = mkAdt 10
             in printPacked adt

