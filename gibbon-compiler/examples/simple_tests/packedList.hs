data PackedInt = PacI Int
data List = Cons Int PackedInt List | Nil 

addPackedInt' :: PackedInt -> Int -> PackedInt
addPackedInt' a b = case a of
                     PacI a' -> PacI (a' + b)

addPackedInt :: PackedInt -> PackedInt -> PackedInt
addPackedInt a b = case a of
                      PacI a' -> case b of
                                    PacI b' -> PacI (a' + b')

unwrapPackedInt :: PackedInt -> Int
unwrapPackedInt a = case a of
                      PacI a' -> a'

mkPackedInt :: Int -> PackedInt
mkPackedInt i = let new_packed_int = PacI i
                  in new_packed_int

mkList :: Int -> List
mkList length = if length <= 0
                then Nil
		else
                 let i = mkPackedInt length
                     rst = mkList (length - 1)
		   in Cons length i rst

add1 :: List -> List
add1 lst = case lst of
		Nil -> Nil
		Cons j i rst -> let
                        i1 = addPackedInt' i 1
					  in Cons (j + 1) i1 (add1 rst)

sumList :: List -> Int
sumList lst = case lst of
 		   Nil -> 0
 		   Cons j i rst -> let i' = unwrapPackedInt i
                                       sumRst = sumList rst
                                     in j + i' + sumRst

gibbon_main = let 
                pi = mkPackedInt 10
                lst = mkList 10
                lst' = add1 lst
                -- _ = printPacked lst'
                --(val, lst'') = fieldDep lst'
               in (sumList lst') --printPacked lst' --val --sumList lst'




 
