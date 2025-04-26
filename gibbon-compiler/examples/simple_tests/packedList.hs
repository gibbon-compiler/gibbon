data PackedInt = PacI Int
data List = Cons PackedInt List | Nil 

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
mkPackedInt i = PacI i

mkList :: Int -> List
mkList length = if length <= 0
                then Nil
				else
                 let rst = mkList (length - 1)
                     i = mkPackedInt length
					in Cons i rst

add1 :: List -> List
add1 lst = case lst of
		Nil -> Nil
		Cons i rst -> let
                        i1 = addPackedInt' i 1
					  in Cons i1 (add1 rst)

-- sumList :: List -> Int
-- sumList lst = case lst of
-- 		   Nil -> 0
-- 		   Cons i rst -> let sumRst = sumList rst
--                                    in (unwrapPackedInt i) + sumRst

gibbon_main = let 
                pi = PacI 10
                lst = mkList 20000000
                lst' = iterate (add1 lst)
                -- _ = printPacked lst'
                --(val, lst'') = fieldDep lst'
               in (printPacked lst') --printPacked lst' --val --sumList lst'




 
