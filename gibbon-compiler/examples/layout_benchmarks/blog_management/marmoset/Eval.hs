data Ast
  = Val Bool
  | Not Ast
  | Or Ast Ast
  | And Ast Ast

--eval :: Ast -> Bool
--eval x = case x of
--  Val b -> b
--  Not e -> if eval e then False else True
--  Or e1 e2 -> 
--    if eval e1 then True
--    else eval e2
--  And e1 e2 -> 
--    if eval e1 then eval e2
--    else False

--simplify :: Ast -> Ast
--simplify x = Val (eval x)

evalR :: Ast -> Bool
{-# ANN evalR Or #-}
{-# ANN evalR And #-}
evalR x = case x of
  Val b -> b
  Not e -> if evalR e then False else True
  Or e1 e2 -> 
    if evalR e2 then True
    else evalR e1
  And e1 e2 -> 
    if evalR e2 then evalR e1
    else False

simplifyR :: Ast -> Ast
simplifyR x = Val (evalR x)

mkRandTree :: Int -> Ast
mkRandTree n = 
  if n > 0 then
    let m = mod rand 3 in
    if m == 0 then Not (mkRandTree (n-1))
    else if m == 1 then And (mkRandTree (n-1)) (mkRandTree (n-1))
    else Or (mkRandTree (n-1)) (mkRandTree (n-1))
  else Val (mod rand 2 == 0)
