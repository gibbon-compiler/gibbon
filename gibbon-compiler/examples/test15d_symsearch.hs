data List = Nil | Cons Sym List

elem_go :: Int -> Sym -> List -> Int
elem_go n x xs =
  case xs of
    Nil       -> -1
    Cons y ys -> if eqsym y x
                 then n
                 else elem_go (n + 1) x ys

elem :: Sym -> List -> Int
elem x xs = elem_go 0 x xs


gibbon_main = let a  = quote "abc"
                  as = Cons (quote "a") (Cons (quote "b") (Cons (quote "abc") Nil))
              in elem a as
