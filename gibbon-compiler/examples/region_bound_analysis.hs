data List = Nil | Cons Int List

reverse :: List -> List -> List
reverse xs acc = case xs of
  Nil       -> acc
  Cons z zs -> reverse zs (Cons z acc)

gibbon_main =
  case reverse (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))) Nil of
    Cons v _ -> v
    Nil      -> 0
