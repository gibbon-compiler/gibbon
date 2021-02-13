-- import Prelude hiding ( Maybe(..), Either (..), succ, not, foldr, map, head)

data MyList a = Nil
              | Cons a (MyList a)
  deriving Show

head :: a -> MyList a -> a
head d xs =
  case xs of
    Nil -> d
    Cons l ls -> l

gen_symbols :: Int -> MyList Sym
gen_symbols n =
 if n == 0
 then Nil
 else let s = gensym
      in Cons s (gen_symbols (n - 1))

count_occ :: Int -> Sym -> MyList Sym -> Int
count_occ acc s xs =
  case xs of
    Nil -> acc
    Cons l ls -> if eqsym s l
                 then count_occ (acc + 1) s ls
                 else count_occ acc s ls

has_dups :: MyList Sym -> Bool
has_dups xs =
  case xs of
    Nil       -> False
    Cons l ls ->
      if count_occ 0 l ls > 0
      then True
      else has_dups ls

gibbon_main =
  let xs      = gen_symbols 10
      s       = quote "unused"
      ys      = Cons (head s xs) xs
      no_dups = has_dups xs
      dups    = has_dups ys
  -- Expected answer: (False, True)
  in (no_dups, dups)
