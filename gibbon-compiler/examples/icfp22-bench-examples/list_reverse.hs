data List = Nil | Cons Int List

reverse :: List -> List -> List
reverse xs acc = case xs of
  Nil       -> acc
  Cons z zs -> reverse zs (Cons z acc)

create_vec :: Int -> List
create_vec n = if n == 0 then Nil else Cons n (create_vec (n - 1))

printlist :: List -> ()
printlist vec = case vec of
  Nil ->
    let _ = printsym (quote "NEWLINE")
    in  ()
  Cons x vec' ->
    let _ = printint x
        _ = printsym (quote "SPACE")
        _ = printlist vec'
    in  ()

bench_main :: ()
bench_main =
  let n     = sizeParam
      vec   = create_vec n
      revec = reverse vec Nil
    --   _     = printlist vec
    --   _     = printlist revec
  in  ()

gibbon_main = bench_main
