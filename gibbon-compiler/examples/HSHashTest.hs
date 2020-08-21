module HSHashTest where

gibbon_main =
  let x = (quote "hello")
      y = empty_hash
      z = insert_hash y x (quote "world")
  in if eqsym (lookup_hash z (quote "hello")) (quote "world")
     then 42
     else 0
