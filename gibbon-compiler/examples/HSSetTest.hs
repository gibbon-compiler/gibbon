module HSSetTest where

gibbon_main =
  let x = (quote "hello")
      y = empty_set
      z = insert_set y x
  in if contains_set z (quote "hello")
     then 42
     else 0
