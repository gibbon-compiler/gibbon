module Test187 where

import Gibbon.Prelude

data Foo = K2 Foo Foo | K0

-- | Inferlocations cannot infer that y' needs to be copied, so we fix this
--   in an earlier pass.
foo :: Foo -> Foo
foo a =
  case a of
    K2 x y ->
      let y' = foo y
          x' = foo x
      in K2 x' y'
    K0 -> K0

-- | Inferlocations does copy the second argument (x) to K2,
--   so no additional copies need to be inserted earlier.
bar :: Foo
bar =
  let a = K2 K0 K0 in
    case a of
      K0 -> K0
      K2 x y -> K2 x x

gibbon_main =
  let x = foo (K2 K0 K0)
      y = bar
{-
      -- should print:
      --   (K2 (K0 ) ->i (K0 ))
      --   (K2  ->i (K0 )(K0 ))

      _ = printPacked x
      _ = print_newline ()
      _ = printPacked y
      _ = print_newline ()
-}
  in 42
