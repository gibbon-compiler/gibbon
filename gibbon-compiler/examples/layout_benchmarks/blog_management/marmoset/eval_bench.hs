import Eval

gibbon_main =
  let
    n = 45
    t = mkRandTree n

    -- _ = iterate (eval t)
    s = iterate (evalR t)
  in ()

