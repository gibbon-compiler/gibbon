module NestedTuples where

foo (a, b) = (b, a)
bar (a, b) (c, d) (e, f) g = (b, (a, d), (c, f), e, g)
baz (a, b, (c, d, (e, f, (g, h, (i, j))))) =
  ((a, b), (c, (d, e), f), (g, h), (i, j))


gibbon_main =
  ( foo (1, (2,3))
  , bar (3, 4) (5, 6) (7, (8, 9)) 10
  , baz (11, (12, 13), (14, (15, 16), (17, 18, (19, 20, (21, 22)))))
  )
