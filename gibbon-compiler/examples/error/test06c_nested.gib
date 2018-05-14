#lang gibbon

(data Foo (MkFoo Int))
(data Bar (MkBar Foo))

(case (MkBar (MkFoo 99))
  [(MkBar f)
   (case f
     [(MkFoo n) n])])
