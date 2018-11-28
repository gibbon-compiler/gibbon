In the current Gibbon implementation, we use pointers to add random access
capabilities to datatypes. But this has an adverse impact on the
serialization format. It prevents us from storing and mmap'ing
such a datatype to/from disk. A better way achieve the same thing would
be to store these offsets separately from the data itself.
Consider this example:

```Haskell
    data Foo = A Int
             | B Foo Foo
             | C Foo Foo Foo


    -- Factored out rep

    x = C (A 1) (A 2) (A 3)
    o = (9,0) (9,0)

    y = C (B (A 1) (A 2)) (A 3) (A 4)
    p = (21,1) (9,0) (9,0) (9,0)

    z = C (B (B (A 1) (A 2)) (A 3)) (A 4) (A 5)
    r = (32,2) (21,1) (9,0) (9,0) (9,0)
```
