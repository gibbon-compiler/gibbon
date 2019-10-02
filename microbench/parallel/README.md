# Parallel sumFoo with automatic granularity control

```
data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo


mkFoo :: Int -> Foo
mkFoo n
  | n <= 0    = A 10
  | n == 1    = B n (mkFoo (n-1)) (mkFoo (n-2))
  | otherwise = C n (mkFoo (n-1)) (mkFoo (n-2)) (mkFoo (n-3))


sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i          -> i
    B n f1 f2    -> n + sumFoo f1 + sumFoo f2
    C n f1 f2 f3 -> n + sumFoo f1 + sumFoo f2 + sumFoo f3
```


| Variant | mkFoo (median of 9) | sumFoo (median of 9) |
| :---:   |        :---:        |         :---:        |
| (1) | 99.6ms | 5.35ms |
| (2) | 96.48ms | 6.03ms |
| Packed Sequential | 90.62ms | 24.54ms |
| Pointer Parallel | 0.24s | 9.96ms |
| Pointer Sequential | 0.24s | 33ms |


For (1) and (2), the threshold for parallelism was `size >= 64KB`. For the
pointer variant, it was `depth > 12`.

..TODO..
