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

    C_big  ....  -> sum things in parallel

```

| Variant | mkFoo (median of 9) | sumFoo (median of 9) |
| :---:   |        :---:        |         :---:        |
| Packed (1) | 100ms | 5.11ms |
| Packed (2) | 95.17ms | 6.03ms |
| Packed Sequential | 100ms | 24.51ms |
| Pointer Parallel | 0.24s | 9.96ms |
| Pointer Sequential | 0.24s | 33ms |


For (1) and (2), the threshold for parallelism was `size >= 64KB`. For the
pointer variant, it was `depth > 12`.
These benchmarks we run on Swarm (Ubuntu 18.04 / GCC-7 / 64GB RAM / 18 cores?) and used Cilk for
parallel processing.

We use different data constructors for granularity control i.e there's a special
constructor `C_big` that `mkFoo` writes which tells `sumFoo` that it should process
it's parts in parallel.
However, in `mkFoo` we won't know if `C` will need to be a `C_big` or not
before writing out it's subtrees. Below are two different ideas to work around this.


### Representation (1)

In representation (1), we always assume that `C` is going to `C_big` i.e
all it's subtrees are going to be BIG (wrt the threshold).
And we always leave space for a pointer before writing the subtrees.

Before writing out the first subtree:

```
-----------------------------------------------
| C_big |    _    | n | write_subtree_1 ...
-----------------------------------------------
```

After writing all subtrees:

```
-----------------------------------------------
| C_big |    _    | n | FOO_1 | FOO_2 | FOO_3 |
-----------------------------------------------
```

Now, we check if the size of the whole thing is greater than the threshold i.e
if (size FOO_1) + (size FOO_2) + (size FOO_3) > threshold. If it's not, we leave
the hole as is, and change `C_big` to be `C`.

```
-----------------------------------------------
| C     |    _    | n | FOO_1 | FOO_2 | FOO_3 |
-----------------------------------------------
```


Otherwise, we use the scratch region given to `mkFoo` to write
the random access nodes, and store the address of those random access
nodes after `C_big`.


```
-----------------------------------------------
| C_big |  PTR    | n | FOO_1 | FOO_2 | FOO_3 |
-----------------------------------------------
            |
            |
            V
-----------------------------------------------
| ..... | RAN_1 | RAN_2| ....
-----------------------------------------------

```

The random access nodes are stored in a separate buffer because if it turns out
that we have to change the `C_big` to a `C`, we only waste 8 bytes every time,
as opposed to (size-of-packed - 1).


### Representation (2)

In representation (2), we do the opposite, and always assume that `C` is never
going to be big. So we start writing it as usual:

Before writing out the first subtree:

```
---------------------------------
| C | n | write_subtree_1 ...
---------------------------------
```

After writing all subtrees:

```
---------------------------------
| C | n | FOO_1 | FOO_2 | FOO_3 |
---------------------------------
```

Then we check if the size of the whole thing is greater than the threshold i.e
if (size FOO_1) + (size FOO_2) + (size FOO_3) > threshold. If it is, we
change it into a `C_big` just-in-time. We accomplish this with re-directions.
We shave off enough bytes to write a redirection node (9 bytes), and copy
that data off to another buffer. And then tie things together with 2 redireciton
nodes.


```
-------------------------------------------------
| R |  PTR  | FOO_1 | FOO_2 | FOO_3 |
-------------------------------------------------
        |      A
        |      |
        |      ~~~~~~~~~~~~~~~~~~~~~~~~~|
        V                               |
-------------------------------------------------
| ... | C_big| RAN_1 | RAN_2 | n | R | PTR | ....
-------------------------------------------------

```
