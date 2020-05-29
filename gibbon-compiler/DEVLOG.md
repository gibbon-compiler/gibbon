Development log: Core Gibbon Compiler
===================================

This is a log to track our internal development notes as we're working
on this compiler.  It's in forward-chronological order.


[2016.11.12] {Debugging}
----------------------------------------

I believe that one of the simplification passes (e.g. inlinetriv, it's
before unariser), is introducing a bug with projection.


After cursorize:

```Haskell
  ProjE 0
        (LetE ("flatPr58",
               ProdTy [PackedTy "Tree"
                                (),
                       PackedTy "CURSOR_TY"
                                ()],
               LetE ("cursplus1_73",
                     PackedTy "Tree"
                              (),
                     MkPackedE "Leaf"
                               [VarE "add1_tree70"])
                    (LetE ("curstmp74",
                           PackedTy "CURSOR_TY"
                                    (),
                           AppE "WriteInt"
                                (MkProdE [VarE "cursplus1_73",
                                          VarE "flatPk10"]))
                          (MkProdE [VarE "add1_tree70",
                                    VarE "curstmp74"])))
              (VarE "flatPr58"))],
```

Late becomes, after InlineTriv:


```Haskell
 (LetE ("curstmp74",                          -- end_B
        PackedTy "CURSOR_TY" (),
        AppE "WriteInt"
             (MkProdE [VarE "cursplus1_73",
                       VarE "flatPk10"]))
       (LetE ("end_tr1",
              PackedTy "CURSOR_TY"
                       (),
              PrimAppE AddP
                       [ProjE 1
                              (VarE "fnarg71"),  -- A
                        LitE 9])
             (MkProdE [MkProdE [VarE "end_tr1",     -- end_A
                                ProjE 0
                                      (VarE "fnarg71")],  -- B
                       ProjE 0
                         (VarE "curstmp74")])
```

Here we have an invalid projection on the `curstmp74`, whereas before
it was correctly applied to `flatPr58`.

----------------------------------------

Nope, that was not the problem.  In fact the curstmp74 above was a red
herring, because the cursorize pass was eroneously producing two
duplicated bindings for curstmp74.

So here it goes again.  Starting after inlinePacked:


```Haskell
   (LetE ("flatPk10",
          IntTy,
          PrimAppE AddP
                   [VarE "flatPA54",
                    VarE "n2"])
         (MkProdE [VarE "end_tr1",
                   LetE ("flatPr58",
                         PackedTy "Tree"
                                  (),
                         MkPackedE "Leaf"
                                   [VarE "flatPk10"])
                        (VarE "NAMED_VAL")]))
```

Here's the SECOND place curstmp74 gets bound and the SECOND Leaf
constructor due to code duplication.  (That shoud be InlinePacked's
job, not cursorize!)

```Haskell
    LetE ("flat75",
          ProdTy [],
          MkProdE [])
         (LetE ("flat76",
                ProdTy [PackedTy "CURSOR_TY"
                                 ()],
                ProjE 1
                      (LetE ("flatPr58",
                             ProdTy [PackedTy "Tree"
                                              (),
                                     PackedTy "CURSOR_TY"
                                              ()],
                             LetE ("cursplus1_73",
                                   PackedTy "Tree"
                                            (),
                                   MkPackedE "Leaf"
                                             [VarE "add1_tree70"])
                                  (LetE ("curstmp74",
                                         PackedTy "CURSOR_TY"
                                                  (),
                                         AppE "WriteInt"
                                              (MkProdE [VarE "cursplus1_73",
                                                        VarE "flatPk10"]))
                                        (MkProdE [VarE "add1_tree70",
                                                  VarE "curstmp74"])))
                            (VarE "flatPr58")))
               (ProjE 0
                      (VarE "flat76")))
```

Ok, here there's one bug straight off.  It created a unary "Prod" type
for flat76.  That explains the bogus ProjE 0, because it's trying to
reference a bogus unary tuple.

But where's the code duplication come from?  flat76 is created by
cursorize.  This whole thing is part of a big `(_,_)` dilated value
which has managed to duplicate the Leaf constructor in both the front
and end expressions. ... And that's before any subsequent
flattening/inlining.



[2016.11.13] {Debugging inlineTriv}
----------------------------------------

There's a new flatten, but it really looks like flatten's output
typechecks.  Here it is before inlineTriv:

```Haskel
    (LetE ("unpkcall62",
           ProdTy [PackedTy "CURSOR_TY"
                            (),
                   PackedTy "CURSOR_TY"
                            ()],
           AppE "add1_tree"
                (MkProdE [VarE "flddst58",
                          VarE "y4"]))
          (LetE ("hoistapp39",
                 ProdTy [PackedTy "CURSOR_TY"
                                  (),
                         PackedTy "Tree"
                                  ()],
                 ProjE 1
                       (VarE "unpkcall62"))
```

And then after inlineTriv, we get this:


```Haskell
    (LetE ("unpkcall62",
        ProdTy [PackedTy "CURSOR_TY" (),
                PackedTy "CURSOR_TY" ()],
        AppE "add1_tree"
             (MkProdE [ProjE 1
                             (ProjE 1
                                    (VarE "unpkcall59")),
                       ProjE 0
                             (ProjE 1
                                    (VarE "unpkcall59"))]))
       (MkProdE [MkProdE [ProjE 0
                                (ProjE 1
                                       (VarE "unpkcall62")),
                          ProjE 0
                                (VarE "fnarg50")],
                 ProjE 1
                       (ProjE 1
                               (VarE "unpkcall62"))]))))])
```

Ok, unsurprisingly the problem is still with Cursorize.  It produces
this badly typed code:

```Haskell
    LetE ("hoistapp39",
     ProdTy [PackedTy "CURSOR_TY"
                      (),
             PackedTy "Tree"
                      ()],
     LetE ("unpkcall62",
           ProdTy [PackedTy "CURSOR_TY"
                            (),
                   PackedTy "CURSOR_TY"
                            ()],
           AppE "add1_tree"
                (MkProdE [VarE "flddst58",
                          VarE "y4"]))
          (ProjE 1
                 (MkProdE [MkProdE [ProjE 0
                                          (VarE "unpkcall62"),
                                    VarE "flddst58"],
                           ProjE 1
                                 (VarE "unpkcall62")])))
    (VarE "hoistapp39")
```

From the correct input:

```Haskell
    ProjE 1
          (LetE ("hoistapp39",
                 ProdTy [PackedTy "CURSOR_TY"
                                  (),
                         PackedTy "Tree"
                                  ()],
                 AppE "add1_tree"
                      (VarE "y4"))
                (VarE "NAMED_VAL"))
```

Hoistapp39 is supposed to be a tuple.  It's supposed to be the full
function result with end-witneses.  This expression pushes the
`ProjE 1` projcetion into the wrong place:

    (ProjE 1
     (MkProdE [MkProdE [ProjE 0
                              (VarE "unpkcall62"),
                        VarE "flddst58"],
               ProjE 1
                     (VarE "unpkcall62")]))


[2016.11.13] {Debugging function arguments in inlineTriv}
---------------------------------------------------------

Next problem seems to be that this function call:

```Haskell
     AppE "add1_tree"
      (MkProdE [VarE "flddst58",
        VarE "y4"]))
```

Here y4 is an alias for end_x3, and is CursorTy as it should be.
But then after inlineTrivs, we get this weird thing:

```Haskell
    (LetE ("unpkcall62",
        ProdTy [PackedTy "CURSOR_TY" (),
                PackedTy "CURSOR_TY" ()],
        AppE "add1_tree"
             (MkProdE [ProjE 1
                             (VarE "unpkcall59"),
                       MkProdE [ProjE 0
                                      (VarE "unpkcall59"),
                                VarE "cursplus1_56"]]))
```

It sure looks like a dilated value is getting stuck in place of a
"front value". The car of unpkcall59 is indeed the end-of-a witness
returned by the first call to add1_tree in this Node case.

But cursplus1_56 is bogus... that's actually the output position right
after the written Node tag.  _56 is indeed the correct output cursor
to the FIRST call to add1.

So maybe there is a legit problem with the end_x3 witness?

```Haskell
    (LetE ("hoistapp35",
           ProdTy [PackedTy "CURSOR_TY"
                            (),
                   PackedTy "Tree"
                            ()],
           MkProdE [MkProdE [ProjE 0
                                   (VarE "unpkcall59"),
                             VarE "cursplus1_56"],
                    ProjE 13
                          (VarE "unpkcall59")])
          (LetE ("fldtup57",
                 ProdTy [PackedTy "Tree"
                                  (),
                         PackedTy "CURSOR_TY"
                                  ()],
                 VarE "hoistapp35")
                (LetE ("flddst58",
                       PackedTy "CURSOR_TY"
                                (),
                       ProjE 1
                             (VarE "fldtup57"))
                      (LetE ("end_x3",
                             PackedTy "CURSOR_TY"
                                      (),
                             ProjE 0
                                   (VarE "hoistapp35"))
                            (LetE ("y4",
                                   PackedTy "CURSOR_TY"
                                            (),
                                   VarE "end_x3")
```

Here's what the first of the two add1 call sites looks like BEFORE cursorize:

```Haskell
    [ProjE 1
           (LetE ("hoistapp35",
                  ProdTy [PackedTy "CURSOR_TY"
                                   (),
                          PackedTy "Tree"
                                   ()],
                  AppE "add1_tree"
                       (VarE "x3"))
                 (VarE "NAMED_VAL")),
```


But, above... hoistapp35 is not type checking..  Its type has not been
updated, but it is clearly returning a dilated version of
(cursor,tree) which becomes ((cursor,tree),end_tree)

AH!  The NamedVal handling was incorrectly binding names to dilated
types.



[2016.11.13] {Seems to be accidentally dilating }
------------------------------------------------

For add1tree, right before lower we are generating this bad return
value in tail position:

```Haskell
    (LetE ("unpkcall57",
      ProdTy [PackedTy "CURSOR_TY" (),
              PackedTy "CURSOR_TY" ()],
      AppE "add1_tree"
           (MkProdE [ProjE 1
                           (VarE "unpkcall53"),
                     ProjE 0
                           (VarE "unpkcall53")]))
     (MkProdE [MkProdE [ProjE 0
                              (VarE "unpkcall57"),
                        ProjE 0
                              (VarE "fnarg43")],
               ProjE 1
                     (VarE "unpkcall57")]))))]})],
```

I thought that was just an eroneously dilated value that needed to be
undilated, but that's not quite it.  The function should return
`(end_a,end_b)`, and the end-witness in the input program should be
treated just as a scalar.  That return value above is instead:

    ((end_a, b), end_b)

Now... there is a `b+9` in circulation after cursorize (end_tr0, where
"a" = tr0 in this example).  The leaf branch terminates returns this:

    (MkProdE [MkProdE [VarE "end_tr0",
                       ProjE 0
                             (VarE "combdil48")],
              ProjE 1
                    (VarE "combdil48")])

Ok, so it's clear how this is a dilation.  The end_tr0 thing doesn't
get reflected in the dilation.  Rather, it's the start and end of "b".

`combdil48` is an alias for a (tree,cursor) pair representing the
completed "b" value.  This actually sure does make it look like the
"splice" thing is failing its job...

  It was supposed to throw away that "b" and give (end_a,end_b) only.

[2016.11.13] {Debugging new flatten}
----------------------------------------

After writing a new flatten, there are still some problems to debug.
findWitnesses is failing on this input:

```Haskell
 FunDef {funname = "trav",
            funty = ArrowTy {arrIn = PackedTy "CURSOR_TY" "a",
                             arrEffs = [Traverse "a"],
                             arrOut = ProdTy [PackedTy "CURSOR_TY" "end_a",IntTy]},
            funarg = "x0",
            funbod = CaseE (VarE "x0")
                           [("Zero",
                             ["cursIn16"],
                             LetE ("end_x0",
                                   PackedTy "CURSOR_TY" (),
                                   PrimAppE AddP [VarE "x0",LitE 1])
                                  (MkProdE [VarE "end_x0",LitE 0])),
                            ("Suc",
                             ["cursIn16"],
                             LetE ("n1", PackedTy "CURSOR_TY" (), VarE "cursIn16")
                                  (LetE ("fltPrm3",
                                         IntTy,
                                         LetE ("hoistapp11",
                                               ProdTy [PackedTy "CURSOR_TY" (),IntTy],
                                               AppE "trav" (VarE "n1"))
                                              (LetE ("end_n1",
                                                     PackedTy "CURSOR_TY" (),
                                                     ProjE 0 (VarE "hoistapp11"))
                                                    (ProjE 1 (VarE "hoistapp11"))))
                                        (LetE ("fltPrd15",
                                               IntTy,
                                               PrimAppE AddP [LitE 1,VarE "fltPrm3"])
                                              (MkProdE [VarE "end_n1",
                                                        VarE "fltPrd15"]))))]})],
```

Ok, that looks like flatten's fault.  It should have squished that
`Let (_,_,Let _ _)`.


[2020.05.28] {A good vector library for Gibbon}
-----------------------------------------------

We'd like the library to have the following operations on vectors.

| Op                                                 | Work | Span |
|----------------------------------------------------|------|------|
| alloc :: Int -> Int -> Vector a                    | O(1) | O(1) |
| length :: Vector a -> Int                          | O(1) | O(1) |
| isEmpty :: Vector a -> Bool                        | O(1) | O(1) |
| slice :: Int -> Int -> Vector a -> Vector a        | O(1) | O(1) |
| nth :: Vector a -> a                               | O(1) | O(1) |
| splitAt :: Int -> Vector a -> (Vector a, Vector a) | O(1) | O(1) |
| generate :: Int -> (Int -> a) -> Vector a          | O(n) | O(n) |
| par-generate                                       | O(n) | O(1) |
| map :: (a -> b) -> Vector a -> Vector b            | O(n) | O(n) |
| par-map                                            | O(n) | O(1) |
| foldr :: (a -> b -> b) -> b -> Vector a -> b       | O(n) | O(n) |
| par-foldr                                          | O(n) | ??   |
| append :: Vector a -> Vector a -> Vector a         | O(n) | O(n) |
| par-append                                         | O(n) | O(1) |
| filter :: (a -> Bool) -> Vector a -> Vector a      | O(n) | O(n) |
| par-filter                                         | ??   | ??   |
| snoc                                               | O(n) | O(n) |
| par-snoc                                           | O(n) | O(1) |
| update                                             | O(n) | 1    |
|                                                    |      |      |
