# How to Annotate Your Gibbon Source Files (v3.1)

The benchmarking script uses three kinds of source-file information:

| Source | How it's obtained |
|--------|-------------------|
| ADT field count (`adt_fields`) | Your `-- @BENCH` comment |
| Per-pass field usage (`uses`) | Extension to existing `printsym` line |
| Buffer counts (AoS / SoA) | **Automatic** — parsed from the `data` declaration |

---

## Automatic: Buffer count from ADT definition

No annotation needed. The script parses your `data` declaration directly.

**Counting rule:**
```
AoS buffers = 1  (always — all data in one packed buffer)

SoA buffers = 1  (constructor tags)
            + 1 per field slot in every constructor
              (recursive and non-recursive fields each get their own buffer)
```

**Example:**
```haskell
data Tree = Node Int Tree Tree | Leaf Int
--         ──────────────────   ────────
--         Node: Int, Tree, Tree  (3 field slots)
--         Leaf: Int              (1 field slot)
--
-- AoS:  1 buffer
-- SoA:  1 (tags) + 3 (Node fields) + 1 (Leaf field) = 5 buffers
```

The script prints a confirmation line for each program:
```
  ✓ DomTree.hs: ADT 'DomNode' → AoS=1 buf, SoA=7 bufs (6 field slots, 2 constructor(s))
```

### Optional: name the target ADT explicitly

If your file defines multiple `data` types, the script picks the one with the most
field slots. To override this heuristic, add one comment anywhere:

```haskell
-- @BENCH adt_type=DomNode
```

---

## Step 1 — Annotate the ADT field count (for dead-field analysis)

Add one comment near the `data` declaration:

```haskell
-- @BENCH adt_fields=5
data DomNode = DomLeaf
             | DomNode Color Float Float Float DomNode
```

Count the **non-recursive** value fields across all constructors.
(Recursive child pointers are NOT counted here; they are counted automatically
for buffer analysis.)

---

## Step 2 — Annotate each pass with field usage

Extend your existing `printsym` line. Add `, uses=N` inside the parentheses:

```haskell
-- before:
_ = printsym (quote "Running pass SumArea (fold): ")

-- after — uses=1 because only the 'area' field is read:
_ = printsym (quote "Running pass SumArea (fold, uses=1): ")
```

`uses` should count every distinct ADT field the pass reads or writes.
Include recursive child traversals if you want buffer counts to be accurate.

### Optional: `ilp=N` on map passes

The annotation is a comma-separated `key=value` list, so more keys can be added
without breaking older programs. The only other key currently understood is
`ilp=N` — the number of **independent dependence chains** in the pass body:

```haskell
-- one serial Horner chain: each multiply waits on the previous one
_ = printsym (quote "Running pass mapSer8 (map, uses=1, ilp=1): ")

-- two chains that can issue in parallel
_ = printsym (quote "Running pass mapChain4 (map, uses=1, ilp=2): ")
```

It feeds the *Map passes — vectorization vs loop+share scalar* table in the
layout-version report. ILP matters there because it sets the ceiling a map pass
can reach: at the same arithmetic intensity, `ilp=1` is latency-bound (packed
multiply has worse latency than scalar `imul`) while `ilp=2` gets close to the
throughput ceiling. Measured on `MapIntensityV2.hs`, the asymptotic speedup is
1.56× at ILP 1 versus 2.21× at ILP 2.

Omit it and the column shows `--`; nothing else changes. Unrecognised keys are
parsed and ignored, so the syntax is forward compatible.

Note that the companion `mul/el` column is **not** annotated — it is measured by
disassembling the scalar build, because declared arithmetic has repeatedly been
optimized away without notice. See `check_intensity_codegen.py`.

---

## Complete Example — DomTree.hs

```haskell
module DomTree where

-- @BENCH adt_fields=4
-- @BENCH adt_type=DomNode
data DomNode = DomLeaf
             | DomNode Color   -- field 1 (non-recursive)
                       Float   -- field 2 (non-recursive)
                       Float   -- field 3 (non-recursive)
                       Float   -- field 4 (non-recursive)
                       DomNode -- recursive child (auto-counted for buffers)

-- fold: only reads 'area' (field 4) → uses=1
sumArea :: DomNode -> Float
sumArea node =
  _ = printsym (quote "Running pass sumArea (fold, uses=1): ")
  ...

-- map: reads and writes width, height, area (fields 2,3,4) → uses=3
scaleLayout :: Float -> DomNode -> DomNode
scaleLayout f node =
  _ = printsym (quote "Running pass scaleLayout (map, uses=3): ")
  ...

-- fold: reads only Color (field 1) → uses=1
countStyled :: DomNode -> Int
countStyled node =
  _ = printsym (quote "Running pass countStyled (fold, uses=1): ")
  ...
```

**Buffer analysis the script will compute:**
```
ADT 'DomNode':
  Constructors: DomLeaf (0 fields), DomNode (5 fields: 4 non-rec + 1 rec)
  AoS: 1 buffer
  SoA: 1 (tags) + 0 (DomLeaf) + 5 (DomNode) = 6 buffers total
```

**Per-pass table (Bufs column shows AoS/SoA used/SoA total):**

| Pass        | T | Uses | Dead% | Bufs (AoS/SoA) | AoS (s) | SoA (s) | Speedup |
|-------------|---|------|-------|----------------|---------|---------|---------|
| sumArea     | F | 1/4  | 75%   | 1/2/6          | …       | …       | …       |
| scaleLayout | M | 3/4  | 25%   | 1/4/6          | …       | …       | …       |
| countStyled | F | 1/4  | 75%   | 1/2/6          | …       | …       | …       |

The **"Bufs (AoS/SoA)"** column reads as:
`AoS_buffers_used / SoA_buffers_used / SoA_total_buffers`

---

## New figures produced

| Figure | What it shows |
|--------|---------------|
| `buffers_vs_speedup.pdf` | Scatter: SoA buf-access ratio (x) vs speedup (y). Lower ratio → fewer cache streams → expected SoA advantage. |
| `dead_vs_speedup.pdf` | Scatter: dead-field ratio (x) vs speedup (y). |

---

## Annotation format summary

```
-- @BENCH adt_fields=N        (once per file; count non-recursive fields)
-- @BENCH adt_type=TypeName   (optional; overrides ADT auto-detection)

_ = printsym (quote "Running pass <name> (<type>, uses=N): ")
                                           ^^^^    ^^^^^^
                                           fold    fields accessed
                                           or map
```

Buffer counts are derived automatically from the `data` declaration —
no extra annotation needed for them.

---

## `OPT:` annotations — opting a function into an optimization

These are **source annotations on functions**, distinct from the `@BENCH` comments above.
They are parsed in `HaskellFrontend.hs` (`parseAnnotation`), and there are exactly three:

```haskell
{-# ANN mkTree     "OPT:StoreScalarCounts"     #-}
{-# ANN add1Tree   "OPT:MayVectorize"          #-}
{-# ANN someFn     "OPT:SelectiveBufferSharing" #-}
```

Layout annotations use the same pragma but attach to a **type**:

```haskell
{-# ANN type Tree "Factored" #-}   -- fully factored (SoA)
{-# ANN type Tree "Linear"   #-}   -- flat (AoS)
```

**An unrecognised string is a hard error, not a silently ignored pragma.** A typo'd layout
string, a different spelling such as `{-# ANN T (Layout "SoA") #-}`, or an unknown `OPT:`
name aborts the compile naming the accepted forms. This matters most for layout: an
unrecognised layout annotation must never let a datatype fall through to the Linear/AoS
default as if nothing had been written.

### What an `OPT:` annotation means

**A promise the compiler is free to decline.** The annotation makes a function a *candidate*;
every pass then applies its own legality checks and may silently leave the function alone.
`OPT:MayVectorize` in particular is a promise that recursive calls are independent — it is
not a request that anything be vectorized, and it does not guarantee a loop is emitted.

To find out what actually happened, pass **`--loopification-report`**: it names every
candidate function and, for each, whether it was rewritten and if not why not. Before that
flag existed every decline was silent, which is how several of these annotations came to be
believed effective when they were not.

### The annotation's effect depends on CLI flags, silently in one direction

`OPT:MayVectorize` does nothing without `--opt-loopification` (or `--auto-loopification`),
and vectorization additionally requires `--use-mutable-cursors`. That last pair used to skip
silently; it is now a hard error. `OPT:StoreScalarCounts` needs
`--store-scalar-field-counts`, and `--defer-scalar-counts` without it is likewise refused
rather than being a no-op.

The general point for anyone reading a benchmark result: **a source annotation's effect is
conditional on the compiler flags of the run**, so an annotated program is not evidence that
the optimization ran.

## `shared=N` — a hand-written claim, not a measurement

Map-pass banners may carry `shared=N`:

```
_ = printsym (quote "Running pass targetReturnPass (map, uses=9, shared=6): ")
```

For a map, `shared=N` records how many scalar fields the pass leaves **unmodified**. A map
copies every field into the output region, so "fields used" is vacuously all of them and
distinguishes nothing; what separates one map from another is how much it merely *copies*,
because those are the buffers selective buffer sharing can share instead of rewriting.
`gibbon_benchmark.py` parses it out of the banner and reports it as `Σ_b`.

**It is written by hand in the source and is never checked against the compiler.** It states
what the author believed the pass leaves alone, not what selective buffer sharing achieved.
A pass once carried `shared=1` while zero sharing occurred, which made an unrelated
investigation look like a sharing bug. If you need to know what was actually shared, read
`--loopification-report` or the generated C, not the banner.
