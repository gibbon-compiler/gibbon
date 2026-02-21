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
