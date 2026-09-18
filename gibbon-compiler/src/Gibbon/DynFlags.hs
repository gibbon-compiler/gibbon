{-# LANGUAGE CPP #-}

-- | Flags à la GHC
module Gibbon.DynFlags
  ( DynFlags(..), GeneralFlag(..), DebugFlag(..)
  , defaultDynFlags, dynflagsParser
  , gopt, gopt_set, dopt, dopt_set
  , SimdIsa(..), simdIsaOf, simdIsaWithReason, simdIsaName, simdIsaRegisterBytes
  , simdIsaCcFlags, simdIsaCpuFeature
  , parseSimdIsa
  ) where

#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Set as S
import Options.Applicative

data GeneralFlag
  = Opt_Gibbon1            -- ^ Set Opt_No_RemoveCopies & Opt_BigInfiniteRegions
  | Opt_Gibbon2            -- ^ Set Opt_RemoveCopies & Opt_InfiniteRegions
  | Opt_RemoveCopies       -- ^ Calls to copy functions are converted to indirections
  | Opt_No_RemoveCopies    -- ^ Unset Opt_RemoveCopies
  | Opt_InfiniteRegions    -- ^ Use infinite regions
  | Opt_BigInfiniteRegions -- ^ Use big infinite regions
  | Opt_BenchPrint         -- ^ Should the benchamrked function have its output printed?
  | Opt_Packed             -- ^ Use packed representation
  | Opt_Pointer            -- ^ Use pointer representation
  | Opt_BumpAlloc          -- ^ Use bump-pointer allocation if using the non-packed backend
  | Opt_Warnc              -- ^ Show warnings from the C compiler
  | Opt_DisableGC          -- ^ Don't run the the garbage collector (used by Codegen).
  | Opt_No_PureAnnot       -- ^ Don't use 'pure' annotations (a GCC optimization)
  | Opt_Fusion             -- ^ Enable fusion.
  | Opt_Parallel           -- ^ Fork/join parallelism.
  | Opt_RegionOnSpawn      -- ^ Allocate into fresh regions for every spawn, not steal.
  | Opt_GhcTc              -- ^ Typecheck with GHC before compiling with Gibbon.
  | Opt_RelativeOffsets    -- ^ Enable relative offsets.
  | Opt_CountParRegions    -- ^ Count and print the number of regions allocated for parallelism.
  | Opt_CountAllRegions    -- ^ Count and print the number of all the regions allocated.
  | Opt_RtsDebug           -- ^ Compile the RTS in debugging mode.
  | Opt_PrintGcStats       -- ^ Record and print GC statistics.
  | Opt_GenGc              -- ^ Use the new generational GC.
  | Opt_ReclaimIterateRegions
  -- ^ Reclaim the region chunks an @iterate@ benchmark iteration grew.  Each
  -- iteration rewinds to the output region's first chunk and re-grows it, and
  -- the previous iteration's chunk chain is stranded rather than freed, so
  -- memory grows by one whole output value per iteration.  Off by default:
  -- this changes runtime memory behaviour, so the pre-existing behaviour stays
  -- exactly recoverable.
  --
  -- Iterations do get FASTER with this on, and that is not a fidelity problem:
  -- the leak made the kernel supply fresh zeroed pages every iteration (2.8 GB
  -- over 31 iterations at 10M elements), which no real program calling the same
  -- map repeatedly would do.  What would be a fidelity problem is reusing the
  -- chunks WITHOUT freeing -- the data stays resident and the iteration skips
  -- work a cold run pays -- which is why growth still allocates normally.
  | Opt_NoEagerPromote     -- ^ Disable eager promotion.
  | Opt_SimpleWriteBarrier -- ^ Disables eliminate-indirection-chains optimization.
  | Opt_No_RAN             -- ^ Don't use shortcut pointers instead use extra traversals to reach get endwitness
  | Opt_UseMutableCursors  -- ^ Use Mutable Cursors instead of Immutable Cursors, this allows inplace updates to the Packed Cursor values.
  | Opt_MutableCursorsNonRec -- ^ A non-recursive SoA function that only reads packed
                             --   values omits its end-of-input-region cursors from its
                             --   return value; each caller reuses the ones it passed in.
                             --   Requires Opt_UseMutableCursors.
  | Opt_PapiInstrumentation -- ^ Enable PAPI instrumentation while compiling the gibbon binary.
  | Opt_PapiNativeInstrumentation -- ^ Enable native PAPI event instrumentation while compiling the gibbon binary.
  | Opt_TailCallOptimize   -- ^ For functions that are tail recursive, run the optimization pass to transform them in tail position.
  | Opt_StoreScalarFieldCounts -- ^ Store scalar-field counts for annotated SoA builders.
  | Opt_DeferScalarCounts -- ^ Maintain scalar-field counts with a deferred per-buffer counter
                          --   instead of a per-element footer bump, flushing at region growth
                          --   and at end of production.  See Note [Deferred scalar counts] in
                          --   Gibbon.Passes.AssignScalarCountSlots.
  | Opt_ScalarCountDiff -- ^ Emit both schemes and make every flush verify they agree instead of
                        --   applying; a mismatch aborts naming the slot.  Implies
                        --   Opt_DeferScalarCounts.
  | Opt_EnableLoopification -- ^ Enable loopification for OPT:MayVectorize traversals. For an SoA
                            --   target this also requires Opt_StoreScalarFieldCounts (a hard
                            --   compile error otherwise, whenever an SoA candidate exists).
  | Opt_AutoLoopification -- ^ Infer loopification candidates for map-like traversals structurally,
                          --   instead of requiring an OPT:MayVectorize annotation.
  | Opt_LoopificationReport -- ^ Print one line per function for each loopification pass:
                            --   whether it was rewritten, or the specific reason it was
                            --   declined.  Turns nothing on by itself.
  | Opt_EnableLoopFusion -- ^ Enable scalar-buffer loop fusion inside loopified SoA traversals.
                         --   Requires Opt_EnableLoopification or Opt_AutoLoopification (hard
                         --   compile error otherwise): it only fuses loops loopification produced.
  | Opt_EnableSelectiveBufferSharing -- ^ Enable post-loopification selective SoA buffer sharing.
                                     --   Requires Opt_EnableLoopification or Opt_AutoLoopification
                                     --   (hard compile error otherwise), same reason as above.
  | Opt_EnableVectorization -- ^ Enable SIMD vectorization for supported loopified SoA scalar-buffer
                            --   loops. Requires Opt_EnableLoopification or Opt_AutoLoopification
                            --   (hard compile error otherwise), same reason as above.
  | Opt_SimdW64Multiply -- ^ @--simd-w64-multiply@: let the vectorizer use the emulated
                        --   64-bit packed multiply, which is refused by default because it
                        --   is slower than the scalar multiply it would replace.
  | Opt_Sse41 -- ^ Compile the generated C with -msse4.1 (opt-in; default targets baseline SSE2).
  -- The SIMD instruction set BOTH sides of the compilation target: Gibbon's
  -- own vectorizer (which picks its register width from it) and the C
  -- compiler's auto-vectorizer (which gets the matching -m flag).  One
  -- decision, so the two can never be compiled for different targets --
  -- which is exactly the comparison error that made a Gibbon-vectorized
  -- build look better than it was: it received -march=native while the
  -- baseline it was measured against was left at the x86-64 default, where
  -- GCC's auto-vectorizer can only reach SSE2.
  | Opt_SimdIsaSse2    -- ^ @--simd-isa=sse2@
  | Opt_SimdIsaSse41   -- ^ @--simd-isa=sse4.1@
  | Opt_SimdIsaAvx2    -- ^ @--simd-isa=avx2@
  | Opt_SimdIsaNative  -- ^ @--simd-isa=native@
  | Opt_MarchNative -- ^ Compile the generated C with -march=native, so the SIMD helpers'
                    --   @#if defined(__SSE4_1__)@ / @__AVX512DQ__@ branches select the best
                    --   instruction the build machine actually has. Implied by
                    --   Opt_EnableVectorization unless Opt_SimdBaselineSse2 is set. Pass it
                    --   explicitly to NON-vectorized builds too when comparing against a
                    --   vectorized one, or the two are not compiled for the same target.
  | Opt_SimdBaselineSse2 -- ^ Suppress the -march=native that Opt_EnableVectorization would
                         --   otherwise imply, keeping the generated C portable baseline SSE2.
  | Opt_NoGccVectorize -- ^ Disable the C compiler's own automatic vectorization -- both its
                       --   loop vectorizer and its SLP (basic-block) vectorizer -- of the
                       --   generated translation unit: -fno-tree-loop-vectorize
                       --   -fno-tree-slp-vectorize under gcc, -fno-vectorize -fno-slp-vectorize
                       --   under clang. Explicit SIMD intrinsics are unaffected, so this
                       --   isolates Gibbon's own vectorizer from the C compiler's.
  | Opt_NoGccTailCalls -- ^ Disable the C compiler's own sibling/tail-call optimization
                       --   (-fno-optimize-sibling-calls -- the same flag name under both gcc and
                       --   clang) when compiling the generated translation unit, so every call
                       --   in the generated C keeps its own stack frame instead of being turned
                       --   into a jump. Unrelated to Opt_TailCallOptimize, which is Gibbon's own
                       --   IR-level pass for marking Gibbon-level calls as tail calls; this flag
                       --   only affects what the C compiler's backend does with the resulting C
                       --   code. Applies only to the generated translation unit, not the RTS.
  deriving (Show,Read,Eq,Ord)

-- | Exactly like GHC's ddump flags.
data DebugFlag
  = Opt_D_Dump_Repair
  | Opt_D_Dump_ParAlloc
  | Opt_D_DumpToFile
  | Opt_D_Dump_Hs
  deriving (Show, Read, Eq, Ord)

-- Coming soon ...
-- data WarningFlag

data DynFlags = DynFlags { generalFlags :: Set GeneralFlag
                         , debugFlags :: Set DebugFlag }
  deriving (Show,Read,Eq,Ord)

defaultDynFlags :: DynFlags
defaultDynFlags = DynFlags { generalFlags = S.empty
                           , debugFlags = S.empty }

-- | Test whether a 'GeneralFlag' is set
gopt :: GeneralFlag -> DynFlags -> Bool
gopt f dflags  = f `S.member` generalFlags dflags

gopt_set :: GeneralFlag -> DynFlags -> DynFlags
gopt_set f dflags = dflags { generalFlags = S.insert f (generalFlags dflags) }

dopt :: DebugFlag -> DynFlags -> Bool
dopt f dflags = f `S.member` debugFlags dflags

dopt_set :: DebugFlag -> DynFlags -> DynFlags
dopt_set f dflags = dflags { debugFlags = S.insert f (debugFlags dflags) }

dynflagsParser :: Parser DynFlags
dynflagsParser = DynFlags <$> (S.fromList <$> many gflagsParser) <*> (S.fromList <$> many dflagsParser)
  where
    gflagsParser :: Parser GeneralFlag
    gflagsParser = -- Default Opt_Gibbon2
                   flag' Opt_Gibbon1 (long "gibbon1" <>
                                      help "Gibbon1 mode") <|>
                   -- Default Opt_RemoveCopies
                   flag' Opt_No_RemoveCopies (long "no-rcopies" <>
                                              long "no-indirections" <>
                                              help "Calls to copy functions are *not* converted to indirections") <|>
                   -- Default Opt_InfiniteRegions
                   flag' Opt_BigInfiniteRegions (long "biginf" <>
                                                 help "Use big infinite regions") <|>
                   flag' Opt_BenchPrint (long "bench-print" <>
                                         help "Print the output of the benchmarked function, rather than #t") <|>
                   flag' Opt_Packed (short 'p' <>
                                     long "packed" <>
                                     help "Enable packed tree representation in C backend") <|>
                   flag' Opt_Pointer (long "pointer" <>
                                      help "Enable pointer-based trees in C backend (default)") <|>
                   flag' Opt_BumpAlloc (long "bumpalloc" <>
                                        help "Use BUMPALLOC mode in generated C code.  Only affects --pointer") <|>
                   flag' Opt_Warnc (short 'w' <>
                                    long "warnc" <>
                                    help "Show warnings from C compiler, normally suppressed") <|>
                   flag' Opt_DisableGC (long "no-gc" <>
                                        help "Disable the garbage collector (don't use -g when using this flag).") <|>
                   flag' Opt_No_PureAnnot (long "no-pure-annot" <>
                                           help "Don't use 'pure' annotations (a GCC optimization).") <|>
                   flag' Opt_Fusion (long "fusion" <>
                                     help "Enable fusion.") <|>
                   flag' Opt_Parallel (long "parallel" <> help "Enable parallelism") <|>
                   flag' Opt_RegionOnSpawn (long "region-on-spawn" <> help "Allocate into fresh regions for every spawn, not steal.") <|>
                   flag' Opt_GhcTc (long "ghc-tc" <> help "Typecheck with GHC before compiling with Gibbon. Output shown with -v3.") <|>
                   flag' Opt_RelativeOffsets (long "reloffsets" <> help "Enable relative offsets.") <|>
                   flag' Opt_CountParRegions (long "count-par-regions" <> help "Count and print the number of regions allocated for parallelism.") <|>
                   flag' Opt_CountAllRegions (long "count-all-regions" <> help "Count and print the number of all the regions allocated.") <|>
                   flag' Opt_RtsDebug (long "debug-rts" <> help "Compile the RTS in debugging mode.") <|>
                   flag' Opt_PrintGcStats (long "print-gc-stats" <> short 'S' <> help "Record and print GC statistics.") <|>
                   flag' Opt_GenGc (long "gen-gc" <> help "Use the new generational GC.") <|>
                   flag' Opt_ReclaimIterateRegions (long "reclaim-iterate-regions" <>
                                         help "Free the region chunks each --iterate benchmark iteration grew, instead of stranding them. Peak memory becomes flat in the iteration count rather than linear (measured 2.98GB -> 224MB at 10M elements over 31 iterations). Iterations also get faster, because the un-fixed loop made the kernel supply fresh zeroed pages for memory it had leaked; that cost was the artifact.") <|>
                   flag' Opt_NoEagerPromote (long "no-eager-promote" <> help "Disable eager promotion.") <|>
                   flag' Opt_SimpleWriteBarrier (long "simple-write-barrier" <> help "Disables eliminate-indirection-chains optimization.") <|>
                   flag' Opt_No_RAN (long "no-ran" <>
                                         help "Don't use RAN pointers, instead, use extra traversals.") <|>
                   flag' Opt_UseMutableCursors (long "use-mutable-cursors" <> help "Use Mutable Cursors Instead of Immutable Cursors.") <|>
                   flag' Opt_MutableCursorsNonRec (long "opt-mutable-cursors-nonrec" <>
                                                  help ("Non-recursive SoA functions that only read packed values do not " ++
                                                        "return their end-of-input-region cursors. Requires --use-mutable-cursors.")) <|>
                   flag' Opt_TailCallOptimize (long "tail-call-optimize" <> help "Run the oprimization pass to optimize functions that are tail recursive.") <|>
                   flag' Opt_StoreScalarFieldCounts (long "store-scalar-field-counts" <>
                                                  help "Store scalar-count footer metadata for SoA functions annotated with OPT:StoreScalarCounts.") <|>
                   flag' Opt_DeferScalarCounts (long "defer-scalar-counts" <>
                                                  help ("Maintain scalar-count footers with a deferred per-buffer counter rather " ++
                                                        "than a per-element bump. Requires --store-scalar-field-counts; " ++
                                                        "incompatible with --gen-gc.")) <|>
                   flag' Opt_ScalarCountDiff (long "scalar-counts-diff" <>
                                                  help ("Run the per-element bump and the deferred counter together and abort if " ++
                                                        "any flush disagrees. Implies --defer-scalar-counts.")) <|>
                   flag' Opt_EnableLoopification (long "opt-loopification" <>
                                                    help ("Loopify map-like traversals annotated OPT:MayVectorize (or, with " ++
                                                          "--auto-loopification, structurally inferred candidates). AoS maps get a flat " ++
                                                          "cursor loop; SoA maps get counted per-buffer loops, which additionally " ++
                                                          "require --store-scalar-field-counts (a compile error if omitted and an SoA " ++
                                                          "candidate exists). OPT:MayVectorize is only a promise the compiler is free to " ++
                                                          "decline (parent-child dependency, unsupported ABI shape, ...); this flag alone " ++
                                                          "does not guarantee a given function is actually rewritten.")) <|>
                   flag' Opt_AutoLoopification (long "auto-loopification" <>
                                                  help "Infer map-like traversal candidates for loopification instead of requiring OPT:MayVectorize annotations. Still rejects parent-child dependencies and unsupported traversal shapes.") <|>
                   flag' Opt_LoopificationReport (long "loopification-report" <>
                                                    help ("Print one line per function for each loopification pass: whether it " ++
                                                          "was rewritten, or the specific reason it was declined. Reports only; " ++
                                                          "turns no optimisation on.")) <|>
                   flag' Opt_EnableLoopFusion (long "opt-loop-fusion" <>
                                                 help ("Fuse the per-buffer loops loopification produced for fully factored SoA " ++
                                                       "scalar-buffer traversals. Requires --opt-loopification or " ++
                                                       "--auto-loopification (compile error otherwise): there is nothing to fuse " ++
                                                       "without it.")) <|>
                   flag' Opt_EnableSelectiveBufferSharing (long "opt-selective-buffer-sharing" <>
                                                           help ("Share unchanged fully factored SoA buffers across the loops " ++
                                                                 "loopification produced. Requires --opt-loopification or " ++
                                                                 "--auto-loopification (compile error otherwise): there is nothing " ++
                                                                 "loopified to share buffers from without it.")) <|>
                   flag' Opt_EnableVectorization (long "opt-vectorization" <>
                                                   help ("Vectorize (SSE2) the fully factored SoA scalar-buffer loops " ++
                                                         "loopification produced. Requires --opt-loopification or " ++
                                                         "--auto-loopification (compile error otherwise): there are no loops " ++
                                                         "to vectorize without it.")) <|>
                   flag' Opt_SimdW64Multiply (long "simd-w64-multiply" <>
                                    help ("Let the vectorizer use the emulated 64-bit packed " ++
                                          "multiply. It is correct SIMD -- three packed 32x32->64 " ++
                                          "multiplies plus two shifts and two adds, all in registers " ++
                                          "-- but seven instructions for two lanes lose to one imul " ++
                                          "per lane, so it is refused by default. Enable it to measure " ++
                                          "that loss; it makes W64 multiply-heavy loops slower.")) <|>
                   flag' Opt_Sse41 (long "sse4.1" <>
                                    long "gibbon-sse41" <>
                                    help "Compile generated C with -msse4.1 (default: off, baseline SSE2).") <|>
                   option (eitherReader parseSimdIsaFlag)
                          (long "simd-isa" <> metavar "ISA" <>
                           help ("SIMD instruction set for BOTH Gibbon's vectorizer and the C " ++
                                 "compiler: sse2 (128-bit registers, no -m flag -- the x86-64 " ++
                                 "baseline), avx2 (256-bit, -mavx2), or native (256-bit for " ++
                                 "Gibbon, -march=native for the C compiler). Defaults to avx2 " ++
                                 "when --opt-vectorization is given and sse2 otherwise. Pass the " ++
                                 "SAME value to every configuration being compared, or the " ++
                                 "comparison is not like-for-like.")) <|>
                   flag' Opt_MarchNative (long "march-native" <>
                                    help ("Compile generated C with -march=native, selecting the best SIMD " ++
                                          "instructions this machine has. Implied by --opt-vectorization " ++
                                          "unless --simd-baseline-sse2 is given. Pass it to a non-vectorized " ++
                                          "build as well when comparing the two, so both target the same ISA.")) <|>
                   flag' Opt_SimdBaselineSse2 (long "simd-baseline-sse2" <>
                                    help ("Keep generated C at portable baseline SSE2: suppresses the " ++
                                          "-march=native that --opt-vectorization otherwise implies.")) <|>
                   flag' Opt_NoGccVectorize (long "no-gcc-vectorize" <>
                                    help ("Disable the C compiler's own automatic vectorization -- both loop and SLP " ++
                                          "(basic-block) vectorization -- of the generated translation unit: " ++
                                          "-fno-tree-loop-vectorize -fno-tree-slp-vectorize under gcc, " ++
                                          "-fno-vectorize -fno-slp-vectorize under clang. Explicit SIMD intrinsics " ++
                                          "are unaffected, so this isolates Gibbon's own vectorizer from the C " ++
                                          "compiler's. Applies only to the generated translation unit, not the RTS.")) <|>
                   flag' Opt_NoGccTailCalls (long "no-gcc-tail-calls" <>
                                    help ("Disable the C compiler's own sibling/tail-call optimization " ++
                                          "(-fno-optimize-sibling-calls, the same flag under both gcc and clang) " ++
                                          "on the generated translation unit, so every call keeps its own stack " ++
                                          "frame instead of being turned into a jump. Unrelated to " ++
                                          "--tail-call-optimize, which is Gibbon's own IR-level pass, not a C " ++
                                          "compiler backend setting. Applies only to the generated translation " ++
                                          "unit, not the RTS.")) <|>
                   flag' Opt_PapiInstrumentation (long "enable-papi" <> help "Enable instrumentation using papi, extends the iterate timing function." ) <|>
                   flag' Opt_PapiNativeInstrumentation (long "enable-papi-native" <> help "Enable PAPI native-event instrumentation in iterate timing (uses EventSet API).")
    dflagsParser :: Parser DebugFlag
    dflagsParser = flag' Opt_D_Dump_Repair (long "ddump-repair" <>
                                            help "Dump some information while running RepairProgram") <|>
                   flag' Opt_D_Dump_ParAlloc (long "ddump-paralloc" <>
                                             help "Dump the AST after ParAlloc") <|>
                   flag' Opt_D_DumpToFile (long "ddump-to-file" <>
                                           help "Dump output to files instead of stdout.") <|>
                   flag' Opt_D_Dump_Hs (long "ddump-hs" <>
                                        help "Dump GHC compliant source code after all the L1 passes are done.")

-- | @--simd-isa@ as a 'GeneralFlag', for the options parser.
parseSimdIsaFlag :: String -> Either String GeneralFlag
parseSimdIsaFlag isaStr = toFlag <$> parseSimdIsa isaStr
  where
    toFlag SimdSse2 = Opt_SimdIsaSse2
    toFlag SimdSse41 = Opt_SimdIsaSse41
    toFlag SimdAvx2 = Opt_SimdIsaAvx2
    toFlag SimdNative = Opt_SimdIsaNative

-- | Which SIMD instruction set a compilation targets.
--
-- @SimdNative@ gives Gibbon's own vectorizer the same 256-bit registers as
-- @SimdAvx2@ -- there is no 512-bit helper set -- while handing the C compiler
-- @-march=native@.  On a machine with AVX-512 that lets the C compiler's
-- auto-vectorizer go wider than Gibbon's vectorizer can, so @avx2@ is the
-- value to use when the point is to compare the two.
data SimdIsa = SimdSse2 | SimdSse41 | SimdAvx2 | SimdNative
  deriving (Show, Read, Eq, Ord, Enum, Bounded)

-- | Parse a @--simd-isa@ value.  Exact spellings only; anything else is
-- rejected with an actionable message rather than silently defaulting.
parseSimdIsa :: String -> Either String SimdIsa
parseSimdIsa s =
  case s of
    "sse2"   -> Right SimdSse2
    "sse4.1" -> Right SimdSse41
    "avx2"   -> Right SimdAvx2
    "native" -> Right SimdNative
    _ -> Left $ "invalid --simd-isa value " ++ show s ++
                "; must be one of: sse2, sse4.1, avx2, native"

-- | Inverse of 'parseSimdIsa', for captions and provenance strings.
simdIsaName :: SimdIsa -> String
simdIsaName SimdSse2 = "sse2"
simdIsaName SimdSse41 = "sse4.1"
simdIsaName SimdAvx2 = "avx2"
simdIsaName SimdNative = "native"

-- | The instruction set this compilation targets.
--
-- An explicit @--simd-isa@ always wins.  The legacy spellings
-- @--simd-baseline-sse2@ and @--march-native@ are kept as aliases for
-- @sse2@ and @native@.  Failing all of those, asking for Gibbon's vectorizer
-- means asking for the widest registers it can emit, and a build that is not
-- vectorizing stays on the portable baseline.
simdIsaOf :: DynFlags -> SimdIsa
simdIsaOf = fst . simdIsaWithReason

-- | 'simdIsaOf' together with the flag that chose it, so a diagnostic naming
-- the flag cannot name a different one from the selection.
simdIsaWithReason :: DynFlags -> (SimdIsa, String)
simdIsaWithReason dflags = withSse41 (baseIsa dflags)
  where
    -- @--sse4.1@ names a capability, not a register width, so it raises the
    -- 128-bit tier and leaves a wider selection alone.  Gibbon emits a
    -- different multiply sequence for it, so it has to be part of the ISA the
    -- backend reads rather than a separate flag only the C command line sees.
    withSse41 (isa, why)
      | isa == SimdSse2, gopt Opt_Sse41 dflags = (SimdSse41, "--sse4.1")
      | otherwise = (isa, why)

baseIsa :: DynFlags -> (SimdIsa, String)
baseIsa dflags
  | gopt Opt_SimdIsaSse2 dflags = (SimdSse2, "--simd-isa=sse2")
  | gopt Opt_SimdIsaSse41 dflags = (SimdSse41, "--simd-isa=sse4.1")
  | gopt Opt_SimdIsaAvx2 dflags = (SimdAvx2, "--simd-isa=avx2")
  | gopt Opt_SimdIsaNative dflags = (SimdNative, "--simd-isa=native")
  | gopt Opt_SimdBaselineSse2 dflags = (SimdSse2, "--simd-baseline-sse2")
  | gopt Opt_MarchNative dflags = (SimdNative, "--march-native")
  | gopt Opt_EnableVectorization dflags = (SimdAvx2, "--opt-vectorization")
  | otherwise = (SimdSse2, "the default")

-- | Width in bytes of the SIMD register Gibbon's own vectorizer targets.
simdIsaRegisterBytes :: SimdIsa -> Int
simdIsaRegisterBytes SimdSse2 = 16
simdIsaRegisterBytes SimdSse41 = 16
simdIsaRegisterBytes SimdAvx2 = 32
simdIsaRegisterBytes SimdNative = 32

-- | The C compiler flags that put the C compiler on the SAME instruction set.
--
-- @sse2@ emits nothing: SSE2 is the x86-64 baseline, so the default target
-- already is exactly it.  Measured on this machine, @-O3@ alone auto-vectorizes
-- to 128-bit @paddd@\/@movdqa@ with no @ymm@ register in sight, while
-- @-mavx2@ and @-march=native@ both reach 256-bit @vpaddd@ on @ymm@.  (@-mavx@
-- is NOT enough: AVX1 has no 256-bit integer operations.)
simdIsaCcFlags :: SimdIsa -> String
simdIsaCcFlags SimdSse2 = ""
simdIsaCcFlags SimdSse41 = " -msse4.1 "
simdIsaCcFlags SimdAvx2 = " -mavx2 "
simdIsaCcFlags SimdNative = " -march=native "

-- | The @__builtin_cpu_supports@ feature a binary compiled for this ISA needs
-- at run time, or 'Nothing' when the x86-64 baseline already provides it.
--
-- @native@ compiles for the BUILD machine, whose full instruction set cannot
-- be named here; AVX2 is the part of it Gibbon's own vectorizer emits, so that
-- is what gets checked.
simdIsaCpuFeature :: SimdIsa -> Maybe String
simdIsaCpuFeature SimdSse2 = Nothing
simdIsaCpuFeature SimdSse41 = Just "sse4.1"
simdIsaCpuFeature SimdAvx2 = Just "avx2"
simdIsaCpuFeature SimdNative = Just "avx2"
