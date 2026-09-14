-- | Conservative loopification for `OPT:MayVectorize` traversals over
-- fully-factored SoA layouts.  A structural nano-pass: recursion is removed
-- only when a simple buffer-local plan can be extracted from the cursorized L3
-- body.  Any unmet invariant leaves the function unchanged.
--
-- Activation:
--
-- * Requires `--opt-loopification` plus `--store-scalar-field-counts`; SoA loop
--   bounds come from scalar-count footers, so the former without the latter is
--   a hard error whenever an SoA candidate exists.  (Pure AoS has nothing here
--   to loopify; see `Gibbon.Passes.LoopifyFlatTraversals`.)
-- * The function must carry `OPT:MayVectorize`, or `--auto-loopification` must
--   be set.  Automatic mode skips compiler-generated helpers (`_copy_*`,
--   `_print_*`, `_traverse_*`, `_unpack_*`).
-- * The annotation is a promise that recursive calls are independent, but a
--   syntactic check still rejects loopification when a value derived from a
--   self-call feeds a parent scalar write, tag write, scrutinee or conditional.
-- * The cursor ABI is inferred from arguments: four cursor arrays of the SoA
--   length (input ends, output ends, output cursors, input cursors).  Extra
--   arguments are loop-invariant scalars.  Buffer 0 is the tag stream; scalar
--   buffers follow constructor fields in `DDef` order, skipping packed fields.
--
-- Scalar plans:
--
-- * Each branch writes each scalar buffer at most once, to the buffer for that
--   constructor and field, with a matching scalar type.
-- * Update expressions must be pure and mention only scalar reads from the same
--   constructor instance or loop-invariant arguments; cross-constructor scalar
--   dependencies are rejected.
-- * Unmentioned buffers are identity-copied, leaving selective buffer sharing
--   to decide which can be shared.
-- * A scalar conditional is accepted only when both branches write the same
--   buffer set; it lowers to unit-valued control flow, since `ForE` and
--   `WhileCursor` bodies are unit tails.
--
-- Chunks and footers:
--
-- * Emits one outer chunk loop and one inner counted `ForE` per buffer.  The
--   first chunk count comes from the end-of-region footer, later counts from
--   the footer at the preceding redirection boundary, matching the RTS cyclic
--   encoding.  `LoopifiedTraversalFusion` may fuse the remainder afterwards.
-- * Tags are copied verbatim from input to output, so `extractBranchPlans`
--   refuses any branch writing a tag other than its own.  Every branch body is
--   scanned against a whitelist (`scanBranchBody`); anything the plan cannot
--   reproduce -- another call, an indirection or tagged-cursor write, a packed
--   `MemCpy`, an arena/region operation -- bails out to the recursive body
--   rather than dropping the effect.
-- * An untouched footer reads back as 0, indistinguishable from an empty chunk,
--   so consuming absent counts would silently yield empty output.
--   `countGuaranteedTyCons` therefore refuses to loopify over a type unless
--   every user-written producer of it establishes counts.
-- * A scalar update depending on another buffer gets its own cursor anchored at
--   the original input array, advanced in lock-step across redirection
--   boundaries.  It must not reuse that buffer's main cursor, which its own
--   loop may already have consumed.
-- * A loopified map is itself a builder, so it writes scalar-count metadata for
--   every output buffer including the tag stream.  Shape is preserved, so
--   output chunk counts equal input counts and the footer is set once per chunk
--   rather than bumped per element.
--
-- Limitations: scalar loops only (SIMD is `VectorizeTraversals`); the accepted
-- scalar language is variables, literals, projections, primitive scalar
-- operations, and the conditional above.
module Gibbon.Passes.LoopifyTraversals
  ( loopifyTraversals
  , LoopifyCandidate(..)
  , TraversalPlan(..)
  , ScalarBufferPlan(..)
  , loopifyCandidateInfo
  , loopifyCandidateInfoWith
  , collectMentionedDataCons
  , hasParentChildDependency
  , isGeneratedPackedHelper
  -- Shared with 'LoopifyFlatTraversals': which formals the recursion really
  -- leaves alone.  Both passes read non-cursor arguments once at function
  -- entry, so both need the same answer.
  , trulyInvariantArgs
  -- Shared with 'LoopifyFlatTraversals': whether the program can create an
  -- indirection node at all.  Neither loop emitter inspects tags.
  , programWritesIndirections
  -- Exported for tests: the count-availability gate and the
  -- "which constructors does this expression materialize" helper it rests on.
  , countGuaranteedTyCons
  -- Exported for tests: the SoA buffer list, which must agree with the layout
  -- 'InferLocations' chose and with the cursor array length in the types.
  , ScalarBufferSpec(..)
  , scalarBufferSpecs
  , writtenDataCons
  , unattributedPackedTyCons
  -- The report's elaboration of a counts-gate rejection.  Exported so a test
  -- can pin it to 'countGuaranteedTyCons' rather than let the two drift.
  , CountsGateReason(..)
  , countsGateReason
  -- The constructor-key encoder shared with 'LoopifiedTraversalFusion'.
  -- Exported so its injectivity -- a correctness obligation, see the Note on
  -- it -- is tested against the real function rather than a copy.
  , sanitizeLoopName
  -- The scalar-expression grammar and its effect classification.  Exported so
  -- the vectorizer's administrative-let transparency uses the SAME rule the
  -- loopifier admitted the expression under, rather than a second, drifting copy.
  , EffectClass(..)
  , primEffectClass
  , classifyScalarShape
  , scalarExprClass
  -- The one answer to "would this be rewritten, and if not why not".  Shared
  -- with the vectorizer's flag check and the loopification report so neither
  -- re-derives it.
  , SoaDecline(..)
  , soaDeclineReason
  , tyConHasRanNodes
  , soaLoopifyLegality
  , soaLoopifyOutcome
  -- Shared with the AoS pass so both reports print the same way.
  , loopificationReport
  -- The names emitted loops give their per-buffer bindings, and the matchers
  -- that read them back.  Exported so 'Gibbon.Passes.SelectiveBufferSharing'
  -- names them the same way this module spells them; see Note [The loop buffer
  -- name contract].
  , LoopBufferSuffix(..)
  , LoopBufferKey
  , loopBufferIx
  , loopBufferKey
  , loopBufferSeed
  , isLoopBufferName
  , isOwnLoopBufferName
  ) where

import Control.Monad (foldM, guard)
import Data.Char (isAlphaNum, isDigit, ord)
import Data.Either (isRight)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.Language
import Gibbon.L3.Syntax
import Gibbon.L3.Abi ( abiCursorArrayAt, abiUniquePosition )
import Gibbon.L3.Traverse (extExps)
import Gibbon.Passes.InferLocations (filterRanDatacons)
import Gibbon.Passes.ScalarCountPropagation (countPropagatedProducers)

data LoopifyCandidate = LoopifyCandidate
  { lcFunName :: Var
  , lcTyCon :: TyCon
  , lcDataCons :: [DataCon]
  }
  deriving (Eq, Ord, Show)

data TraversalPlan = TraversalPlan
  { tpABI :: LoopifyABI
  , tpScalarPlans :: [ScalarBufferPlan]
  }
  deriving (Eq, Ord, Show)

data ScalarBufferSpec = ScalarBufferSpec
  { sbsBufIx :: Int
  , sbsDCon :: DataCon
  , sbsFieldIdx :: Int
  , sbsTy :: Ty3
  }
  deriving (Eq, Ord, Show)

data ScalarBufferPlan = ScalarBufferPlan
  { sbpBufIx :: Int
  , sbpDCon :: DataCon
  , sbpFieldIdx :: Int
  , sbpTy :: Ty3
  , sbpScalar :: Scalar
  , sbpOp :: ScalarBufferOp
  }
  deriving (Eq, Ord, Show)

data ScalarBufferOp
  = ScalarCopy
  | ScalarExpr Exp3 (M.Map Var ScalarInputInfo)
  deriving (Eq, Ord, Show)

data BufferRole
  = InputBuf Int
  | OutputBuf Int
  deriving (Eq, Ord, Show)

data ScalarInputInfo = ScalarInputInfo
  { siiScalar :: Scalar
  , siiBufIx :: Int
  }
  deriving (Eq, Ord, Show)

data LoopifyABI = LoopifyABI
  { abiArrLen :: Int
  , abiInEnds :: Var
  , abiOutEnds :: Var
  , abiOutCurs :: Var
  , abiInCurs :: Var
  , abiLoopInvariantArgs :: S.Set Var
  }
  deriving (Eq, Ord, Show)

newtype LoopNameSeed = LoopNameSeed
  { loopNameSeedPrefix :: Var
  }
  deriving (Eq, Ord, Show)

freshLoopNameSeed :: Bool -> PassM LoopNameSeed
freshLoopNameSeed isMutable =
  LoopNameSeed <$> gensym (if isMutable then "loop_mut" else "loop")

loopName :: LoopNameSeed -> String -> Var
loopName LoopNameSeed{loopNameSeedPrefix} s =
  loopNameSeedPrefix `varAppend` "_" `varAppend` toVar s

-- | A loop binding whose name another pass matches on.
--
-- Note [The loop buffer name contract]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'Gibbon.Passes.SelectiveBufferSharing' finds the bindings it must rewrite,
-- read or drop by matching the names this module gives them.  Spelling both
-- sides as string literals leaves that contract unchecked: renaming a suffix
-- here silently stops the matcher finding anything.  For the bindings sharing
-- must DROP -- the per-chunk cursor and count updates of a buffer that is now
-- an indirection -- finding nothing means leaving them behind.
--
-- So each name crossing that boundary is a constructor, and the renderer below
-- is the only place it becomes a string.  Names no other pass matches on stay
-- strings; 'loopBufferNameLocal' rejects one that collides with a constructor
-- here, so a local name cannot quietly enter the contract either.
data LoopBufferSuffix
  = LbInputEnd
  | LbInLoc
  | LbOutLoc
  | LbOutEndLoc
  | LbCurrentOutEnd
  | LbSetChunkCount
  | LbGrowOut
  | LbReadCur
  | LbWriteCur
  deriving (Eq, Ord, Show, Enum, Bounded)

loopBufferSuffixName :: LoopBufferSuffix -> String
loopBufferSuffixName s =
  case s of
    LbInputEnd -> "input_end"
    LbInLoc -> "in_loc"
    LbOutLoc -> "out_loc"
    LbOutEndLoc -> "out_end_loc"
    LbCurrentOutEnd -> "current_out_end"
    LbSetChunkCount -> "set_chunk_count"
    LbGrowOut -> "grow_out"
    LbReadCur -> "read_cur"
    LbWriteCur -> "write_cur"

-- | The infix carrying a binding's buffer index.
loopBufferIxInfix :: Int -> String
loopBufferIxInfix ix = "_buf" ++ show ix ++ "_"

-- | Name buffer @ix@'s binding for a suffix other passes match on.
loopBufferName :: LoopNameSeed -> Int -> LoopBufferSuffix -> Var
loopBufferName seed ix = loopBufferNameRaw seed ix . loopBufferSuffixName

-- | Name a binding of buffer @ix@ that is private to the emitted loop.
loopBufferNameLocal :: LoopNameSeed -> Int -> String -> Var
loopBufferNameLocal seed ix s
  | s `elem` map loopBufferSuffixName [minBound .. maxBound] =
      error $
        "loopBufferNameLocal: " ++ show s ++ " is matched on by another pass; "
          ++ "see Note [The loop buffer name contract] and use loopBufferName."
  | otherwise = loopBufferNameRaw seed ix s

loopBufferNameRaw :: LoopNameSeed -> Int -> String -> Var
loopBufferNameRaw LoopNameSeed{loopNameSeedPrefix} ix s =
  loopNameSeedPrefix
    `varAppend` toVar (loopBufferIxInfix ix)
    `varAppend` toVar s

-- | Which loop, and which of its buffers, a binding belongs to.
--
-- The buffer index alone does not identify a buffer: two loops in one body
-- both number their buffers from zero, so anything accumulating per-buffer
-- state across a whole function body has to carry the loop as well.
type LoopBufferKey = (String, Int)

loopBufferKey :: Var -> Maybe LoopBufferKey
loopBufferKey v = parseAfterBuf (fromVar v)
  where
    parseAfterBuf s =
      case splitAtBuf "" s of
        Just (seed, rest0) ->
          case L.stripPrefix "_buf" rest0 of
            Just rest ->
              let (digits, afterDigits) = span isDigit rest
               in case afterDigits of
                    '_':_ | not (null digits) -> Just (reverse seed, read digits)
                    _ -> Nothing
            Nothing -> Nothing
        Nothing -> Nothing

    splitAtBuf _ [] = Nothing
    splitAtBuf acc str@('_':'b':'u':'f':_) = Just (acc, str)
    splitAtBuf acc (c:cs) = splitAtBuf (c : acc) cs

-- | The buffer a loop binding belongs to, read back out of its name.
loopBufferIx :: Var -> Maybe Int
loopBufferIx = fmap snd . loopBufferKey

-- | The loop a binding belongs to.
loopBufferSeed :: Var -> Maybe String
loopBufferSeed = fmap fst . loopBufferKey

-- | Does @v@ name some buffer's @s@ binding?
isLoopBufferName :: LoopBufferSuffix -> Var -> Bool
isLoopBufferName s v = ('_' : loopBufferSuffixName s) `L.isSuffixOf` fromVar v

-- | Does @v@ name buffer @ix@'s own @s@ binding?
--
-- Cross-buffer dependency cursors for the same buffer are named
-- @<seed>_buf<ix>_dep<n>_<suffix>@ and are deliberately rejected: they walk a
-- peer buffer's data, so a rewrite keyed on buffer @ix@ must not claim them.
isOwnLoopBufferName :: Int -> LoopBufferSuffix -> Var -> Bool
isOwnLoopBufferName ix s v =
  (loopBufferIxInfix ix ++ loopBufferSuffixName s) `L.isSuffixOf` fromVar v

-- | Encode a data-constructor name so it can be carried inside a generated
-- loop variable's name and recovered later.
--
-- Note [The loop-name constructor key must be injective]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'Gibbon.Passes.LoopifiedTraversalFusion' fuses adjacent chunk loops that
-- agree on the constructor key it parses back out of this name, and the fused
-- loop drives EVERY participating buffer from ONE representative buffer's
-- per-chunk trip count.  That is sound only because two scalar buffers of the
-- same constructor necessarily hold the same number of logical elements in the
-- same physical chunk (one element per occurrence of that constructor, and
-- 'BoundsCheckVector' grows every peer buffer together, so chunk boundaries
-- stay aligned).  It is NOT sound across constructors, whose per-chunk counts
-- are unrelated.
--
-- So this encoding carries a correctness obligation: distinct constructors must
-- get distinct keys.  It previously collapsed every non-alphanumeric character
-- to @'_'@, which is not injective -- @A'@ and @A_@ both became @A_@.  Their
-- two buffers are adjacent (buffer indices are assigned in constructor order,
-- then field order), so the fusion pass merged them and ran the @A_@ loop for
-- the number of @A'@ elements.  Measured on a 40-node list with a 1:3
-- frequency skew: @--opt-loop-fusion@ turned the correct @60810@ into
-- @20403@, silently, in loopify, selective and vectorize alike.  Renaming the
-- constructors to @Ap@/@Aq@ -- same shape, same frequencies -- fused nothing
-- and gave the right answer.
--
-- The encoding below is injective: alphanumerics pass through, @'_'@ doubles,
-- and any other character @c@ becomes @'_' : show (ord c) ++ "_"@.  A decoder
-- can always tell the three cases apart by the character following a @'_'@
-- (@'_'@ itself, or a digit).  The output stays a legal C identifier tail, and
-- purely alphanumeric constructor names -- which is every constructor in the
-- example tree -- encode to themselves, so no existing loop name changes.
sanitizeLoopName :: String -> String
sanitizeLoopName = concatMap esc
  where
    esc c
      | isAlphaNum c = [c]
      | c == '_'     = "__"
      | otherwise    = '_' : show (ord c) ++ "_"

loopifyTraversals :: Prog3 -> PassM Prog3
loopifyTraversals prog@Prog{ddefs, fundefs} = do
  dflags <- getDynFlags
  let loopificationRequested = gopt Opt_EnableLoopification dflags
      storeScalarCountsOn = gopt Opt_StoreScalarFieldCounts dflags
      auto = gopt Opt_AutoLoopification dflags
      report = gopt Opt_LoopificationReport dflags
      say lns x = loopificationReport report "SoA" lns x
  if not loopificationRequested
    then pure $ say ["--opt-loopification is off; the pass did nothing"] prog
    -- The emitted per-buffer loops inspect no tags, so a single indirection
    -- node landing mid-chunk would desynchronise every scalar buffer for the
    -- rest of that chunk.  Refuse the whole program rather than emit a loop
    -- that cannot survive one.  See 'programWritesIndirections'.
    else if programWritesIndirections prog
    then pure $ say ["the program writes indirections; no function is loopified"] prog
    else if storeScalarCountsOn
    then do
      let countedTyCons = countGuaranteedTyCons auto prog
      results <- mapM (rewriteFun False auto countedTyCons ddefs) (M.elems fundefs)
      let fds' = map fst results
          lns = [ soaReportLine auto prog fn outcome | (fn, outcome) <- results ]
      pure $ say lns $
        prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }
    -- --opt-loopification was requested without --store-scalar-field-counts.
    -- Only a real misconfiguration if a function would ACTUALLY be rewritten
    -- once the flag is supplied.  Nomination is not enough: a function can
    -- carry OPT:MayVectorize, be a FullyFactored target, and still be declined
    -- by the legality scan, in which case supplying the flag changes nothing
    -- and naming it in an error is a false alarm.  A pure-AoS program has
    -- nothing SoA to loopify at all (it goes through 'loopifyFlatTraversals',
    -- which has no scalar-count-footer dependency) and stays a quiet no-op.
    --
    -- The counts gate is consulted too, even though the flag is off:
    -- 'countGuaranteedTyCons' reads `OPT:StoreScalarCounts` annotations and
    -- the shape of the program, not the flag, so it gives the same answer
    -- either way.  Asking the whole question is what makes the error's advice
    -- true -- a function the gate would decline is not one that supplying the
    -- flag would loopify.
    else
      let countedTyCons = countGuaranteedTyCons auto prog
          soaCandidates =
            [ funName fn
            | fn <- M.elems fundefs
            , isRight (soaLoopifyOutcome auto countedTyCons ddefs fn)
            ]
      in case L.sortOn fromVar soaCandidates of
        [] -> pure prog
        (f0 : _) -> error $
          "loopifyTraversals: --opt-loopification is enabled and " ++
          show f0 ++ " (an OPT:MayVectorize-annotated or auto-inferred SoA " ++
          "map) would be loopified, but --store-scalar-field-counts " ++
          "was not passed.\nSoA loopification derives its loop trip counts " ++
          "from scalar-count footer metadata, which only exists when " ++
          "--store-scalar-field-counts is enabled.\nAdd --store-scalar-field-counts " ++
          "to the compile command."

-- | The rewritten (or unchanged) function, paired with what was decided about
-- it, for @--loopification-report@.
rewriteFun :: Bool -> Bool -> S.Set TyCon -> DDefs Ty3 -> FunDef3
           -> PassM (FunDef3, Either SoaDecline ())
rewriteFun fuseScalarLoops auto countedTyCons ddefs fn =
  case soaLoopifyOutcome auto countedTyCons ddefs fn of
    Left d -> pure (fn, Left d)
    Right (_cand, plan) -> do
      mbody <- loopifyFastPath fuseScalarLoops plan fn
      case mbody of
        -- 'fastPathApplies' already agreed the shape is emittable, so this
        -- arm is unreachable; keeping the function unchanged is the safe
        -- reading if the two ever disagree.
        Nothing -> pure (fn, Left SoaAbiMismatch)
        Just body' -> pure (stampLoopified (fn { funBody = body' }), Right ())

-- | One report line for one function.
soaReportLine :: Bool -> Prog3 -> FunDef3 -> Either SoaDecline () -> String
soaReportLine auto prog fn outcome =
  fromVar (funName fn) ++ ": " ++
  case outcome of
    Right () -> "loopified"
    Left (SoaCountsUnavailable tycon) ->
      "declined: " ++ soaDeclineReason (SoaCountsUnavailable tycon) ++
      case countsGateReason auto prog tycon of
        Just r -> " -- " ++ countsGateReasonText tycon r
        Nothing -> ""
    Left d -> "declined: " ++ soaDeclineReason d

-- | @--loopification-report@: one line per function, rewritten or declined.
-- Reporting only; it turns no optimisation on, and a run that reports nothing
-- rewritten proves nothing on its own.
loopificationReport :: Bool -> String -> [String] -> a -> a
loopificationReport False _ _ x = x
loopificationReport True pass lns x =
  dbgTraceIt (unlines (("loopification report (" ++ pass ++ " pass):")
                       : map ("  " ++) lns)) x

-- | Types for which scalar-count footer metadata is guaranteed to be present
-- on every value a loopified traversal could be handed.
--
-- The previous rule only asked whether *some* function in the program carried
-- `OPT:StoreScalarCounts` for the type, and explicitly annotated
-- `OPT:MayVectorize` functions skipped even that.  That is far too weak: any
-- other function in the program that materializes a fresh value of the same
-- type without establishing counts can feed the loopified traversal, whose
-- footer reads then return 0 and whose loops silently write nothing.
--
-- The rule here is:
--
--   * at least one producer establishes counts from scratch
--     (`OPT:StoreScalarCounts`), and
--   * every other user-written producer of the type also ends up with valid
--     counts, either because it is itself loopified (loopified maps write
--     output counts once per chunk) or because `ScalarCountPropagation` copies
--     the input's footer chains at all of its call sites.
--
-- Compiler-generated packed helpers (`_copy_*`, `_print_*`, ...) are not
-- treated as producers here; that matches the pre-existing behavior of the
-- pass and is noted as a remaining limitation.
--
-- There is a third clause, for `gibbon_main`.  Main establishes no counts --
-- 'Cursorize.cursorize' cursorizes the main expression with count-bump
-- emission off, and there is no main-expression form of
-- `OPT:StoreScalarCounts` -- so a value materialized there never has valid
-- footers.  What the clause asks is therefore not whether main is a
-- count-establishing producer, which it cannot be, but whether such a value
-- can REACH a traversal that would be loopified over its type.  See
-- 'mainProducedTyCons'.
countGuaranteedTyCons :: Bool -> Prog3 -> S.Set TyCon
countGuaranteedTyCons auto prog@Prog{ddefs, fundefs} =
  S.fromList
    [ tycon
    | tycon <- S.toList allProducedTyCons
    , any (\fd -> establishesFromScratch fd && tycon `S.member` producedBy fd) userFuns
    , all (\fd -> tycon `S.notMember` producedBy fd || countEstablishing fd) userFuns
    , tycon `S.notMember` mainProduced
    ]
  where
    userFuns =
      [ fd | fd <- M.elems fundefs, not (isGeneratedPackedHelper (funName fd)) ]

    propagated = countPropagatedProducers prog

    producedBy FunDef{funBody} = tagWrittenTyCons funBody

    mainProduced = mainProducedTyCons auto prog

    allProducedTyCons = S.unions (map producedBy userFuns)

    establishesFromScratch FunDef{funMeta} = StoreScalarCounts `elem` funOpt funMeta

    -- Note the deliberate lack of circularity here: `wouldLoopify` depends only
    -- on the structural plan extraction, never on this predicate.  If the gate
    -- rejects a type, nothing over that type is loopified and nothing over that
    -- type reads counts, so the (then false) claim that a would-be-loopified
    -- producer writes counts is never relied upon.
    countEstablishing fd =
      establishesFromScratch fd
        || funName fd `S.member` propagated
        || wouldLoopify auto ddefs fd

    -- A type is "produced" here if the expression materializes one of its
    -- constructors OR obtains a whole value of it some other way.  The second
    -- half matters: `readPackedFile` hands back a fully formed packed value
    -- whose scalar-count footers were never established, and it writes no tag
    -- the first half could see, so without this the gate would not learn that
    -- such a value exists.
    tagWrittenTyCons ex =
      S.fromList
        ([ getTyOfDataCon ddefs dcon
         | dcon <- writtenDataCons ex
         , not (isIndirectionTag dcon || isRedirectionTag dcon)
         ] ++ unattributedPackedTyCons ex)

-- | Types whose values `gibbon_main` materializes AND can hand to a traversal
-- that would be loopified over them.
--
-- Every such value has invalid scalar-count footers, because 'Cursorize'
-- cursorizes the main expression with count-bump emission off.  A loopified
-- consumer takes its trip count from those footers with no way to tell "this
-- chunk holds zero elements" from "nobody ever wrote a count here", so it
-- would silently produce an empty value.  Nothing else reads them: a recursive
-- traversal walks tags.
--
-- So the question is reachability, and it is asked in three steps.
--
--   * The value is identified by the cursors a tag of the type is written to
--     in main.  A materialization that cannot be attributed to a cursor -- a
--     'readPackedFile', or a 'DataConE' that reached L3 -- names the type
--     outright, because there is nothing to trace.
--
--   * From those cursors, everything the value could also be named by:
--     backwards to the cursor arrays and regions they were derived from, then
--     forwards to everything derived from THOSE.  Both closures
--     over-approximate, which is the direction that disqualifies more types.
--     'MemCpy' relates its two cursors in both directions.
--
--   * The type is named if any of those variables is an argument of a call in
--     main that can reach a function 'soaLoopifyLegality' accepts over this
--     type.  Reachability is over the whole call graph, so a value passed to a
--     wrapper that eventually calls the traversal is caught too.
--
-- Asking 'soaLoopifyLegality' here is not circular for the same reason
-- 'wouldLoopify' is not: it is the structural legality scan, which never
-- consults the counts gate.
mainProducedTyCons :: Bool -> Prog3 -> S.Set TyCon
mainProducedTyCons auto Prog{ddefs, fundefs, mainExp} =
  case mainExp of
    Nothing -> S.empty
    Just (m, _) ->
      unattributed m `S.union`
      S.fromList [ tycon | tycon <- S.toList (attributed m), reaches m tycon ]
  where
    -- Materializations with no cursor to trace from.
    unattributed m =
      S.fromList
        (unattributedPackedTyCons m ++
         [ getTyOfDataCon ddefs dcon
         | dcon <- dataConEs m
         , not (isIndirectionTag dcon || isRedirectionTag dcon)
         ])

    attributed m =
      S.fromList
        [ getTyOfDataCon ddefs dcon
        | (dcon, _) <- tagWriteCursors m
        , not (isIndirectionTag dcon || isRedirectionTag dcon)
        ]

    reaches m tycon =
      let seeds = S.fromList [ cur | (dcon, cur) <- tagWriteCursors m
                                   , getTyOfDataCon ddefs dcon == tycon ]
          tainted = mainValueVars m seeds
          risky = reachesLoopifiedOver auto ddefs fundefs tycon
       in or [ not (S.null (S.intersection tainted argVars))
             | (callee, argVars) <- callSitesWithArgVars m
             , callee `S.member` risky
             ]

-- | Every variable that could name the same value as one of @seeds@.
--
-- Backwards first -- a tag is written through a cursor indexed out of the
-- cursor array that IS the value -- and then forwards from those roots.  Doing
-- it in that order is what keeps a value materialized later in main from
-- tainting the inputs of a call made earlier.
mainValueVars :: Exp3 -> S.Set Var -> S.Set Var
mainValueVars m seeds = closure forward (closure backward seeds)
  where
    binds = bindDeps m
    copies = memCpyPairs m

    backward s =
      S.unions $
        s : [ deps | (v, deps) <- binds, v `S.member` s ]
          ++ copyEdges s

    forward s =
      S.unions $
        s : [ S.singleton v | (v, deps) <- binds, not (S.null (S.intersection deps s)) ]
          ++ copyEdges s

    copyEdges s =
      [ S.fromList [a, b] | (a, b) <- copies, a `S.member` s || b `S.member` s ]

    closure step = go
      where
        go acc =
          let acc' = step acc
           in if acc' == acc then acc else go acc'

-- | Functions that would be loopified over @tycon@, and every function that
-- can reach one.
reachesLoopifiedOver :: Bool -> DDefs Ty3 -> FunDefs3 -> TyCon -> S.Set Var
reachesLoopifiedOver auto ddefs fundefs tycon = go targets
  where
    targets =
      S.fromList
        [ funName fd
        | fd <- M.elems fundefs
        , Right (cand, _) <- [soaLoopifyLegality auto ddefs fd]
        , lcTyCon cand == tycon
        ]

    callers =
      [ (funName fd, S.fromList (map fst (callSitesWithArgVars (funBody fd))))
      | fd <- M.elems fundefs
      ]

    go acc =
      let acc' = acc `S.union`
                 S.fromList [ f | (f, cs) <- callers
                                , not (S.null (S.intersection cs acc)) ]
       in if acc' == acc then acc else go acc'

-- | The cursor each constructor tag is written to.
--
-- 'writtenDataCons' answers which constructors an expression writes;
-- attributing the write to a cursor is what makes it possible to ask where the
-- value goes.  Reaches extension forms through 'extExps', so a tag write under
-- a form not named here still surfaces.
tagWriteCursors :: Exp3 -> [(DataCon, Var)]
tagWriteCursors = go
  where
    go ex =
      case ex of
        LetE (_, _, _, rhs) bod -> go rhs ++ go bod
        Ext (WriteTag dcon cur) -> [(dcon, cur)]
        Ext (ScalarCountBump dcon curs) -> [ (dcon, cur) | (cur, _) <- curs ]
        Ext ext -> concatMap go (extExps ext)
        _ -> concatMap go (subExps ex)

-- | Constructor applications that reached L3 with no cursor to attribute them
-- to.
dataConEs :: Exp3 -> [DataCon]
dataConEs = go
  where
    go ex =
      case ex of
        DataConE _ dcon args -> dcon : concatMap go args
        Ext ext -> concatMap go (extExps ext)
        _ -> concatMap go (subExps ex)

-- | Every binding, paired with the variables its right-hand side mentions.
bindDeps :: Exp3 -> [(Var, S.Set Var)]
bindDeps = go
  where
    go ex =
      case ex of
        LetE (v, _, _, rhs) bod -> (v, collectVars rhs) : (go rhs ++ go bod)
        Ext ext -> concatMap go (extExps ext)
        _ -> concatMap go (subExps ex)

-- | The cursor pairs a 'MemCpy' relates.  Direction is deliberately ignored:
-- either end naming the value is enough to make the other name it too.
memCpyPairs :: Exp3 -> [(Var, Var)]
memCpyPairs = go
  where
    go ex =
      case ex of
        Ext (MemCpy a b _) -> [(a, b)]
        Ext ext -> concatMap go (extExps ext)
        LetE (_, _, _, rhs) bod -> go rhs ++ go bod
        _ -> concatMap go (subExps ex)

-- | Every call, with the variables its arguments mention.
callSitesWithArgVars :: Exp3 -> [(Var, S.Set Var)]
callSitesWithArgVars = go
  where
    go ex =
      case ex of
        AppE f _ _ args -> (f, S.unions (map collectVars args)) : concatMap go args
        SpawnE f _ args -> (f, S.unions (map collectVars args)) : concatMap go args
        Ext ext -> concatMap go (extExps ext)
        LetE (_, _, _, rhs) bod -> go rhs ++ go bod
        _ -> concatMap go (subExps ex)

-- | The immediate expression children of every 'PreExp' form except 'Ext',
-- which the callers above handle themselves through 'extExps'.  Total, so a
-- new form is a compile error rather than a silently unvisited position.
subExps :: Exp3 -> [Exp3]
subExps ex =
  case ex of
    VarE{} -> []
    LitE{} -> []
    CharE{} -> []
    FloatE{} -> []
    LitSymE{} -> []
    SyncE -> []
    AppE _ _ _ args -> args
    SpawnE _ _ args -> args
    PrimAppE _ args -> args
    LetE (_, _, _, rhs) bod -> [rhs, bod]
    IfE a b c -> [a, b, c]
    MkProdE ls -> ls
    ProjE _ e -> [e]
    CaseE scrt brs -> scrt : [ rhs | (_, _, rhs) <- brs ]
    DataConE _ _ args -> args
    TimeIt e _ _ -> [e]
    WithArenaE _ e -> [e]
    MapE (_, _, rhs) bod -> [rhs, bod]
    FoldE (_, _, r1) (_, _, r2) bod -> [r1, r2, bod]
    Ext _ -> []

-- | Which of 'countGuaranteedTyCons' three conditions a type fails, or
-- 'Nothing' if it passes.  Only the report asks -- the gate itself needs the
-- set, and building the reason per function would recompute
-- 'countPropagatedProducers' once per function.
data CountsGateReason
  = NoScratchProducer
    -- ^ Nothing in the program establishes counts for the type from scratch.
  | ProducerWithoutCounts Var
    -- ^ A producer of the type that neither carries @OPT:StoreScalarCounts@,
    -- nor is itself loopified, nor has counts propagated into it.
  | ProducedInGibbonMain
    -- ^ @gibbon_main@ materializes a constructor of the type directly.  One
    -- such @DataConE@ disables loopification for the type program-wide.
  deriving (Eq, Show)

countsGateReasonText :: TyCon -> CountsGateReason -> String
countsGateReasonText tycon r =
  case r of
    NoScratchProducer ->
      "no producer of " ++ tycon ++ " carries OPT:StoreScalarCounts"
    ProducerWithoutCounts fn ->
      fromVar fn ++ " produces " ++ tycon ++
      " without establishing counts, and is neither loopified nor count-propagated"
    ProducedInGibbonMain ->
      "gibbon_main constructs a " ++ tycon ++ " directly, so counts for it are " ++
      "not guaranteed anywhere in the program"

countsGateReason :: Bool -> Prog3 -> TyCon -> Maybe CountsGateReason
countsGateReason auto prog@Prog{ddefs, fundefs} tycon
  | not (any (\fd -> establishesFromScratch fd && produces fd) userFuns) =
      Just NoScratchProducer
  | (fd : _) <- [ fd | fd <- userFuns, produces fd, not (countEstablishing fd) ] =
      Just (ProducerWithoutCounts (funName fd))
  | tycon `S.member` mainProducedTyCons auto prog =
      Just ProducedInGibbonMain
  | otherwise = Nothing
  where
    userFuns =
      [ fd | fd <- M.elems fundefs, not (isGeneratedPackedHelper (funName fd)) ]
    propagated = countPropagatedProducers prog
    produces fd = tycon `S.member` producedTyCons (funBody fd)
    establishesFromScratch FunDef{funMeta} = StoreScalarCounts `elem` funOpt funMeta
    countEstablishing fd =
      establishesFromScratch fd
        || funName fd `S.member` propagated
        || wouldLoopify auto ddefs fd
    producedTyCons ex =
      S.fromList
        ([ getTyOfDataCon ddefs dcon
         | dcon <- writtenDataCons ex
         , not (isIndirectionTag dcon || isRedirectionTag dcon)
         ] ++ unattributedPackedTyCons ex)

-- | Why the SoA loopifier did not rewrite a function.
--
-- One decision, asked once.  'rewriteFun' acts on it, the missing-flag error
-- selects on it, and @--loopification-report@ prints it; deriving "would this
-- be rewritten?" separately at each of those points is how the three answers
-- drift apart.
data SoaDecline
  = SoaNotCandidate
    -- ^ No @OPT:MayVectorize@ and not inferred, a generated packed helper, or
    -- not a single-tycon traversal over a `FullyFactored` type.
  | SoaRandomAccessNodes TyCon
    -- ^ The type has random-access nodes.  See 'tyConHasRanNodes'.
  | SoaCountsUnavailable TyCon
    -- ^ Legal, but some producer of this type does not establish scalar-count
    -- footers, so the loop's trip counts would not be trustworthy.
  | SoaNoPlan
    -- ^ The legality scan refused: unrecognised cursor ABI, a branch the plan
    -- cannot reproduce, an argument the recursion varies, an indirection.
  | SoaAbiMismatch
    -- ^ A plan was extracted, but the cursor-array arity or the return type is
    -- not one the emitted fast path handles.
  deriving (Eq, Show)

-- | Human-readable, one line, for @--loopification-report@.
soaDeclineReason :: SoaDecline -> String
soaDeclineReason d =
  case d of
    SoaNotCandidate -> "not a candidate (no OPT:MayVectorize, not inferred, or not a fully factored single-type map)"
    SoaRandomAccessNodes tycon ->
      tycon ++ " has random-access nodes, whose cursor array is written inline " ++
      "in the tag buffer; the emitted loops advance by a fixed stride. " ++
      "Compile with --no-ran to loopify this traversal."
    SoaCountsUnavailable tycon -> "scalar-count footers are not guaranteed for " ++ tycon
    SoaNoPlan -> "legality scan refused the traversal shape"
    SoaAbiMismatch -> "cursor-array arity or return type is not a shape the loop emitter handles"

-- | The counts-agnostic half of the decision: is this a candidate whose
-- traversal shape the loop emitter can actually handle?
--
-- Kept separate from 'soaLoopifyOutcome' because 'countGuaranteedTyCons'
-- consumes it, and a loopified map is itself a count-establishing producer --
-- folding the counts gate in here would make that recursive.
soaLoopifyLegality :: Bool -> DDefs Ty3 -> FunDef3 -> Either SoaDecline (LoopifyCandidate, TraversalPlan)
soaLoopifyLegality auto ddefs fn =
  case loopifyCandidateInfoWith auto ddefs fn of
    Nothing -> Left SoaNotCandidate
    Just cand
      | tyConHasRanNodes ddefs (lcTyCon cand) ->
          Left (SoaRandomAccessNodes (lcTyCon cand))
      | otherwise ->
          case extractTraversalPlan ddefs cand fn of
            Nothing -> Left SoaNoPlan
            Just plan
              | fastPathApplies plan fn -> Right (cand, plan)
              | otherwise -> Left SoaAbiMismatch

-- | Does this type have random-access nodes?
--
-- @AddRAN@ replaces a constructor with a @^@ variant that writes the SoA
-- cursor array of its skipped subtree INLINE in the tag buffer, immediately
-- after the tag: @1 + 8 * arrLen@ bytes where every other constructor writes
-- one.  The emitted per-buffer loops read no tags and advance each buffer by a
-- fixed stride, so one such node desynchronises the tag buffer for the rest of
-- the chunk -- the same hazard as an indirection, which
-- 'programWritesIndirections' refuses for the same reason.
tyConHasRanNodes :: DDefs Ty3 -> TyCon -> Bool
tyConHasRanNodes ddefs tycon =
  any (L.isSuffixOf "^" . fst) (dataCons (lookupDDef ddefs tycon))

-- | The whole decision, counts gate included.  'rewriteFun' rewrites exactly
-- when this returns a plan.
soaLoopifyOutcome
  :: Bool -> S.Set TyCon -> DDefs Ty3 -> FunDef3 -> Either SoaDecline (LoopifyCandidate, TraversalPlan)
soaLoopifyOutcome auto countedTyCons ddefs fn = do
  (cand, plan) <- soaLoopifyLegality auto ddefs fn
  -- The generated loop takes its trip count from scalar-count footer metadata
  -- with no way to tell "this chunk really holds zero elements" from "nobody
  -- ever wrote a count here" -- both read back as 0, and the latter silently
  -- produces an empty output value.
  if lcTyCon cand `S.member` countedTyCons
    then Right (cand, plan)
    else Left (SoaCountsUnavailable (lcTyCon cand))

-- | The shapes 'loopifyFastPath' emits a body for.  Asked here so the
-- predicate and the emitter cannot disagree about what is emittable.
fastPathApplies :: TraversalPlan -> FunDef3 -> Bool
fastPathApplies TraversalPlan{tpABI, tpScalarPlans} FunDef{funTy = (_, out)} =
  let arrLen = abiArrLen tpABI
   in arrLen == 1 + length tpScalarPlans
        && (out == loopifiedOutTy arrLen || out == ProdTy [])

-- | Would this function be loopified, ignoring the count-availability gate?
-- A loopified map writes output footer counts once per chunk, so it is itself
-- a count-establishing producer.
wouldLoopify :: Bool -> DDefs Ty3 -> FunDef3 -> Bool
wouldLoopify auto ddefs fn = isRight (soaLoopifyLegality auto ddefs fn)

-- | Type constructors this expression materializes a packed value of WITHOUT
-- writing any tag the compiler can attribute to a producer.
--
-- Today that is `ReadPackedFile`: it yields a complete packed value read from
-- disk, so nothing in the program established its scalar-count footers.  A
-- loopified traversal handed such a value would read untouched footers, get
-- zero, and silently write nothing.  Reporting the type here makes the
-- count-availability gate reject it, so the traversal simply stays recursive.
--
-- This is deliberately a REFUSAL rather than an attempt to synthesize counts:
-- the counts are not recoverable without traversing the value, which is exactly
-- the work loopification is trying to avoid.
unattributedPackedTyCons :: Exp3 -> [TyCon]
unattributedPackedTyCons ex =
  case ex of
    PrimAppE (ReadPackedFile _ tycon _ _) args ->
      tycon : concatMap unattributedPackedTyCons args
    PrimAppE _ args -> concatMap unattributedPackedTyCons args
    AppE _ _ _ args -> concatMap unattributedPackedTyCons args
    SpawnE _ _ args -> concatMap unattributedPackedTyCons args
    LetE (_, _, _, rhs) bod -> unattributedPackedTyCons rhs ++ unattributedPackedTyCons bod
    IfE a b c -> concatMap unattributedPackedTyCons [a, b, c]
    MkProdE ls -> concatMap unattributedPackedTyCons ls
    ProjE _ e -> unattributedPackedTyCons e
    CaseE scrt brs ->
      unattributedPackedTyCons scrt
        ++ concatMap (\(_, _, rhs) -> unattributedPackedTyCons rhs) brs
    DataConE _ _ args -> concatMap unattributedPackedTyCons args
    TimeIt e _ _ -> unattributedPackedTyCons e
    WithArenaE _ e -> unattributedPackedTyCons e
    -- Fails CLOSED via 'extExps': every extension form's expression children
    -- are visited, so a packed value obtained through a form not named above
    -- (a 'RetE', a 'Vec*' node, ...) still surfaces here instead of vanishing.
    Ext ext -> concatMap unattributedPackedTyCons (extExps ext)
    _ -> []

-- | Data constructors whose tag this expression writes.  Unlike
-- `collectMentionedDataCons` this ignores `case` scrutinee patterns, so it
-- reports only constructors the expression actually materializes.
writtenDataCons :: Exp3 -> [DataCon]
writtenDataCons ex =
  case ex of
    AppE _ _ _ args -> concatMap writtenDataCons args
    SpawnE _ _ args -> concatMap writtenDataCons args
    PrimAppE _ args -> concatMap writtenDataCons args
    LetE (_, _, _, rhs) bod -> writtenDataCons rhs ++ writtenDataCons bod
    IfE a b c -> concatMap writtenDataCons [a, b, c]
    MkProdE ls -> concatMap writtenDataCons ls
    ProjE _ e -> writtenDataCons e
    CaseE scrt brs ->
      writtenDataCons scrt ++ concatMap (\(_, _, rhs) -> writtenDataCons rhs) brs
    DataConE _ dcon args -> dcon : concatMap writtenDataCons args
    TimeIt e _ _ -> writtenDataCons e
    WithArenaE _ e -> writtenDataCons e
    MapE (_, _, e1) e2 -> writtenDataCons e1 ++ writtenDataCons e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      concatMap writtenDataCons [e1, e2, e3]
    -- Fails CLOSED via 'extExps' for everything but the two forms that
    -- themselves write a tag: an unlisted form's expression children are
    -- still visited, so a 'DataConE' reachable only through a form not named
    -- above (a 'RetE', a 'Vec*' node, ...) still surfaces here.
    Ext ext ->
      case ext of
        WriteTag dcon _ -> [dcon]
        ScalarCountBump dcon _ -> [dcon]
        _ -> concatMap writtenDataCons (extExps ext)
    _ -> []

loopifyCandidateInfo :: DDefs Ty3 -> FunDef3 -> Maybe LoopifyCandidate
loopifyCandidateInfo = loopifyCandidateInfoWith False

loopifyCandidateInfoWith :: Bool -> DDefs Ty3 -> FunDef3 -> Maybe LoopifyCandidate
loopifyCandidateInfoWith allowInferred ddefs FunDef{funName, funMeta, funBody}
  | not explicitlyAnnotated && not canInfer = Nothing
  | otherwise =
      let dcons = L.nub (collectMentionedDataCons funBody)
          tycons = L.nub (map (getTyOfDataCon ddefs) dcons)
       in case tycons of
            [tycon]
              | memLayout (lookupDDef ddefs tycon) == FullyFactored ->
                  Just LoopifyCandidate
                    { lcFunName = funName
                    , lcTyCon = tycon
                    , lcDataCons = dcons
                    }
            _ -> Nothing
  where
    explicitlyAnnotated = MayVectorize `elem` funOpt funMeta
    canInfer = allowInferred && not (isGeneratedPackedHelper funName)

isGeneratedPackedHelper :: Var -> Bool
isGeneratedPackedHelper v =
  or [ isCopyFunName v
     , isCopySansPtrsFunName v
     , isPrinterName v
     , isTravFunName v
     , isUnpackerName v
     , isRelOffsetsFunName v
     ]

-- | Stamp the INTERNAL 'Loopified' marker (never 'MayVectorize' -- the
-- user's own annotation is never mutated) onto a function this pass just
-- successfully rewrote. Downstream passes read 'Loopified', not
-- 'MayVectorize', to decide whether a function was actually loopified.
stampLoopified :: FunDef3 -> FunDef3
stampLoopified fn@FunDef{funMeta} =
  fn { funMeta = funMeta { funOpt = Loopified : filter (/= Loopified) (funOpt funMeta) } }

extractTraversalPlan :: DDefs Ty3 -> LoopifyCandidate -> FunDef3 -> Maybe TraversalPlan
extractTraversalPlan ddefs LoopifyCandidate{lcFunName, lcTyCon} fn@FunDef{funArgs, funBody} = do
  if hasParentChildDependency lcFunName funBody
    then Nothing
    else pure ()
  specs <- scalarBufferSpecs ddefs lcTyCon
  case specs of
    [] -> Nothing
    _ -> pure ()
  (preBinds, _scrt, branches) <- splitTopCase funBody
  let expectedArrLen = 1 + length specs
      trulyInvariant = trulyInvariantArgs lcFunName funArgs funBody
  abi <- loopifyABIFromRoles expectedArrLen (collectVars funBody) trulyInvariant fn
  extractWithABI lcFunName specs preBinds branches abi

extractWithABI
  :: Var
  -> [ScalarBufferSpec]
  -> [(Var, [()], Ty3, Exp3)]
  -> [(DataCon, [(Var, ())], Exp3)]
  -> LoopifyABI
  -> Maybe TraversalPlan
extractWithABI selfName specs preBinds branches abi@LoopifyABI{abiOutCurs, abiInCurs, abiLoopInvariantArgs} = do
  let baseInputArrays = extendCursorArrayAliases (S.singleton abiInCurs) preBinds
      baseOutputArrays = extendCursorArrayAliases (S.singleton abiOutCurs) preBinds
      baseRoles = collectCursorRolesFrom M.empty baseInputArrays baseOutputArrays preBinds
  branchPlanMaps <- mapM (extractBranchPlans selfName specs abiLoopInvariantArgs baseInputArrays baseOutputArrays baseRoles) branches
  merged <- mergeBranchPlanMaps branchPlanMaps
  if M.null merged
    then Nothing
    else pure ()
  let plans = map (\spec -> fromMaybe (identityPlan spec) (M.lookup (sbsBufIx spec) merged)) specs
  pure $ TraversalPlan { tpABI = abi, tpScalarPlans = L.sortOn sbpBufIx plans }

-- | The loop's cursor-array ABI, read off the cursorized calling convention.
--
-- The four arrays are distinguished by the role cursorization recorded, not by
-- argument order.  A function whose convention names more than one array in any
-- role -- a two-packed-input traversal, say -- is declined: there is no single
-- input to walk, and picking one would generate a loop over the wrong value.
loopifyABIFromRoles :: Int -> S.Set Var -> S.Set Var -> FunDef3 -> Maybe LoopifyABI
loopifyABIFromRoles expectedArrLen usedVars trulyInvariant
                    FunDef{funArgs, funTy = (tys, _), funMeta} = do
  roles <- funCursorAbi funMeta
  inEnds <- arrayAt roles AbiInEnd
  outEnds <- arrayAt roles AbiOutEnd
  outCurs <- arrayAt roles AbiOutCur
  inCurs <- arrayAt roles AbiInCur
  -- The emitted loop walks the input through `inCurs` and writes through
  -- `outCurs`; a body that mentions neither is not the traversal shape.
  guard (outCurs `S.member` usedVars)
  guard (inCurs `S.member` usedVars)
  guard (length (L.nub [inEnds, outEnds, outCurs, inCurs]) == 4)
  pure LoopifyABI
    { abiArrLen = expectedArrLen
    , abiInEnds = inEnds
    , abiOutEnds = outEnds
    , abiOutCurs = outCurs
    , abiInCurs = inCurs
    , abiLoopInvariantArgs = S.fromList invariants
    }
  where
    invariants =
      [ v
      | (v, ty) <- zip funArgs tys
      , not (isCursorArrayTy ty)
      , v `S.member` trulyInvariant
      ]

    isCursorArrayTy ty =
      case ty of
        CursorArrayTy{} -> True
        _ -> False

    arrayAt roles role = do
      ix <- abiUniquePosition role roles
      n <- abiCursorArrayAt tys ix
      guard (n == expectedArrLen)
      case drop ix funArgs of
        v : _ -> Just v
        [] -> Nothing

-- | Formals that every self-call passes straight through, as the bare
-- parameter variable and at the same position.
--
-- A loopified traversal reads its non-cursor arguments once, at function
-- entry, and the emitted loop reuses those entry values for every element.
-- That is faithful to the recursion only for an argument the recursion never
-- changes.  An accumulator or a depth counter -- anything a self-call rebinds
-- -- is therefore not loop invariant, and treating it as one silently freezes
-- it at its entry value.  Positions that are not passed as the bare formal
-- drop out here; their uses then stay free, and each pass's own
-- free-variable check refuses the candidate.
--
-- A body with no self-call vacuously satisfies this: nothing varies when
-- nothing recurses.
trulyInvariantArgs :: Var -> [Var] -> Exp3 -> S.Set Var
trulyInvariantArgs selfName formals body =
  S.fromList
    [ v
    | (pos, v) <- zip [0 :: Int ..] formals
    , all (passesThrough pos v) (selfCallArgLists selfName body)
    ]
  where
    passesThrough pos v args =
      length args == length formals
        && case drop pos args of
             VarE v' : _ -> v' == v
             _ -> False

-- | The argument lists of every self-call, ordinary or spawned.
selfCallArgLists :: Var -> Exp3 -> [[Exp3]]
selfCallArgLists selfName body =
  [ args | (fn, args) <- collectCallSites body, fn == selfName ]

-- | Every call site in an expression.  Extension nodes go through the total
-- 'extExps', so a call buried in one is still seen.
collectCallSites :: Exp3 -> [(Var, [Exp3])]
collectCallSites ex =
  case ex of
    AppE fn _ _ args -> (fn, args) : concatMap collectCallSites args
    SpawnE fn _ args -> (fn, args) : concatMap collectCallSites args
    PrimAppE _ args -> concatMap collectCallSites args
    LetE (_, _, _, rhs) bod -> collectCallSites rhs ++ collectCallSites bod
    IfE a b c -> concatMap collectCallSites [a, b, c]
    MkProdE ls -> concatMap collectCallSites ls
    ProjE _ e -> collectCallSites e
    CaseE scrt brs ->
      collectCallSites scrt ++ concatMap (\(_, _, rhs) -> collectCallSites rhs) brs
    DataConE _ _ args -> concatMap collectCallSites args
    TimeIt e _ _ -> collectCallSites e
    WithArenaE _ e -> collectCallSites e
    MapE (_, _, e1) e2 -> collectCallSites e1 ++ collectCallSites e2
    FoldE (_, _, e1) (_, _, e2) e3 -> concatMap collectCallSites [e1, e2, e3]
    Ext ext -> concatMap collectCallSites (extExps ext)
    _ -> []

-- | Can this program write an indirection node anywhere?
--
-- Every cursorized traversal over a packed type carries an INDIRECTION arm in
-- its top-level case, whether or not the program can ever put such a node in
-- the data, so the presence of the ARM says nothing.  What decides the hazard
-- is whether a node can exist at all, and only Cursorize's
-- 'WriteCursorIndirection' / 'IndirectionBarrier' -- or an explicit write of
-- an indirection tag -- can create one.
--
-- Deliberately whole-program and not per-type: an indirection written into
-- one type is evidence the configuration creates them at all, and the loop
-- emitters inspect no tags, so the conservative answer is the safe one.
programWritesIndirections :: Prog3 -> Bool
programWritesIndirections Prog{fundefs, mainExp} =
  any (writesIndirection . funBody) (M.elems fundefs)
    || maybe False (writesIndirection . fst) mainExp

writesIndirection :: Exp3 -> Bool
writesIndirection ex =
  case ex of
    Ext WriteCursorIndirection{} -> True
    Ext IndirectionBarrier{} -> True
    Ext WriteCursorSelectiveIndirection{} -> True
    Ext (WriteTag dcon _) | isIndirectionTag dcon -> True
    DataConE _ dcon args -> isIndirectionTag dcon || any writesIndirection args
    Ext ext -> any writesIndirection (extExps ext)
    AppE _ _ _ args -> any writesIndirection args
    SpawnE _ _ args -> any writesIndirection args
    PrimAppE _ args -> any writesIndirection args
    LetE (_, _, _, rhs) bod -> writesIndirection rhs || writesIndirection bod
    IfE a b c -> any writesIndirection [a, b, c]
    MkProdE ls -> any writesIndirection ls
    ProjE _ e -> writesIndirection e
    CaseE scrt brs ->
      writesIndirection scrt || any (writesIndirection . thd3) brs
    TimeIt e _ _ -> writesIndirection e
    WithArenaE _ e -> writesIndirection e
    MapE (_, _, e1) e2 -> writesIndirection e1 || writesIndirection e2
    FoldE (_, _, e1) (_, _, e2) e3 -> any writesIndirection [e1, e2, e3]
    _ -> False

collectVars :: Exp3 -> S.Set Var
collectVars ex =
  case ex of
    VarE v -> S.singleton v
    LitE{} -> S.empty
    CharE{} -> S.empty
    FloatE{} -> S.empty
    LitSymE{} -> S.empty
    AppE _ _ _ args -> S.unions (map collectVars args)
    PrimAppE _ args -> S.unions (map collectVars args)
    LetE (v, _, _, rhs) bod ->
      S.insert v (collectVars rhs `S.union` collectVars bod)
    IfE a b c ->
      S.unions [collectVars a, collectVars b, collectVars c]
    MkProdE ls -> S.unions (map collectVars ls)
    ProjE _ e -> collectVars e
    CaseE scrt brs ->
      collectVars scrt
        `S.union` S.unions [ S.fromList (map fst vars) `S.union` collectVars rhs
                            | (_, vars, rhs) <- brs
                            ]
    DataConE _ _ args -> S.unions (map collectVars args)
    TimeIt e _ _ -> collectVars e
    WithArenaE _ e -> collectVars e
    SpawnE _ _ args -> S.unions (map collectVars args)
    SyncE -> S.empty
    MapE (v, _, e1) e2 ->
      S.insert v (collectVars e1 `S.union` collectVars e2)
    FoldE (v1, _, e1) (v2, _, e2) e3 ->
      S.insert v1 (S.insert v2 (S.unions [collectVars e1, collectVars e2, collectVars e3]))
    Ext ext ->
      collectExtVars ext

collectExtVars :: E3Ext () Ty3 -> S.Set Var
collectExtVars ext =
  case ext of
    ReadScalar _ cur -> S.singleton cur
    WriteScalar _ cur rhs -> S.insert cur (collectVars rhs)
    ReadTag cur -> S.singleton cur
    WriteTag _ cur -> S.singleton cur
    WriteTagPacked cur rhs -> S.insert cur (collectVars rhs)
    TagCursor cur tag -> S.fromList [cur, tag]
    WriteCursorIndirection cur target end -> S.fromList [cur, target, end]
    WriteCursorSelectiveIndirection cur target end mask ->
      S.fromList [cur, target, end] `S.union` collectVars mask
    UnwrapSelectiveIndirections _ ends curs -> S.fromList [ends, curs]
    WriteTaggedCursor cur rhs -> S.insert cur (collectVars rhs)
    MemCpy src dst _ -> S.fromList [src, dst]
    ReadTaggedCursor cur -> S.singleton cur
    ReadCursor cur -> S.singleton cur
    GrowRegion cur end -> S.fromList [cur, end]
    WriteCursorMutable cur rhs -> S.insert cur (collectVars rhs)
    ReadList cur _ -> S.singleton cur
    WriteList cur rhs _ -> S.insert cur (collectVars rhs)
    ReadVector cur _ -> S.singleton cur
    WriteVector cur rhs _ -> S.insert cur (collectVars rhs)
    MakeCursorArray _ vars -> S.fromList vars
    IndexCursorArray arr _ -> S.singleton arr
    AddCursor cur rhs -> S.insert cur (collectVars rhs)
    BumpCursorMutable cur rhs -> S.insert cur (collectVars rhs)
    AddrOfCursor rhs -> collectVars rhs
    DerefMutCursor cur -> S.singleton cur
    CastPtr cur _ -> S.singleton cur
    SubPtr cur1 cur2 -> S.fromList [cur1, cur2]
    NewBuffer{} -> S.empty
    ScopedBuffer{} -> S.empty
    NewParBuffer{} -> S.empty
    ScopedParBuffer{} -> S.empty
    EndOfBuffer{} -> S.empty
    MMapFileSize cur -> S.singleton cur
    SizeOfPacked cur1 cur2 -> S.fromList [cur1, cur2]
    SizeOfScalar cur -> S.singleton cur
    BoundsCheck _ end cur mb _ ->
      S.fromList [end, cur] `S.union`
        maybe S.empty (\(end', cur') -> S.fromList [end', cur']) mb
    BoundsCheckVector checks ->
      S.unions
        [ S.fromList [endVar, curVar, endVar', curVar']
        | (_, endVar, curVar, (endVar', curVar')) <- checks
        ]
    IndirectionBarrier _ (l1, r1, l2, r2) -> S.fromList [l1, r1, l2, r2]
    BumpArenaRefCount arena end -> S.fromList [arena, end]
    NullCursor -> S.empty
    InitCursor{} -> S.empty
    RetE ls -> S.unions (map collectVars ls)
    GetCilkWorkerNum -> S.empty
    LetAvail _ bod -> collectVars bod
    AllocateTagHere cur _ -> S.singleton cur
    AllocateScalarsHere cur -> S.singleton cur
    StartTagAllocation cur -> S.singleton cur
    EndTagAllocation cur -> S.singleton cur
    StartScalarsAllocation cur -> S.singleton cur
    EndScalarsAllocation cur -> S.singleton cur
    ScalarCountBump _ curs -> S.fromList (L.map fst curs)
    ScalarCountBind _ _ ends -> S.singleton ends
    ScalarCountFinalize _ _ ends -> S.singleton ends
    ScalarCountSet footer count -> S.fromList [footer, count]
    ScalarCountCopyAll _ dstEnds srcEnds -> S.fromList [dstEnds, srcEnds]
    ReadScalarCount cur -> S.singleton cur
    ReadScalarCountFirstFooter cur -> S.singleton cur
    ReadScalarCountNextFooter cur -> S.singleton cur
    ForE v bound bod -> S.insert v (collectVars bound `S.union` collectVars bod)
    WhileCursor cur bod -> S.insert cur (collectVars bod)
    WhileCursorEnd cur end bod -> S.insert cur (S.insert end (collectVars bod))
    VecBroadcast _ _ val -> collectVars val
    VecLoad _ _ ref -> S.singleton ref
    VecAdd _ _ a b -> collectVars a `S.union` collectVars b
    VecSub _ _ a b -> collectVars a `S.union` collectVars b
    VecMul _ _ a b -> collectVars a `S.union` collectVars b
    VecDiv _ _ a b -> collectVars a `S.union` collectVars b
    VecMod _ _ a b -> collectVars a `S.union` collectVars b
    VecCmp _ _ _ a b -> collectVars a `S.union` collectVars b
    VecSelect _ _ m a b -> S.unions [collectVars m, collectVars a, collectVars b]
    VecStore _ _ ref val -> S.insert ref (collectVars val)
    SSPush _ a b _ -> S.fromList [a, b]
    SSPop _ a b -> S.fromList [a, b]
    Assert rhs -> collectVars rhs

identityPlan :: ScalarBufferSpec -> ScalarBufferPlan
identityPlan ScalarBufferSpec{sbsBufIx, sbsDCon, sbsFieldIdx, sbsTy} =
  ScalarBufferPlan
    { sbpBufIx = sbsBufIx
    , sbpDCon = sbsDCon
    , sbpFieldIdx = sbsFieldIdx
    , sbpTy = sbsTy
    , sbpScalar = mkScalar sbsTy
    , sbpOp = ScalarCopy
    }

-- | The scalar buffers of a fully factored value, in the order the SoA cursor
-- array holds them, with buffer 0 (the tag buffer) left implicit.
--
-- Three things have to agree about that order, and this is where two of them
-- meet:
--
--   * 'Gibbon.Passes.InferLocations.freshSoALoc2' decides the layout, over
--     'filterRanDatacons' of the constructor list.  Random access replaces a
--     constructor with a @^@ variant carrying extra cursor fields, and it is
--     the variant, not the original, that the program's case branches are
--     written over -- so the buffer keys must name the variant too.
--   * 'getCursorTypeFromTy' decides the cursor array's LENGTH, which is what
--     the ABI scan matches against.
--
-- The length is asserted against 'getCursorTypeFromTy' rather than recomputed,
-- so a disagreement declines the traversal instead of producing a plan indexed
-- off the end of the array.
scalarBufferSpecs :: DDefs Ty3 -> TyCon -> Maybe [ScalarBufferSpec]
scalarBufferSpecs ddefs tycon = do
  specs <- snd <$> foldM stepCtor (1, []) userDataCons
  case getCursorTypeFromTy tycon ddefs of
    CursorArrayTy n | n == 1 + length specs -> pure specs
    _ -> Nothing
  where
    ddef = lookupDDef ddefs tycon
    userDataCons =
      filter
        (\(dcon, _) -> not (isIndirectionTag dcon || isRedirectionTag dcon))
        (filterRanDatacons (dataCons ddef))

    stepCtor :: (Int, [ScalarBufferSpec]) -> (DataCon, [(Bool, Ty3)]) -> Maybe (Int, [ScalarBufferSpec])
    stepCtor (nextIx, acc) (dcon, fields) =
      foldM (stepField dcon) (nextIx, acc) (zip [0..] (map snd fields))

    stepField :: DataCon -> (Int, [ScalarBufferSpec]) -> (Int, Ty3) -> Maybe (Int, [ScalarBufferSpec])
    stepField dcon (nextIx, acc) (fieldIx, ty)
      -- A field of the type being traversed shares its parent's buffers.  A
      -- cursor field -- a random-access node, an indirection or a redirection
      -- target -- has no buffer of its own.  A packed field of a DIFFERENT
      -- type does get buffers, which the emitted loop cannot walk, so the
      -- whole traversal is refused rather than mis-indexed.
      | PackedTy tyc _ <- ty = if tyc == tycon then pure (nextIx, acc) else Nothing
      | CursorTy <- ty = pure (nextIx, acc)
      | CursorArrayTy{} <- ty = pure (nextIx, acc)
      | isScalarTy ty =
          pure
            ( nextIx + 1
            , acc ++ [ScalarBufferSpec nextIx dcon fieldIx ty]
            )
      | otherwise = Nothing

splitTopCase :: Exp3 -> Maybe ([(Var, [()], Ty3, Exp3)], Exp3, [(DataCon, [(Var, ())], Exp3)])
splitTopCase = go []
  where
    go acc ex =
      case ex of
        LetE b bod -> go (acc ++ [b]) bod
        CaseE scrt brs -> Just (acc, scrt, brs)
        _ -> Nothing

collectCursorRoles :: Var -> Var -> [(Var, [()], Ty3, Exp3)] -> M.Map Var BufferRole
collectCursorRoles inCurs outCurs binds =
  let inputArrays = extendCursorArrayAliases (S.singleton inCurs) binds
      outputArrays = extendCursorArrayAliases (S.singleton outCurs) binds
   in collectCursorRolesFrom M.empty inputArrays outputArrays binds

collectCursorRolesFrom :: M.Map Var BufferRole -> S.Set Var -> S.Set Var -> [(Var, [()], Ty3, Exp3)] -> M.Map Var BufferRole
collectCursorRolesFrom env0 inputArrays outputArrays = foldl step env0
  where
    step env (v, _, _, rhs) =
      let env' = collectNestedRoles env rhs
       in case rhsRole env' rhs of
            Just role -> M.insert v role env'
            Nothing -> env'

    rhsRole env rhs =
      case rhs of
        VarE v -> M.lookup v env
        Ext (IndexCursorArray arr ix)
          | arr `S.member` inputArrays -> Just (InputBuf ix)
          | arr `S.member` outputArrays -> Just (OutputBuf ix)
        Ext (AddrOfCursor inner) -> rhsRole env inner
        Ext (DerefMutCursor ref) -> M.lookup ref env
        Ext (AddCursor cur _) -> M.lookup cur env
        _ -> Nothing

    collectNestedRoles env ex =
      case ex of
        LetE (v, _, _, rhs1) bod ->
          let env1 = collectNestedRoles env rhs1
              env2 =
                case rhsRole env1 rhs1 of
                  Just role -> M.insert v role env1
                  Nothing -> env1
           in collectNestedRoles env2 bod
        IfE a b c ->
          let env1 = collectNestedRoles env a
              env2 = collectNestedRoles env1 b
           in collectNestedRoles env2 c
        MkProdE ls ->
          foldl collectNestedRoles env ls
        ProjE _ e ->
          collectNestedRoles env e
        PrimAppE _ args ->
          foldl collectNestedRoles env args
        AppE _ _ _ args ->
          foldl collectNestedRoles env args
        CaseE scrt brs ->
          let env1 = collectNestedRoles env scrt
           in foldl (\acc (_, _, rhs1) -> collectNestedRoles acc rhs1) env1 brs
        DataConE _ _ args ->
          foldl collectNestedRoles env args
        TimeIt e _ _ ->
          collectNestedRoles env e
        WithArenaE _ e ->
          collectNestedRoles env e
        SpawnE _ _ args ->
          foldl collectNestedRoles env args
        MapE (_, _, e1) e2 ->
          collectNestedRoles (collectNestedRoles env e1) e2
        FoldE (_, _, e1) (_, _, e2) e3 ->
          collectNestedRoles (collectNestedRoles (collectNestedRoles env e1) e2) e3
        Ext (LetAvail _ bod) ->
          collectNestedRoles env bod
        Ext (WriteScalar _ _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteTaggedCursor _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteCursorMutable _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (WriteList _ rhs1 _) ->
          collectNestedRoles env rhs1
        Ext (WriteVector _ rhs1 _) ->
          collectNestedRoles env rhs1
        Ext (AddCursor _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (BumpCursorMutable _ rhs1) ->
          collectNestedRoles env rhs1
        Ext (AddrOfCursor rhs1) ->
          collectNestedRoles env rhs1
        Ext (Assert rhs1) ->
          collectNestedRoles env rhs1
        _ -> env

extendCursorArrayAliases :: S.Set Var -> [(Var, [()], Ty3, Exp3)] -> S.Set Var
extendCursorArrayAliases seed binds = foldl step seed binds
  where
    step aliases (v, _, _, rhs) =
      case rhs of
        VarE src
          | src `S.member` aliases -> S.insert v aliases
        _ -> aliases

extractBranchPlans
  :: Var
  -> [ScalarBufferSpec]
  -> S.Set Var
  -> S.Set Var
  -> S.Set Var
  -> M.Map Var BufferRole
  -> (DataCon, [(Var, ())], Exp3)
  -> Maybe (M.Map Int ScalarBufferPlan)
extractBranchPlans selfName specs loopInvariantArgs baseInputArrays baseOutputArrays baseRoles (branchDCon, _, rhs) = do
  -- The generated loop synthesizes the branch body purely from the extracted
  -- scalar plans plus a verbatim copy of the input tag stream.  Anything else
  -- the branch does would silently disappear, so refuse to loopify unless
  -- every form in the branch is one the plan actually reproduces.  In
  -- particular a branch that writes a constructor tag other than its own is a
  -- tag rewrite, which the verbatim tag copy in `mkDConInnerLoop` would drop.
  --
  -- A REDIRECTION branch is exempt: redirection appears at a chunk boundary,
  -- and `mkContinueOneBufferLets` reads the boundary tag at each chunk
  -- transition, so the generated chunk walk does handle it.
  --
  -- An INDIRECTION branch is exempt only because the whole pass refuses to
  -- run on a program that can write one (see 'programWritesIndirections').
  -- Indirection appears MID-chunk, and `mkDConInnerLoop` copies one tag byte
  -- and bumps by one for `chunk_count` iterations with no tag inspection at
  -- all: a single indirection node -- a tag plus an 8-byte tagged cursor --
  -- would make the tag loop read pointer bytes as eight further tags and
  -- leave every scalar buffer misaligned for the rest of the chunk.  That is
  -- memory safety, not a wrong value.  Retargeting the walk is a future
  -- enhancement; until then the hazard is closed at the pass entry.
  if isIndirectionTag branchDCon || isRedirectionTag branchDCon
    then pure ()
    else if branchScanCovered branchDCon (scanBranchBody selfName rhs)
           then pure ()
           else Nothing
  let binds = collectAllLets rhs
      inputArrays = extendCursorArrayAliases baseInputArrays binds
      outputArrays = extendCursorArrayAliases baseOutputArrays binds
      roles = collectCursorRolesFrom baseRoles inputArrays outputArrays binds
      scalarInputs = collectScalarInputsWithRoles roles binds
      useCounts = occurrenceCounts rhs
      -- The binders on the branch body's UNCONDITIONAL spine.
      --
      -- `binds` above is 'collectAllLets', which descends into `IfE` arms and
      -- `CaseE` branches and records no distinction, so it cannot say whether a
      -- binding was evaluated on every element or only under a guard.  That
      -- distinction is exactly what decides whether a partial binding may be
      -- promoted to a residual: promoting a guarded one would hoist it out of
      -- its guard and make it trap on elements the source never divided.
      -- 'collectLeadingLets' is the spine, and nothing else.
      spineBinders = S.fromList [ v | (v, _, _, _) <- collectLeadingLets rhs ]
      pureEnv = collectPureBindings spineBinders scalarInputs useCounts binds
      specByBuf = M.fromList [ (sbsBufIx spec, spec) | spec <- specs ]

  -- A branch that computes something trapping or effectful and then never uses
  -- it must not be loopified: the synthesized loop reproduces only the plans,
  -- so the computation would vanish.  See 'branchDropsEffect'.
  if branchDropsEffect useCounts binds
    then Nothing
    else pure ()

  extractPlansFromExpr roles scalarInputs pureEnv specByBuf rhs
  where
    -- A constructor branch is converted into a map from scalar buffer index to
    -- the operation that should run for each element in that homogeneous
    -- buffer.  For normal branches this is just the set of scalar writes found
    -- in the branch.  For an `if`, both arms must write the same target
    -- buffers; the branch-level conditional is then retained as a scalar
    -- expression and later emitted as unit-valued write control flow in the
    -- inner loop.
    extractPlansFromExpr roles scalarInputs pureEnv specByBuf ex =
      case stripLeadingLets ex of
        IfE cond thn els -> do
          let cond' = normalizeWithResiduals pureEnv cond
              condFvs = S.toList (gFreeVars cond')
          if not (all (\v -> M.member v scalarInputs || v `S.member` loopInvariantArgs) condFvs)
            then Nothing
            else pure ()
          let condDeps = M.restrictKeys scalarInputs (S.fromList condFvs)
          validateScalarDeps specByBuf branchDCon condDeps
          thnPlans <- extractFlatPlans roles scalarInputs pureEnv specByBuf thn
          elsPlans <- extractFlatPlans roles scalarInputs pureEnv specByBuf els
          mergeConditionalPlanMaps scalarInputs cond' condDeps thnPlans elsPlans
        _ ->
          extractFlatPlans roles scalarInputs pureEnv specByBuf ex

    extractFlatPlans roles scalarInputs pureEnv specByBuf ex =
      foldM (stepWrite roles scalarInputs pureEnv specByBuf) M.empty (collectAllLets ex)

    -- Only strip leading administrative lets.  Nested lets still participate
    -- in the scalar input/pure binding analysis above.
    stripLeadingLets ex =
      case ex of
        LetE _ bod -> stripLeadingLets bod
        _ -> ex

    -- A scalar write is accepted only when it writes the scalar buffer for the
    -- current constructor field and its RHS mentions only same-constructor
    -- scalar inputs or loop-invariant scalar arguments.  This is the central
    -- "map over a buffer" invariant: no constructor control-flow or child
    -- result is allowed to determine the value being written.
    stepWrite roles scalarInputs pureEnv specByBuf acc (_, _, _, bindRhs) =
      case bindRhs of
        Ext (WriteScalar s outCur rhs0) -> do
          outBufIx <- case M.lookup outCur roles of
                        Just (OutputBuf ix) -> Just ix
                        _ -> Nothing
          spec <- M.lookup outBufIx specByBuf
          if sbsDCon spec /= branchDCon
            then Nothing
            else pure ()
          if scalarToTy s /= sbsTy spec
            then Nothing
            else pure ()
          if M.member outBufIx acc
            then Nothing
            else pure ()
          let rhs' = normalizeWithResiduals pureEnv rhs0
              fvs = S.toList (gFreeVars rhs')
          if not (all (\v -> M.member v scalarInputs || v `S.member` loopInvariantArgs) fvs)
            then Nothing
            else pure ()
          let deps = M.restrictKeys scalarInputs (S.fromList fvs)
          validateScalarDeps specByBuf branchDCon deps
          pure $
            M.insert
              outBufIx
              ScalarBufferPlan
                { sbpBufIx = outBufIx
                , sbpDCon = branchDCon
                , sbpFieldIdx = sbsFieldIdx spec
                , sbpTy = sbsTy spec
                , sbpScalar = s
                , sbpOp = ScalarExpr rhs' deps
                }
              acc
        _ -> pure acc

    -- Dependencies between scalar buffers are legal only within the same data
    -- constructor.  For example, a field update for `Cell.mom` may depend on
    -- `Cell.s`, but it may not depend on a `Particle` field because the loop
    -- over the `Cell.mom` buffer has no per-element dcon control flow.
    validateScalarDeps specByBuf dcon deps =
      mapM_
        (\info -> do
            depSpec <- M.lookup (siiBufIx info) specByBuf
            if sbsDCon depSpec /= dcon
              then Nothing
              else pure ()
            if scalarToTy (siiScalar info) /= sbsTy depSpec
              then Nothing
              else pure ())
        (M.elems deps)

    -- Conditional scalar updates are accepted only when both arms have the
    -- same write shape.  This lets the later loop body do exactly one write to
    -- the buffer per input element, independent of the branch taken.
    mergeConditionalPlanMaps scalarInputs cond condDeps thnPlans elsPlans = do
      let keys = S.toList (M.keysSet thnPlans `S.union` M.keysSet elsPlans)
      pairs <-
        mapM
          (\ix -> do
              thnPlan <- M.lookup ix thnPlans
              elsPlan <- M.lookup ix elsPlans
              plan <- mergeConditionalPlan scalarInputs cond condDeps thnPlan elsPlan
              pure (ix, plan))
          keys
      pure $ M.fromList pairs

    mergeConditionalPlan scalarInputs cond condDeps thnPlan elsPlan
      | thnPlan == elsPlan = Just thnPlan
      | otherwise = do
          if samePlanTarget thnPlan elsPlan
            then pure ()
            else Nothing
          (thnExpr, thnDeps) <- planAsExpr scalarInputs thnPlan
          (elsExpr, elsDeps) <- planAsExpr scalarInputs elsPlan
          pure $
            thnPlan
              { sbpOp =
                  ScalarExpr
                    (IfE cond thnExpr elsExpr)
                    (M.unions [condDeps, thnDeps, elsDeps])
              }

    samePlanTarget a b =
      sbpBufIx a == sbpBufIx b
        && sbpDCon a == sbpDCon b
        && sbpFieldIdx a == sbpFieldIdx b
        && sbpTy a == sbpTy b
        && sbpScalar a == sbpScalar b

    planAsExpr scalarInputs plan =
      case sbpOp plan of
        ScalarExpr expr deps -> Just (expr, deps)
        ScalarCopy -> do
          (v, info) <-
            listToMaybe
              [ (v, info)
              | (v, info) <- M.toList scalarInputs
              , siiBufIx info == sbpBufIx plan
              ]
          pure (VarE v, M.singleton v info)

-- | Abstract summary of one constructor branch body, used to decide whether
-- the synthesized loop reproduces everything the branch does.
--
-- `bsOk` is False as soon as a form is seen that the generated inner loop does
-- not re-emit (a call, an indirection/tagged-cursor write, a packed `MemCpy`,
-- an arena/region operation, ...).  The tag counters are an interval over all
-- control-flow paths through the branch: `bsMinTags`/`bsMaxTags` bound how many
-- constructor tags the branch writes, and `bsTagCons` records which ones.
data BranchScan = BranchScan
  { bsOk :: Bool
  , bsMinTags :: Int
  , bsMaxTags :: Int
  , bsTagCons :: S.Set DataCon
  }
  deriving (Eq, Ord, Show)

bsUnit :: BranchScan
bsUnit = BranchScan True 0 0 S.empty

bsBad :: BranchScan
bsBad = BranchScan False 0 0 S.empty

-- | Sequential composition: tag counts add.
bsSeq :: BranchScan -> BranchScan -> BranchScan
bsSeq a b =
  BranchScan
    { bsOk = bsOk a && bsOk b
    , bsMinTags = bsMinTags a + bsMinTags b
    , bsMaxTags = bsMaxTags a + bsMaxTags b
    , bsTagCons = bsTagCons a `S.union` bsTagCons b
    }

bsSeqAll :: [BranchScan] -> BranchScan
bsSeqAll = foldl bsSeq bsUnit

-- | Alternation (an `if`/nested `case`): tag counts widen to an interval.
bsAlt :: BranchScan -> BranchScan -> BranchScan
bsAlt a b =
  BranchScan
    { bsOk = bsOk a && bsOk b
    , bsMinTags = min (bsMinTags a) (bsMinTags b)
    , bsMaxTags = max (bsMaxTags a) (bsMaxTags b)
    , bsTagCons = bsTagCons a `S.union` bsTagCons b
    }

bsAltAll :: [BranchScan] -> BranchScan
bsAltAll [] = bsUnit
bsAltAll (x:xs) = foldl bsAlt x xs

-- | A branch is safe to replace with the synthesized loop only when nothing
-- unaccounted-for happens in it and it writes exactly one constructor tag on
-- every path, namely its own.  The generated dcon loop copies the input tag
-- stream verbatim, so any other tag write would be silently dropped.
branchScanCovered :: DataCon -> BranchScan -> Bool
branchScanCovered branchDCon scan =
  bsOk scan
    && bsMinTags scan == 1
    && bsMaxTags scan == 1
    && bsTagCons scan == S.singleton branchDCon

-- | Whitelist scan of a constructor branch body.  Anything not explicitly
-- listed as reproduced by the generated loop makes the scan fail, so new IR
-- forms default to "do not loopify".
scanBranchBody :: Var -> Exp3 -> BranchScan
scanBranchBody selfName = go
  where
    go ex =
      case ex of
        VarE{} -> bsUnit
        LitE{} -> bsUnit
        CharE{} -> bsUnit
        FloatE{} -> bsUnit
        LitSymE{} -> bsUnit
        -- Only the self recursive call is accounted for; it becomes the loop.
        -- Any other call would be dropped by the plan-driven body synthesis.
        AppE f _ _ args
          | f == selfName -> bsSeqAll (map go args)
          | otherwise -> bsBad
        PrimAppE _ args -> bsSeqAll (map go args)
        LetE (_, _, _, rhs) bod -> go rhs `bsSeq` go bod
        IfE a b c -> go a `bsSeq` (go b `bsAlt` go c)
        MkProdE ls -> bsSeqAll (map go ls)
        ProjE _ e -> go e
        CaseE scrt brs ->
          go scrt `bsSeq` bsAltAll [ go r | (_, _, r) <- brs ]
        DataConE{} -> bsBad
        TimeIt{} -> bsBad
        WithArenaE{} -> bsBad
        SpawnE{} -> bsBad
        SyncE -> bsBad
        MapE{} -> bsBad
        FoldE{} -> bsBad
        Ext ext -> goExt ext

    goExt ext =
      case ext of
        ReadScalar{} -> bsUnit
        WriteScalar _ _ rhs -> go rhs
        ReadTag{} -> bsUnit
        WriteTag dcon _ -> BranchScan True 1 1 (S.singleton dcon)
        TagCursor{} -> bsUnit
        ReadTaggedCursor{} -> bsUnit
        ReadCursor{} -> bsUnit
        MakeCursorArray{} -> bsUnit
        IndexCursorArray{} -> bsUnit
        AddCursor _ rhs -> go rhs
        BumpCursorMutable _ rhs -> go rhs
        AddrOfCursor rhs -> go rhs
        DerefMutCursor{} -> bsUnit
        CastPtr{} -> bsUnit
        SubPtr{} -> bsUnit
        EndOfBuffer{} -> bsUnit
        MMapFileSize{} -> bsUnit
        SizeOfPacked{} -> bsUnit
        SizeOfScalar{} -> bsUnit
        BoundsCheck{} -> bsUnit
        BoundsCheckVector{} -> bsUnit
        NullCursor -> bsUnit
        InitCursor{} -> bsUnit
        RetE ls -> bsSeqAll (map go ls)
        GetCilkWorkerNum -> bsUnit
        LetAvail _ bod -> go bod
        AllocateTagHere{} -> bsUnit
        AllocateScalarsHere{} -> bsUnit
        StartTagAllocation{} -> bsUnit
        EndTagAllocation{} -> bsUnit
        StartScalarsAllocation{} -> bsUnit
        EndScalarsAllocation{} -> bsUnit
        -- The generated loop re-establishes output footer counts once per
        -- chunk, so per-element count instrumentation is subsumed.
        ScalarCountBump{} -> bsUnit
        ScalarCountSet{} -> bsUnit
        Assert rhs -> go rhs
        -- Cursor-array bookkeeping copies are fine; a packed `MemCpy` moves
        -- payload the loop would not reproduce.
        MemCpy _ _ ty ->
          case ty of
            CursorArrayTy{} -> bsUnit
            _ -> bsBad
        _ -> bsBad

mergeBranchPlanMaps :: [M.Map Int ScalarBufferPlan] -> Maybe (M.Map Int ScalarBufferPlan)
mergeBranchPlanMaps =
  foldM
    (\acc mp ->
       foldM
         (\acc' (ix, plan) ->
            case M.lookup ix acc' of
              Nothing -> pure $ M.insert ix plan acc'
              Just plan'
                | plan' == plan -> pure acc'
                | otherwise -> Nothing)
         acc
         (M.toList mp))
    M.empty

loopifyFastPath :: Bool -> TraversalPlan -> FunDef3 -> PassM (Maybe Exp3)
loopifyFastPath fuseScalarLoops TraversalPlan{tpABI = LoopifyABI{abiArrLen, abiInEnds, abiOutEnds, abiOutCurs, abiInCurs}, tpScalarPlans} FunDef{funTy = (_, out)}
  | otherwise =
      if abiArrLen == 1 + length tpScalarPlans
         && out == loopifiedOutTy abiArrLen
      then Just <$> mkFastPathBody fuseScalarLoops abiArrLen abiInEnds abiOutEnds abiOutCurs abiInCurs tpScalarPlans
      else if abiArrLen == 1 + length tpScalarPlans
              && out == ProdTy []
      then Just <$> mkMutableFastPathBody fuseScalarLoops abiArrLen abiInEnds abiOutEnds abiOutCurs abiInCurs tpScalarPlans
      else pure Nothing

loopifiedOutTy :: Int -> Ty3
loopifiedOutTy arr =
  ProdTy
    [ CursorArrayTy arr
    , CursorArrayTy arr
    , CursorArrayTy arr
    , ProdTy [CursorArrayTy arr, CursorArrayTy arr]
    ]

collectLeadingLets :: Exp3 -> [(Var, [()], Ty3, Exp3)]
collectLeadingLets ex =
  case ex of
    LetE b bod -> b : collectLeadingLets bod
    _ -> []

collectAllLets :: Exp3 -> [(Var, [()], Ty3, Exp3)]
collectAllLets ex =
  case ex of
    LetE b@(_, _, _, rhs) bod ->
      b : collectAllLets rhs ++ collectAllLets bod
    IfE a b c ->
      collectAllLets a ++ collectAllLets b ++ collectAllLets c
    MkProdE ls ->
      concatMap collectAllLets ls
    ProjE _ e ->
      collectAllLets e
    PrimAppE _ args ->
      concatMap collectAllLets args
    AppE _ _ _ args ->
      concatMap collectAllLets args
    CaseE scrt brs ->
      collectAllLets scrt ++ concatMap (\(_, _, rhs) -> collectAllLets rhs) brs
    DataConE _ _ args ->
      concatMap collectAllLets args
    TimeIt e _ _ ->
      collectAllLets e
    WithArenaE _ e ->
      collectAllLets e
    SpawnE _ _ args ->
      concatMap collectAllLets args
    MapE (_, _, e1) e2 ->
      collectAllLets e1 ++ collectAllLets e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      collectAllLets e1 ++ collectAllLets e2 ++ collectAllLets e3
    Ext (ForE _ bound body) ->
      collectAllLets bound ++ collectAllLets body
    Ext (WhileCursor _ bod) ->
      collectAllLets bod
    Ext (WhileCursorEnd _ _ bod) ->
      collectAllLets bod
    Ext (WriteScalar _ _ rhs) ->
      collectAllLets rhs
    Ext (WriteTaggedCursor _ rhs) ->
      collectAllLets rhs
    Ext (WriteCursorMutable _ rhs) ->
      collectAllLets rhs
    Ext (WriteList _ rhs _) ->
      collectAllLets rhs
    Ext (WriteVector _ rhs _) ->
      collectAllLets rhs
    Ext (AddCursor _ rhs) ->
      collectAllLets rhs
    Ext (BumpCursorMutable _ rhs) ->
      collectAllLets rhs
    Ext (AddrOfCursor rhs) ->
      collectAllLets rhs
    Ext (LetAvail _ bod) ->
      collectAllLets bod
    Ext (Assert rhs) ->
      collectAllLets rhs
    _ -> []

hasParentChildDependency :: Var -> Exp3 -> Bool
hasParentChildDependency funName body =
  let childVars = childDerivedVars funName body
   in not (S.null childVars)
        && exprHasParentChildUse childVars body

childDerivedVars :: Var -> Exp3 -> S.Set Var
childDerivedVars funName body = fixedPoint S.empty
  where
    binds = collectAllLets body

    fixedPoint seen =
      let seen' = foldl step seen binds
       in if seen' == seen
            then seen
            else fixedPoint seen'

    step seen (v, _, _, rhs)
      | isSelfCall rhs = S.insert v seen
      | exprMentionsAny seen rhs = S.insert v seen
      | otherwise = seen

    isSelfCall rhs =
      case rhs of
        AppE fn _ _ _ | fn == funName -> True
        _ -> False

exprMentionsAny :: S.Set Var -> Exp3 -> Bool
exprMentionsAny vars rhs =
  not (S.null (collectVars rhs `S.intersection` vars))

exprHasParentChildUse :: S.Set Var -> Exp3 -> Bool
exprHasParentChildUse childVars ex =
  case ex of
    VarE{} -> False
    LitE{} -> False
    CharE{} -> False
    FloatE{} -> False
    LitSymE{} -> False
    AppE _ _ _ args ->
      any (exprMentionsAny childVars) args
    PrimAppE _ args ->
      any (exprMentionsAny childVars) args
    LetE (_, _, _, rhs) bod ->
      exprHasParentChildUse childVars rhs || exprHasParentChildUse childVars bod
    IfE cond thn els ->
      exprMentionsAny childVars cond
        || exprHasParentChildUse childVars thn
        || exprHasParentChildUse childVars els
    MkProdE args ->
      any (exprMentionsAny childVars) args
    ProjE _ rhs ->
      exprHasParentChildUse childVars rhs
    CaseE scrt brs ->
      exprMentionsAny childVars scrt
        || any (\(_, _, rhs) -> exprHasParentChildUse childVars rhs) brs
    DataConE _ _ args ->
      any (exprMentionsAny childVars) args
    TimeIt rhs _ _ ->
      exprHasParentChildUse childVars rhs
    WithArenaE _ rhs ->
      exprHasParentChildUse childVars rhs
    SpawnE _ _ args ->
      any (exprMentionsAny childVars) args
    SyncE -> False
    MapE (_, _, e1) e2 ->
      exprHasParentChildUse childVars e1 || exprHasParentChildUse childVars e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      any (exprHasParentChildUse childVars) [e1, e2, e3]
    Ext ext ->
      extHasParentChildUse childVars ext

extHasParentChildUse :: S.Set Var -> E3Ext () Ty3 -> Bool
extHasParentChildUse childVars ext =
  case ext of
    WriteScalar _ _ rhs ->
      exprMentionsAny childVars rhs
    WriteTagPacked _ rhs ->
      exprMentionsAny childVars rhs
    WriteTaggedCursor _ rhs ->
      exprMentionsAny childVars rhs
    WriteCursorMutable _ rhs ->
      exprMentionsAny childVars rhs
    WriteList _ rhs _ ->
      exprMentionsAny childVars rhs
    WriteVector _ rhs _ ->
      exprMentionsAny childVars rhs
    AddCursor _ rhs ->
      exprMentionsAny childVars rhs
    BumpCursorMutable _ rhs ->
      exprMentionsAny childVars rhs
    AddrOfCursor rhs ->
      exprHasParentChildUse childVars rhs
    LetAvail _ bod ->
      exprHasParentChildUse childVars bod
    Assert rhs ->
      exprMentionsAny childVars rhs
    ForE _ bound bod ->
      exprMentionsAny childVars bound || exprHasParentChildUse childVars bod
    WhileCursor _ bod ->
      exprHasParentChildUse childVars bod
    WhileCursorEnd _ _ bod ->
      exprHasParentChildUse childVars bod
    RetE args ->
      any (exprMentionsAny childVars) args
    _ ->
      False

mkFastPathBody :: Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkFastPathBody fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  dflags <- getDynFlags
  mkGenericFastPathBody dflags False fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans

mkMutableFastPathBody :: Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkMutableFastPathBody fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  dflags <- getDynFlags
  mkGenericFastPathBody dflags True fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans

mkGenericFastPathBody :: DynFlags -> Bool -> Bool -> Int -> Var -> Var -> Var -> Var -> [ScalarBufferPlan] -> PassM Exp3
mkGenericFastPathBody dflags isMutable fuseScalarLoops arrLen inEnds outEnds outCurs inCurs plans = do
  nameSeed <- freshLoopNameSeed isMutable
  let body = mkLets (prelude nameSeed) (fastBody nameSeed)
  pure body
  where
    -- The generated structure is:
    --
    --   for the dcon stream, and each constructor's scalar-buffer group:
    --     while representative_count_footer != NULL:
    --       count = scalar_count(representative_count_footer)
    --       set each output buffer's footer count to count
    --       for i in [0,count):
    --         copy/update one element in every buffer in the group
    --       if not last chunk:
    --         read each input redirection, grow each output region, and advance
    --         each footer cursor to the next chunk's count
    --
    -- This is intentionally buffer-oriented rather than recursive.  We fuse
    -- scalar buffers by constructor, not by field, because fields belonging to
    -- the same constructor have the same per-chunk element count.  Fully
    -- factored SoA layout keeps redirection boundaries aligned across buffers:
    -- when any buffer grows, all peer buffers get corresponding redirections.
    -- The dcon stream remains separate because its footer count is the total
    -- number of constructor tags in the chunk, not the count for a single
    -- constructor.  The generated loops rely on the RTS invariant that footer
    -- counts describe the next chunk in O(1): the final/end footer stores the
    -- first chunk count, and each redirection boundary footer stores the
    -- following chunk count.
    sortedPlans = L.sortOn sbpBufIx plans
    planMap = M.fromList [ (sbpBufIx p, p) | p <- sortedPlans ]
    bufferIndices = [0 .. arrLen - 1]
    scalarGroups
      | fuseScalarLoops =
          L.sortOn (minimum . map sbpBufIx) $
            map (L.sortOn sbpBufIx) $
              M.elems $
                M.fromListWith (++)
                  [ (sbpDCon plan, [plan])
                  | plan <- sortedPlans
                  ]
      | otherwise =
          map (:[]) sortedPlans
    loopGroups = Left 0 : map Right scalarGroups

    groupBufferIndices group =
      case group of
        Left ix -> [ix]
        Right groupPlans -> map sbpBufIx groupPlans

    groupRepIx group =
      case groupBufferIndices group of
        ix:_ -> ix
        [] -> error "loopify: empty loop group"

    nullFooter seed = loopName seed "null_footer"
    overwriteReg seed = loopName seed "overwrite_reg"
    inFinalArr seed = loopName seed "in_final_arr"
    outFinalArr seed = loopName seed "out_final_arr"
    packedPair seed = loopName seed "packed_pair"

    inputEndVar seed ix = loopBufferName seed ix LbInputEnd
    firstFooterVar seed ix = loopBufferNameLocal seed ix "first_footer"
    countFooterCurVar seed ix = loopBufferNameLocal seed ix "count_footer_cur"
    countFooterLocVar seed ix = loopBufferNameLocal seed ix "count_footer_loc"
    nextFooterCurVar seed ix = loopBufferNameLocal seed ix "next_footer_cur"
    nextFooterLocVar seed ix = loopBufferNameLocal seed ix "next_footer_loc"
    inLocVar seed ix = loopBufferName seed ix LbInLoc
    outLocVar seed ix = loopBufferName seed ix LbOutLoc
    outEndLocVar seed ix = loopBufferName seed ix LbOutEndLoc
    loopResVar seed ix = loopBufferNameLocal seed ix "loop"
    scalarLoopResVar seed ix dcon =
      loopBufferNameLocal seed ix ("dcon_" ++ sanitizeLoopName dcon ++ "_loop")
    finalInVar seed ix = loopBufferNameLocal seed ix "in_final"
    finalOutVar seed ix = loopBufferNameLocal seed ix "out_final"
    finalOutEndVar seed ix = loopBufferNameLocal seed ix "out_end_final"

    depStartVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_start")
    depLocVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_loc")

    depReadCurVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_read_cur")
    depReadPairVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_read_pair")
    depReadValVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_read_val")
    depBumpVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_bump")
    depBoundaryCurVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_boundary_cur")
    depBoundaryPairVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_boundary_pair")
    depBoundaryAfterVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_boundary_after")
    depRedirPairVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_redir_pair")
    depNextStartVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_next_start")
    depSetInVar seed ix depIx = loopBufferNameLocal seed ix ("dep" ++ show depIx ++ "_set_in")

    prelude pfx =
      [ (nullFooter pfx, [], CursorTy, Ext NullCursor) ]
      ++ concatMap (mkBufferPrelude pfx) bufferIndices
      ++ concatMap (mkDependencyPrelude pfx) dependencyPairs

    dependencyPairs =
      [ (sbpBufIx plan, info)
      | plan <- sortedPlans
      , info <- planDependencyInfos plan
      , siiBufIx info /= sbpBufIx plan
      ]

    -- Each buffer loop owns its mutable input/output cursors and the footer
    -- cursors used for chunk bounds.  Cross-buffer dependency cursors are
    -- separate mutable cursors initialized from the original input cursor
    -- array; they are not aliases of another buffer loop's main cursor.
    mkBufferPrelude pfx ix =
      [ (inputEndVar pfx ix, [], CursorTy, indexCursorExp inEnds ix)
      , (firstFooterVar pfx ix, [], CursorTy, Ext $ ReadScalarCountFirstFooter (inputEndVar pfx ix))
      , (countFooterCurVar pfx ix, [], CursorTy, VarE (inputEndVar pfx ix))
      , (countFooterLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (VarE (countFooterCurVar pfx ix)))
      , (nextFooterCurVar pfx ix, [], CursorTy, VarE (firstFooterVar pfx ix))
      , (nextFooterLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (VarE (nextFooterCurVar pfx ix)))
      , (inLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp inCurs ix))
      , (outLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outCurs ix))
      , (outEndLocVar pfx ix, [], MutCursorTy, Ext $ AddrOfCursor (indexCursorExp outEnds ix))
      ]

    mkDependencyPrelude pfx (ix, info) =
      let depIx = siiBufIx info
       in [ (depStartVar pfx ix depIx, [], CursorTy, indexCursorExp inCurs depIx)
          , (depLocVar pfx ix depIx, [], MutCursorTy, Ext $ AddrOfCursor (VarE (depStartVar pfx ix depIx)))
          ]

    fastBody pfx =
      if isMutable
        then mkLets (map (mkLoopGroup pfx) loopGroups) (MkProdE [])
        else
          mkLets
            ( map (mkLoopGroup pfx) loopGroups
                ++ concatMap (mkBufferFinalLets pfx) bufferIndices
                ++ [ (overwriteReg pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalOutEndVar pfx) bufferIndices))
                   , (inFinalArr pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalInVar pfx) bufferIndices))
                   , (outFinalArr pfx, [], CursorArrayTy arrLen, Ext $ MakeCursorArray arrLen (map (finalOutVar pfx) bufferIndices))
                   , (packedPair pfx, [], ProdTy [CursorArrayTy arrLen, CursorArrayTy arrLen], MkProdE [VarE outCurs, VarE (outFinalArr pfx)])
                   ]
            )
            (MkProdE [VarE inEnds, VarE (overwriteReg pfx), VarE (inFinalArr pfx), VarE (packedPair pfx)])

    mkLoopGroup pfx group =
      let repIx = groupRepIx group
          resVar =
            case group of
              Left{} -> loopResVar pfx repIx
              Right (plan:_) -> scalarLoopResVar pfx repIx (sbpDCon plan)
              Right [] -> loopResVar pfx repIx
       in (resVar, [], ProdTy [], Ext $ WhileCursor (countFooterLocVar pfx repIx) (mkGroupChunkBody pfx group))

    mkBufferFinalLets pfx ix =
      [ (finalInVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
      , (finalOutVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
      , (finalOutEndVar pfx ix, [], CursorTy, Ext $ DerefMutCursor (outEndLocVar pfx ix))
      ]

    -- Note [Output capacity in synthesized chunk loops]
    -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    -- Loopification REPLACES the recursive function's per-node
    -- 'BoundsCheck'/'BoundsCheckVector'.  That check does not survive into the
    -- synthesized loop -- measured: a shape-preserving SoA `bump` carries
    -- @BoundsCheckVector [(10,..),(26,..)]@ before this pass and none after.
    -- What replaces it is the chunk discipline built below, one instance per
    -- output buffer:
    --
    --     while (*count_footer_loc != NULL) {
    --       chunk_count = ReadScalarCount(*count_footer_loc)   -- from the INPUT footer
    --       ScalarCountSet(*out_end_loc, chunk_count)          -- stamp the OUTPUT footer
    --       ForE i in [0, chunk_count) { read one elt; write one elt; bump both }
    --       if !is_last_chunk then GrowRegion(out_loc, out_end_loc)
    --     }
    --
    -- So the trip count comes from the INPUT and the capacity from the OUTPUT,
    -- and nothing tests one against the other.  The invariant that makes this
    -- safe, and which anything editing this code must preserve:
    --
    --   For every output buffer b and every chunk:
    --       bytes_written(b) = chunk_count * width(b)  <=  usable_capacity(b)
    --
    --   because (i) `chunk_count` is recorded by the PRODUCER at the point the
    --   *widest* buffer of the group would overflow its chunk, so every
    --   narrower buffer carries slack; and (ii) the output region mirrors the
    --   input's chunk-size sequence -- same initial size from
    --   `gib_get_inf_init_chunk_size()`, same doubling in `gib_grow_region`,
    --   exactly one growth per input chunk transition.
    --
    -- Measured on a mixed-width Factored SoA
    -- @Node Int8 Int16 Int32 Int64 Rec@ at 3000 nodes, crossing four chunk
    -- boundaries: bytes per element are exactly 1.000 / 2.000 / 4.000 / 8.000,
    -- and the minimum margin per buffer is 863 / 742 / 500 / **16** bytes.  The
    -- W64 buffer is the binding constraint at a constant 16-byte margin; the
    -- others are slack.  Zero overruns, zero ASan findings, across W8/W16/W32/
    -- W64, counts 0..2049 spanning lane-1/lane/lane+1 for 16/8/4/2 lanes and
    -- chunk boundaries, in gibbon2/loopify/selective/vectorize.
    --
    -- The vector/tail split adds no risk: 'VectorizeTraversals' derives
    -- @simd_vec_count = chunk_count / lanes@ and
    -- @simd_tail_count = chunk_count % lanes@, so
    -- @lanes * vec_count + tail_count == chunk_count@ identically.
    --
    -- THREE UNCHECKED PRECONDITIONS.  These are residual risk; each
    -- would break the inequality above and none is verified at runtime:
    --   P1  the output cursor enters each chunk at its start.  A caller that
    --       has already written into the output chunk leaves less room while
    --       `chunk_count` still describes a full input chunk.
    --   P2  the output region's chunk sizes are pointwise >= the input's.
    --   P3  the input footer's `chunk_count` faithfully describes that chunk.
    -- 'tests/LoopifyTraversals.hs' pins the structure emitted here so the
    -- replacement mechanism cannot be dropped silently; the runtime capacity
    -- accounting is re-measurable with
    -- 'gibbon-compiler/tests/vw07_output_capacity.sh'.
    mkGroupChunkBody pfx group =
      let repIx = groupRepIx group
          currentCountFooter = loopBufferNameLocal pfx repIx "current_count_footer"
          chunkCount = loopBufferNameLocal pfx repIx "chunk_count"
          currentNextFooter = loopBufferNameLocal pfx repIx "current_next_footer"
          isNullNextFooter = loopBufferNameLocal pfx repIx "is_null_next_footer"
          isEndNextFooter = loopBufferNameLocal pfx repIx "is_end_next_footer"
          isLastChunk = loopBufferNameLocal pfx repIx "is_last_chunk"
          innerLoopRes = loopBufferNameLocal pfx repIx "inner_loop_res"
          chunkBranch = loopBufferNameLocal pfx repIx "chunk_branch"
       in mkLets
            ( [ (currentCountFooter, [], CursorTy, Ext $ DerefMutCursor (countFooterLocVar pfx repIx))
              , (chunkCount, [], (IntTy W64), Ext $ ReadScalarCount currentCountFooter)
              , (currentNextFooter, [], CursorTy, Ext $ DerefMutCursor (nextFooterLocVar pfx repIx))
              , (isNullNextFooter, [], BoolTy, PrimAppE eqIntP64 [VarE currentNextFooter, VarE (nullFooter pfx)])
              , (isEndNextFooter, [], BoolTy, PrimAppE eqIntP64 [VarE currentNextFooter, VarE (inputEndVar pfx repIx)])
              , (isLastChunk, [], BoolTy, PrimAppE OrP [VarE isNullNextFooter, VarE isEndNextFooter])
              ]
              ++ concatMap (mkSetChunkCountLets pfx chunkCount) (groupBufferIndices group)
              ++ [ (innerLoopRes, [], ProdTy [], Ext $ ForE (loopBufferNameLocal pfx repIx "i") (VarE chunkCount) (mkGroupInnerLoopBody pfx group))
                 , (chunkBranch, [], ProdTy [], IfE (VarE isLastChunk) (mkGroupLastChunkBody pfx group) (mkGroupContinueChunkBody pfx group currentNextFooter))
              ]
            )
            (MkProdE [])

    mkSetChunkCountLets pfx chunkCount ix =
      let currentOutEnd = loopBufferName pfx ix LbCurrentOutEnd
          setChunkCount = loopBufferName pfx ix LbSetChunkCount
       in [ (currentOutEnd, [], CursorTy, Ext $ DerefMutCursor (outEndLocVar pfx ix))
          , (setChunkCount, [], ProdTy [], Ext $ ScalarCountSet currentOutEnd chunkCount)
          ]

    mkGroupInnerLoopBody pfx group =
      case group of
        Left ix -> mkDConInnerLoop pfx ix
        Right groupPlans ->
          -- A residual `let` re-attached by 'wrapResidualBinds' is attached to
          -- every plan that needs it, and the plans of a group are emitted as
          -- nested unit lets in ONE block -- so a binder two plans share would
          -- be declared twice in the same C scope.  Rename exactly those, and
          -- leave every other binder with the name it was given at its
          -- definition.
          let sharedBinders =
                M.keysSet $
                  M.filter (> (1 :: Int)) $
                    M.fromListWith (+)
                      [ (v, 1)
                      | plan <- groupPlans
                      , v <- scalarPlanLetBinders plan
                      ]
           in mkLets
                [ ( loopBufferNameLocal pfx (sbpBufIx plan) "inner_body"
                  , []
                  , ProdTy []
                  , mkScalarInnerLoop pfx (sbpBufIx plan) sharedBinders plan )
                | plan <- groupPlans
                ]
                (MkProdE [])

    -- The tag stream is copied from input to output.  We deliberately avoid
    -- hardcoding constructor tags here: tree-like and multi-constructor ADTs
    -- may have arbitrary tag order in the packed input.
    mkDConInnerLoop pfx ix =
      let readCur = loopBufferName pfx ix LbReadCur
          readPair = loopBufferNameLocal pfx ix "read_pair"
          readTag = loopBufferNameLocal pfx ix "read_tag"
          writeCur = loopBufferName pfx ix LbWriteCur
          writeTag = loopBufferNameLocal pfx ix "write_tag"
          bumpIn = loopBufferNameLocal pfx ix "bump_in"
          bumpOut = loopBufferNameLocal pfx ix "bump_out"
       in mkLets
            [ (readCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
            , (readPair, [], ProdTy [(IntTy W64), CursorTy], Ext $ ReadTag readCur)
            , (readTag, [], (IntTy W64), ProjE 0 (VarE readPair))
            , (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
            , (writeTag, [], CursorTy, Ext $ WriteTagPacked writeCur (VarE readTag))
            , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (mkLitE64 1))
            , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (mkLitE64 1))
            ]
            (MkProdE [])

    -- Scalar buffers either copy the input value or apply the extracted pure
    -- scalar expression.  Conditional scalar expressions are emitted as
    -- unit-valued write branches so that lowering can keep `ForE` bodies as
    -- unit tails.  Output footer metadata is set once per chunk in
    -- `mkBufferChunkBody`; shape-preserving maps do not need per-element
    -- metadata bumps.
    mkScalarInnerLoop pfx ix sharedBinders plan@ScalarBufferPlan{sbpTy, sbpScalar, sbpOp} =
      let readCur = loopBufferName pfx ix LbReadCur
          readPair = loopBufferNameLocal pfx ix "read_pair"
          readVal = loopBufferNameLocal pfx ix "read_val"
          fieldVal = loopBufferNameLocal pfx ix "field_val"
          fieldThenVal = loopBufferNameLocal pfx ix "field_then_val"
          fieldElseVal = loopBufferNameLocal pfx ix "field_else_val"
          writeCur = loopBufferName pfx ix LbWriteCur
          writeVal = loopBufferNameLocal pfx ix "write_val"
          writeThenVal = loopBufferNameLocal pfx ix "write_then_val"
          writeElseVal = loopBufferNameLocal pfx ix "write_else_val"
          conditionalWrite = loopBufferNameLocal pfx ix "conditional_write"
          bumpIn = loopBufferNameLocal pfx ix "bump_in"
          bumpOut = loopBufferNameLocal pfx ix "bump_out"
          scalarBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc sbpTy) (sizeOfTyD dflags sbpTy)
          rawFieldExpr = instantiateScalarOp pfx ix sharedBinders readVal sbpOp
          (fieldExprLets, fieldExpr) = anfScalarExpr pfx ix rawFieldExpr
          commonLets =
            [ (readCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
            , (readPair, [], ProdTy [sbpTy, CursorTy], Ext $ ReadScalar sbpScalar readCur)
            , (readVal, [], sbpTy, ProjE 0 (VarE readPair))
            ]
            ++ concatMap (mkDependencyRead pfx ix) (planDependencies plan)
            ++ fieldExprLets
          writeLets =
            case fieldExpr of
              IfE cond thn els ->
                [ (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
                , ( conditionalWrite
                  , []
                  , ProdTy []
                  , IfE cond
                      (mkScalarWriteBranch fieldThenVal writeThenVal writeCur thn)
                      (mkScalarWriteBranch fieldElseVal writeElseVal writeCur els)
                  )
                , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (mkLitE64 scalarBytes))
                , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (mkLitE64 scalarBytes))
                ]
              _ ->
                [ (fieldVal, [], sbpTy, fieldExpr)
                , (writeCur, [], CursorTy, Ext $ DerefMutCursor (outLocVar pfx ix))
                , (writeVal, [], CursorTy, Ext $ WriteScalar sbpScalar writeCur (VarE fieldVal))
                , (bumpIn, [], ProdTy [], Ext $ BumpCursorMutable (inLocVar pfx ix) (mkLitE64 scalarBytes))
                , (bumpOut, [], ProdTy [], Ext $ BumpCursorMutable (outLocVar pfx ix) (mkLitE64 scalarBytes))
                ]
       in mkLets
            (commonLets ++ writeLets)
            (MkProdE [])
      where
        mkScalarWriteBranch fieldVar writeVar writeCur expr =
          mkLets
            [ (fieldVar, [], sbpTy, expr)
            , (writeVar, [], CursorTy, Ext $ WriteScalar sbpScalar writeCur (VarE fieldVar))
            ]
            (MkProdE [])

    -- Cross-buffer dependencies are read with their own cursor.  This fixed
    -- the `scaleEnergy` case where one field's update depended on another
    -- field buffer that had already been walked by its own loop.
    mkDependencyRead pfx ix (_, info)
      | depIx == ix = []
      | otherwise =
          let depTy = scalarToTy (siiScalar info)
              depBytes = fromMaybe (error $ "loopify: expected scalar size for " ++ sdoc depTy) (sizeOfTyD dflags depTy)
           in [ (depReadCurVar pfx ix depIx, [], CursorTy, Ext $ DerefMutCursor (depLocVar pfx ix depIx))
              , (depReadPairVar pfx ix depIx, [], ProdTy [depTy, CursorTy], Ext $ ReadScalar (siiScalar info) (depReadCurVar pfx ix depIx))
              , (depReadValVar pfx ix depIx, [], depTy, ProjE 0 (VarE (depReadPairVar pfx ix depIx)))
              , (depBumpVar pfx ix depIx, [], ProdTy [], Ext $ BumpCursorMutable (depLocVar pfx ix depIx) (mkLitE64 depBytes))
              ]
      where
        depIx = siiBufIx info

    instantiateScalarOp pfx ix sharedBinders readVal op =
      case op of
        ScalarCopy -> VarE readVal
        ScalarExpr expr deps ->
          renameScalarLets pfx ix sharedBinders $
            substMany
              [ (src, replacementFor info)
              | (src, info) <- M.toList deps
              ]
              expr
      where
        replacementFor info
          | siiBufIx info == ix = VarE readVal
          | otherwise = VarE (depReadValVar pfx ix (siiBufIx info))

    -- Rename the `let` binders this plan would otherwise share with another
    -- plan in the same group.
    --
    -- Only those: a binder is a name a reader can follow back to the source
    -- binding it came from, so it is kept wherever keeping it is safe.  The
    -- @res@ suffix cannot collide with 'anfScalarExpr''s own @anf@ names, and
    -- @(pfx, ix)@ makes the new name unique across plans.
    renameScalarLets :: LoopNameSeed -> Int -> S.Set Var -> Exp3 -> Exp3
    renameScalarLets pfx ix sharedBinders expr0 = fst (goRen M.empty 0 expr0)
      where
        goRen :: M.Map Var Var -> Int -> Exp3 -> (Exp3, Int)
        goRen sub n ex =
          case ex of
            VarE v -> (VarE (M.findWithDefault v v sub), n)
            LitE{} -> (ex, n)
            CharE{} -> (ex, n)
            FloatE{} -> (ex, n)
            LitSymE{} -> (ex, n)
            PrimAppE p args ->
              let (args', n') = goRenList sub n args
               in (PrimAppE p args', n')
            ProjE i e ->
              let (e', n') = goRen sub n e
               in (ProjE i e', n')
            IfE a b c ->
              let (a', n1) = goRen sub n a
                  (b', n2) = goRen sub n1 b
                  (c', n3) = goRen sub n2 c
               in (IfE a' b' c', n3)
            LetE (v, locs, ty, rhs) bod
              | v `S.member` sharedBinders ->
                  let (rhs', n1) = goRen sub n rhs
                      v' = loopBufferNameLocal pfx ix ("res" ++ show n1)
                      (bod', n2) = goRen (M.insert v v' sub) (n1 + 1) bod
                   in (LetE (v', locs, ty, rhs') bod', n2)
              | otherwise ->
                  let (rhs', n1) = goRen sub n rhs
                      (bod', n2) = goRen (M.delete v sub) n1 bod
                   in (LetE (v, locs, ty, rhs') bod', n2)
            _ -> (ex, n)

        goRenList :: M.Map Var Var -> Int -> [Exp3] -> ([Exp3], Int)
        goRenList _ n [] = ([], n)
        goRenList sub n (e:es) =
          let (e', n1) = goRen sub n e
              (es', n2) = goRenList sub n1 es
           in (e' : es', n2)

    anfScalarExpr :: LoopNameSeed -> Int -> Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3)
    anfScalarExpr pfx ix expr =
      let (binds, expr', _) = go 0 expr
       in (binds, expr')
      where
        tmpVar :: Int -> Var
        tmpVar n = loopBufferNameLocal pfx ix ("anf" ++ show n)

        go :: Int -> Exp3 -> ([(Var, [()], Ty3, Exp3)], Exp3, Int)
        go n ex =
          case ex of
            VarE{} -> ([], ex, n)
            LitE{} -> ([], ex, n)
            CharE{} -> ([], ex, n)
            FloatE{} -> ([], ex, n)
            LitSymE{} -> ([], ex, n)
            PrimAppE p args ->
              let (argBinds, args', n') = goArgs n args
                  tmp = tmpVar n'
                  ty = primRetTy p
               in (argBinds ++ [(tmp, [], ty, PrimAppE p args')], VarE tmp, n' + 1)
            -- CONTROL-SENSITIVE ANF.  A binding may only be lifted to a point
            -- that dominates exactly the evaluations the original expression
            -- performed.  The condition is always evaluated, so its bindings
            -- may leave the `IfE`; the arms are not, so theirs may NOT.
            --
            -- Returning `ab ++ bb ++ cb` (what this used to do) hands all three
            -- lists to a caller that splices them ABOVE the `IfE`, which makes
            -- both arms run unconditionally.  For `if d == 0 then 7 else 100/d`
            -- that hoisted the division out of its guard: gibbon2 printed 27
            -- while every loopified mode divided by zero.
            --
            -- This is structural and applies to every operation, not only the
            -- ones currently classified as partial -- it equally protects
            -- `ErrorP`, future bounds checks, and evaluation cost.
            --
            -- The counter still threads left-to-right through all three
            -- sub-traversals (n -> n1 -> n2 -> n3), so the branch-local names
            -- stay globally distinct even though they are now bound in
            -- different scopes.
            IfE a b c ->
              let (ab, a', n1) = go n a
                  (bb, b', n2) = go n1 b
                  (cb, c', n3) = go n2 c
               in (ab, IfE a' (mkLets bb b') (mkLets cb c'), n3)
            ProjE i e ->
              let (bs, e', n') = go n e
               in (bs, ProjE i e', n')
            -- A source `let` keeps its binder, its type and its control point.
            --
            -- The returned list is spliced by the caller at exactly the point
            -- this expression is evaluated -- the `IfE` case above is that
            -- caller when the let is inside an arm, so a
            -- let written in a branch stays in that branch: branch-local
            -- computations must remain dominated by their guard.  Emitting the
            -- binding into the list therefore preserves both dominance and
            -- order: the RHS's own ANF bindings, then the binding itself, then
            -- the body's.
            --
            -- The binder is NOT inlined into its uses.  A value referenced twice
            -- must not make its RHS run twice, and `v` keeps its original name
            -- (globally unique by construction), its `locs` and its type, so no
            -- new name is introduced and nothing can collide.
            LetE (v, locs, ty, rhs) bod ->
              let (rb, rhs', n1) = go n rhs
                  (bb, bod', n2) = go n1 bod
               in (rb ++ [(v, locs, ty, rhs')] ++ bb, bod', n2)
            _ -> ([], ex, n)

        goArgs :: Int -> [Exp3] -> ([(Var, [()], Ty3, Exp3)], [Exp3], Int)
        goArgs n [] = ([], [], n)
        goArgs n (arg:rest) =
          let (bs1, arg', n1) = go n arg
              (bs2, rest', n2) = goArgs n1 rest
           in (bs1 ++ bs2, arg' : rest', n2)

    -- Every `let` binder in a plan's scalar expression, with repeats, so a
    -- name bound twice within one plan counts twice.
    scalarPlanLetBinders ScalarBufferPlan{sbpOp} =
      case sbpOp of
        ScalarCopy -> []
        ScalarExpr expr _ -> exprLetBinders expr

    exprLetBinders ex =
      case ex of
        LetE (v, _, _, rhs) bod -> v : (exprLetBinders rhs ++ exprLetBinders bod)
        PrimAppE _ args -> concatMap exprLetBinders args
        IfE a b c -> concatMap exprLetBinders [a, b, c]
        ProjE _ e -> exprLetBinders e
        _ -> []

    planDependencies ScalarBufferPlan{sbpOp} =
      case sbpOp of
        ScalarCopy -> []
        ScalarExpr _ deps -> L.sortOn (siiBufIx . snd) (M.toList deps)

    planDependencyInfos plan =
      M.elems $
        M.fromList
          [ (siiBufIx info, info)
          | (_, info) <- planDependencies plan
          ]

    mkGroupLastChunkBody pfx group =
      let updateCountFooter ix = loopBufferNameLocal pfx ix "update_count_footer"
       in mkLets
            [ (updateCountFooter ix, [], ProdTy [], Ext $ WriteCursorMutable (countFooterLocVar pfx ix) (VarE (nullFooter pfx)))
            | ix <- groupBufferIndices group
            ]
            (MkProdE [])

    mkGroupContinueChunkBody pfx group repCurrentNextFooter =
      let repIx = groupRepIx group
       in mkLets
            (concatMap (mkContinueOneBuffer pfx repIx repCurrentNextFooter) (groupBufferIndices group))
            (MkProdE [])

    mkContinueOneBuffer pfx repIx repCurrentNextFooter ix =
      let currentNextFooter =
            if ix == repIx
            then repCurrentNextFooter
            else loopBufferNameLocal pfx ix "current_next_footer"
          readCurrentNextFooter =
            if ix == repIx
            then []
            else [(currentNextFooter, [], CursorTy, Ext $ DerefMutCursor (nextFooterLocVar pfx ix))]
       in readCurrentNextFooter ++ mkContinueOneBufferLets pfx ix currentNextFooter

    mkContinueOneBufferLets pfx ix currentNextFooter =
      let boundaryCur = loopBufferNameLocal pfx ix "boundary_cur"
          boundaryPair = loopBufferNameLocal pfx ix "boundary_pair"
          boundaryAfter = loopBufferNameLocal pfx ix "boundary_after"
          redirPair = loopBufferNameLocal pfx ix "redir_pair"
          nextStart = loopBufferNameLocal pfx ix "next_start"
          growOut = loopBufferName pfx ix LbGrowOut
          setIn = loopBufferNameLocal pfx ix "set_in"
          nextNextFooter = loopBufferNameLocal pfx ix "next_next_footer"
          updateCountFooter = loopBufferNameLocal pfx ix "update_count_footer"
          updateNextFooter = loopBufferNameLocal pfx ix "update_next_footer"
       in [ (boundaryCur, [], CursorTy, Ext $ DerefMutCursor (inLocVar pfx ix))
          , (boundaryPair, [], ProdTy [(IntTy W64), CursorTy], Ext $ ReadTag boundaryCur)
          , (boundaryAfter, [], CursorTy, ProjE 1 (VarE boundaryPair))
          , (redirPair, [], ProdTy [CursorTy, CursorTy, (IntTy W64)], Ext $ ReadTaggedCursor boundaryAfter)
          , (nextStart, [], CursorTy, ProjE 0 (VarE redirPair))
          , (growOut, [], ProdTy [], Ext $ GrowRegion (outLocVar pfx ix) (outEndLocVar pfx ix))
          , (setIn, [], ProdTy [], Ext $ WriteCursorMutable (inLocVar pfx ix) (VarE nextStart))
          ]
          ++ mkDependencyContinueLets pfx ix
          ++
          [ (nextNextFooter, [], CursorTy, Ext $ ReadScalarCountNextFooter currentNextFooter)
          , (updateCountFooter, [], ProdTy [], Ext $ WriteCursorMutable (countFooterLocVar pfx ix) (VarE currentNextFooter))
          , (updateNextFooter, [], ProdTy [], Ext $ WriteCursorMutable (nextFooterLocVar pfx ix) (VarE nextNextFooter))
          ]

    -- Dependency cursors must follow the same chunk transitions as their
    -- consumer loop.  At a redirection boundary, read the dependent buffer's
    -- redirection tag and reset that dependency cursor to the next chunk
    -- start.  This is independent of the dependency buffer's own main loop.
    mkDependencyContinueLets pfx ix =
      case M.lookup ix planMap of
        Nothing -> []
        Just plan -> concatMap (mkDependencyContinue pfx ix) (planDependencyInfos plan)

    mkDependencyContinue pfx ix info
      | depIx == ix = []
      | otherwise =
          [ (depBoundaryCurVar pfx ix depIx, [], CursorTy, Ext $ DerefMutCursor (depLocVar pfx ix depIx))
          , (depBoundaryPairVar pfx ix depIx, [], ProdTy [(IntTy W64), CursorTy], Ext $ ReadTag (depBoundaryCurVar pfx ix depIx))
          , (depBoundaryAfterVar pfx ix depIx, [], CursorTy, ProjE 1 (VarE (depBoundaryPairVar pfx ix depIx)))
          , (depRedirPairVar pfx ix depIx, [], ProdTy [CursorTy, CursorTy, (IntTy W64)], Ext $ ReadTaggedCursor (depBoundaryAfterVar pfx ix depIx))
          , (depNextStartVar pfx ix depIx, [], CursorTy, ProjE 0 (VarE (depRedirPairVar pfx ix depIx)))
          , (depSetInVar pfx ix depIx, [], ProdTy [], Ext $ WriteCursorMutable (depLocVar pfx ix depIx) (VarE (depNextStartVar pfx ix depIx)))
          ]
      where
        depIx = siiBufIx info

    indexCursorExp arr ix = Ext $ IndexCursorArray arr ix

    substMany :: [(Var, Exp3)] -> Exp3 -> Exp3
    substMany replacements ex =
      foldl (\acc (old, new) -> substE (VarE old) new acc) ex replacements

collectScalarInputsWithRoles :: M.Map Var BufferRole -> [(Var, [()], Ty3, Exp3)] -> M.Map Var ScalarInputInfo
collectScalarInputsWithRoles roles binds = goTuple M.empty M.empty binds
  where
    goTuple _ acc [] = acc
    goTuple tupleMap acc ((v, _, _, rhs):rest) =
      case rhs of
        Ext (ReadScalar s cur) ->
          case M.lookup cur roles of
            Just (InputBuf ix) ->
              let tupleMap' = M.insert v (ScalarInputInfo s ix) tupleMap
               in goTuple tupleMap' acc rest
            _ -> goTuple tupleMap acc rest
        ProjE 0 (VarE tup) ->
          case M.lookup tup tupleMap of
            Just info -> goTuple tupleMap (M.insert v info acc) rest
            Nothing -> goTuple tupleMap acc rest
        _ -> goTuple tupleMap acc rest

-- | What 'collectPureBindings' learned about a branch's pure scalar bindings:
-- the ones cheap enough to inline by substitution, and -- in source order --
-- the ones that must stay as `let` bindings instead.
type PureBindEnv = (M.Map Var Exp3, [(Var, [()], Ty3, Exp3)])

-- | Normalize a scalar expression against the inline environment, then
-- re-attach the residual bindings it needs.
normalizeWithResiduals :: PureBindEnv -> Exp3 -> Exp3
normalizeWithResiduals (env, residuals) ex =
  wrapResidualBinds residuals (normalizePureExpr env ex)

-- | Wrap @ex@ in exactly those residual bindings it transitively depends on,
-- in their original order.
--
-- Walking the list in reverse is what makes one pass enough: by the time a
-- binding is considered, every binding that could reference it has already
-- been visited and contributed its own free variables to @need@.  A binding
-- not reached this way is not emitted at all, so an expression never carries
-- bindings it does not use.
wrapResidualBinds :: [(Var, [()], Ty3, Exp3)] -> Exp3 -> Exp3
wrapResidualBinds [] ex = ex
wrapResidualBinds residuals ex = mkLets keep ex
  where
    (_, keep) = L.foldl' step (gFreeVars ex, []) (reverse residuals)
    step (need, acc) b@(v, _, _, rhs)
      | v `S.member` need = (S.delete v need `S.union` gFreeVars rhs, b : acc)
      | otherwise = (need, acc)

-- | The substitution environment of pure bindings that may be inlined into a
-- scalar write's right-hand side.
--
-- Admission is deliberately narrower than "the RHS is a supported expression",
-- because this environment is applied by SUBSTITUTION: a binding admitted here
-- is re-inserted at every use.  Two things follow.
--
--   * Duplicating a total, effect-free expression only costs work.  Duplicating
--     a PARTIAL one duplicates a trap, and duplicating one that itself contains
--     a `let` duplicates the binder, so the same name would be bound twice in
--     one block.  Neither is acceptable, so a non-total or `let`-bearing RHS is
--     inlined only where it is used at most once -- in which case substitution
--     preserves the evaluation count exactly.
--   * When a binding is not admitted, its uses stay as free variables, the
--     write's dependency check fails, and the traversal simply stays scalar.
--     Losing an optimization is the correct outcome; duplicating an effect is
--     not.
collectPureBindings :: S.Set Var -> M.Map Var ScalarInputInfo -> M.Map Var Int
                    -> [(Var, [()], Ty3, Exp3)] -> PureBindEnv
collectPureBindings spineBinders scalarInputs useCounts binds =
  let (env, res) = go M.empty [] binds
   in (env, reverse res)
  where
    go env res [] = (env, res)
    go env res ((v, locs, ty, rhs):rest)
      | v `M.member` scalarInputs = go env res rest
      | otherwise =
          case normalizePureExpr env rhs of
            rhs'
              | Just cls <- scalarExprClass rhs'
              , inlinable cls rhs' v ->
                  go (M.insert v rhs' env) res rest
            -- Not cheap enough to duplicate, but still a total scalar
            -- expression: KEEP it, as a binding rather than a substitution.
            --
            -- Before this case existed the binding was simply dropped from the
            -- environment, its uses stayed free, and the write's dependency
            -- check below rejected them -- so a kernel whose arithmetic chain
            -- was deeper than the inline budget did not loopify at all, and
            -- therefore never reached the vectorizer either.  A binding
            -- emitted once preserves the evaluation count exactly, which is
            -- what substitution could not do; `wrapResidualBinds` re-attaches
            -- only the ones an expression actually needs, and
            -- 'ScalarExpr''s grammar already admits `LetE`
            -- ('anfScalarExpr' re-emits it at the same control point).
            --
            -- Restricted to 'EffTotal'.  A residual is re-attached at the
            -- point of USE, which for a write inside an `IfE` arm is a point
            -- the original binding did not dominate; skipping a total
            -- computation is unobservable, skipping a trap is not.
            rhs'
              | Just EffTotal <- scalarExprClass rhs' ->
                  go env ((v, locs, ty, rhs') : res) rest
            -- A PARTIAL binding on the unconditional spine, kept as a residual
            -- rather than dropped.
            --
            -- Dropping it is what stops `touchHotObjects` loopifying: `hot =
            -- (mod id stride) == 0` is used twice, so it can be neither
            -- substituted (that duplicates the trap) nor -- until now -- kept,
            -- and its uses stay free until the plan's free-variable check
            -- rejects them.  The traversal then also loses selective buffer
            -- sharing, which only runs on functions loopification rewrote.
            --
            -- Safe because of the SPINE restriction, and only because of it.
            -- The residual is re-attached by 'wrapResidualBinds' around the
            -- WHOLE plan expression, so it dominates both arms of any `IfE`
            -- the plan contains -- which is right for a binding the source
            -- evaluated unconditionally, and would be wrong for one the source
            -- guarded.  A guarded partial is not on the spine and still takes
            -- the drop below, so `if d == 0 then 7 else 100 / d` is unaffected.
            --
            -- The binding is recomputed once per consuming plan: production
            -- emits one loop per scalar buffer with no shared per-element
            -- scope, so there is nowhere to evaluate it just once.  That is
            -- unobservable -- the expression is pure, so the value is the same,
            -- and trapping twice is indistinguishable from trapping once --
            -- and it cannot SKIP a trap, because a binding no plan uses is
            -- dead and 'branchDropsEffect' already refuses those.
            rhs'
              | v `S.member` spineBinders
              , Just EffPartial <- scalarExprClass rhs' ->
                  go env ((v, locs, ty, rhs') : res) rest
            _ -> go env res rest

    -- Inline a binding into its uses ONLY when there is no alternative.
    -- Substitution duplicates a value once per use and those copies nest, so a
    -- total binding is never substituted: it is kept, and 'wrapResidualBinds'
    -- re-attaches it at its uses -- one binding, one operation, whatever the
    -- use count.
    --
    -- The exception is a NON-total single-use right-hand side.  It cannot
    -- become a residual (residuals re-attach at the point of use, which for a
    -- write inside an `IfE` arm the original binding did not dominate, and
    -- skipping a trap is observable), and inlining at its one use preserves the
    -- evaluation count exactly.
    --
    -- A multiply-used non-total binding is neither inlined nor kept: the
    -- write's dependency check then fails and the traversal stays scalar.
    --
    inlinable cls _rhs' v =
      let uses = M.findWithDefault 0 v useCounts
       in uses <= 1 && cls /= EffTotal


-- | Refuse to loopify a branch that would silently drop a trapping or
-- effectful computation.
--
-- The synthesized loop body is built ONLY from the extracted scalar plans plus
-- the verbatim tag copy, so any branch computation the plans do not mention
-- disappears.  For a dead binding that is total and effect-free that is
-- harmless.  For a dead binding that can trap it is a semantic change:
--
-- > Cons p x rst -> Cons p (let y = 100 / (x - x) in x * 0 + 7) (xform rst)
--
-- Gibbon's `let` is strict, so `gibbon2` divides by zero and exits 1, while
-- every loopified mode used to drop `y` entirely -- the division did not appear
-- in the generated C at all -- and printed 70.  `scanBranchBody` did not catch
-- it, because it classifies a `PrimAppE` by shape and a division looks like any
-- other arithmetic there.
--
-- Only DEAD bindings need this check: a partial computation that IS used flows
-- into a plan expression, and a used unsupported one makes that plan expression
-- fail 'scalarExprClass' anyway.
branchDropsEffect :: M.Map Var Int -> [(Var, [()], Ty3, Exp3)] -> Bool
branchDropsEffect useCounts binds = any dead binds
  where
    dead (v, _, _, rhs) =
      M.findWithDefault 0 v useCounts == 0
        -- `classifyScalarShape`, not `scalarExprClass`: an `ErrorP` right-hand
        -- side is not an ADMISSIBLE scalar expression, but it is still a scalar
        -- computation that would be dropped, and it is exactly the case that
        -- must block loopification.  Structural bindings (reads, writes, cursor
        -- bumps, the self call) classify as `Nothing` and are unaffected --
        -- most of them are dead, and the loop reproduces them itself.
        && maybe False (/= EffTotal) (classifyScalarShape rhs)

-- | Substitute @env@ for free variables, respecting lexical scope.
--
-- The `LetE` case is the reason this is not a plain fold: the binder shadows
-- any outer mapping for the same name inside the body, so the body is
-- normalized under @M.delete v env@.  Gibbon does establish globally unique
-- binders (`Gibbon.Passes.Freshen.freshNames` at L0, and every later pass uses
-- `gensym`), which would make capture impossible anyway -- but relying on that
-- silently would make this transformation wrong the day the invariant is
-- relaxed, so the shadowing is implemented rather than assumed.
--
-- The `let` itself is PRESERVED, not inlined into its uses: `anfScalarExpr`
-- re-emits it at the same control point.  Inlining here would evaluate the RHS
-- once per use.
normalizePureExpr :: M.Map Var Exp3 -> Exp3 -> Exp3
normalizePureExpr env ex =
  case ex of
    VarE v -> fromMaybe (VarE v) (M.lookup v env)
    LitE{} -> ex
    CharE{} -> ex
    FloatE{} -> ex
    LitSymE{} -> ex
    PrimAppE p args -> PrimAppE p (map (normalizePureExpr env) args)
    IfE a b c -> IfE (normalizePureExpr env a) (normalizePureExpr env b) (normalizePureExpr env c)
    ProjE i e -> ProjE i (normalizePureExpr env e)
    LetE (v, locs, ty, rhs) bod ->
      LetE (v, locs, ty, normalizePureExpr env rhs)
           (normalizePureExpr (M.delete v env) bod)
    _ -> ex

-- | How an operation behaves, for the purposes of deciding whether the loop
-- synthesizer may reproduce, reorder, drop or duplicate it.
--
-- The point of the datatype is that there is no default: a primitive this
-- module has not classified is 'EffUnsupported', not "probably fine".  The
-- previous predicate accepted @PrimAppE _ args@ for ANY primitive, which
-- silently admitted `ErrorP` (a terminating effect) and `RandP`
-- (nondeterministic) as though they were arithmetic.
data EffectClass
  = EffTotal        -- ^ pure, total, freely droppable and duplicable
  | EffPartial      -- ^ pure until it traps: `DivP`, `ModP`, `FDivP`
  | EffUnsupported  -- ^ effectful, nondeterministic, or simply not classified
  deriving (Show, Eq, Ord)

-- | Join two classifications: the worst wins.
effJoin :: EffectClass -> EffectClass -> EffectClass
effJoin = max

primEffectClass :: Prim Ty3 -> EffectClass
primEffectClass p =
  case p of
    -- Total arithmetic, comparison and conversion.
    AddP{} -> EffTotal ; SubP{} -> EffTotal ; MulP{} -> EffTotal ; ExpP{} -> EffTotal
    FAddP -> EffTotal ; FSubP -> EffTotal ; FMulP -> EffTotal ; FExpP -> EffTotal
    FSqrtP -> EffTotal ; FTanP -> EffTotal
    EqIntP{} -> EffTotal ; LtP{} -> EffTotal ; GtP{} -> EffTotal
    LtEqP{} -> EffTotal ; GtEqP{} -> EffTotal
    EqFloatP -> EffTotal ; FLtP -> EffTotal ; FGtP -> EffTotal
    FLtEqP -> EffTotal ; FGtEqP -> EffTotal
    EqCharP -> EffTotal ; EqSymP -> EffTotal
    AndP -> EffTotal ; OrP -> EffTotal
    MkTrue -> EffTotal ; MkFalse -> EffTotal
    IntConvertP{} -> EffTotal ; IntToFloatP{} -> EffTotal ; FloatToIntP -> EffTotal
    -- Pure, but they trap: they must stay in their original branch and must
    -- not be dropped or duplicated.
    DivP{} -> EffPartial ; ModP{} -> EffPartial ; FDivP -> EffPartial
    -- Everything else -- `ErrorP`, `RandP`, printing, reads, dictionaries,
    -- vectors, lists, sets, benchmark hooks -- is not something the synthesized
    -- loop reproduces, so it must keep the traversal scalar.
    _ -> EffUnsupported

-- | Classify a candidate scalar expression, or reject it as not being one.
--
-- This is the grammar admitted as a loopifiable scalar computation:
--
-- > ScalarExpr ::= var | literal
-- >              | PrimAppE p [ScalarExpr]      -- p classified above
-- >              | ProjE i ScalarExpr
-- >              | IfE ScalarExpr ScalarExpr ScalarExpr
-- >              | LetE (v, ty, ScalarExpr) ScalarExpr
--
-- `LetE` is included because natural source expressions with
-- more than one operation in a conditional arm are flattened into a `let`
-- inside that arm, so rejecting `LetE` rejected nested guards, multi-operation
-- arms and dependent temporaries outright -- they never reached the loopifier
-- at all, and stayed scalar with no diagnostic.
-- | The SHAPE classification: @Just c@ when the expression is built only from
-- values, primitives, projections, conditionals and lets, with @c@ the worst
-- effect class among its primitives; @Nothing@ when it contains a structural
-- form -- an `Ext`, a call, a case, a constructor -- that the loop synthesizer
-- reproduces itself rather than treating as a scalar computation.
--
-- The distinction between @Just EffUnsupported@ and @Nothing@ matters: the
-- first is "a computation this pass must not move, drop or duplicate", the
-- second is "not a scalar computation at all".  Collapsing them would make the
-- dead-binding check below either useless or unable to loopify anything, since
-- every read, write and cursor bump is a dead non-scalar binding.
classifyScalarShape :: Exp3 -> Maybe EffectClass
classifyScalarShape ex =
  case ex of
    VarE{} -> Just EffTotal
    LitE{} -> Just EffTotal
    CharE{} -> Just EffTotal
    FloatE{} -> Just EffTotal
    LitSymE{} -> Just EffTotal
    PrimAppE p args ->
      foldl effJoin (primAppEffectClass p args) <$> mapM classifyScalarShape args
    ProjE _ e -> classifyScalarShape e
    IfE a b c -> foldl effJoin EffTotal <$> mapM classifyScalarShape [a, b, c]
    LetE (_, _, _, rhs) bod ->
      effJoin <$> classifyScalarShape rhs <*> classifyScalarShape bod
    _ -> Nothing

-- | 'primEffectClass', refined by the arguments the primitive is applied to.
--
-- A division or remainder is 'EffPartial' because it CAN trap -- but when the
-- divisor is a literal the compiler can often see that it cannot, and calling
-- such an application total is a statement of fact, not a relaxation of the
-- rule.  It matters because a total binding may be kept as a residual and a
-- partial one may not, which is the difference between loopifying and staying
-- scalar.
--
-- The condition is NOT "the divisor is non-zero".  On x86-64 `idiv` also traps
-- when the quotient overflows, which happens for @INT_MIN / -1@ and
-- @INT_MIN % -1@ -- verified on this machine, and the reason
-- `GuardDivEdgeInt8.hs` puts MIN/-1 in its edge matrix.  A divisor of -1 is
-- therefore excluded along with 0; every other literal divisor is safe for
-- both operations at every width, since |d| > 1 makes the quotient strictly
-- smaller in magnitude than the dividend.
--
-- Floating division does not trap (IEEE gives infinity or NaN), but it is left
-- 'EffPartial' here: this module's job is not to relitigate that
-- classification, only to notice when an integer divisor is a safe literal.
primAppEffectClass :: Prim Ty3 -> [Exp3] -> EffectClass
primAppEffectClass p args =
  case (p, args) of
    (DivP{}, [_, d]) | safeDivisor d -> EffTotal
    (ModP{}, [_, d]) | safeDivisor d -> EffTotal
    _ -> primEffectClass p
  where
    -- The width annotation is irrelevant: 0 and -1 are the only two divisors
    -- that can trap, at every width, and a literal is the same value however
    -- it is annotated.
    safeDivisor (LitE _ n) = n /= 0 && n /= (-1)
    safeDivisor _ = False

-- | Admissibility as a loopifiable scalar expression: the right shape, and no
-- unclassified or effectful primitive anywhere inside it.
scalarExprClass :: Exp3 -> Maybe EffectClass
scalarExprClass ex =
  case classifyScalarShape ex of
    Just cls | cls /= EffUnsupported -> Just cls
    _ -> Nothing

isSupportedPureExpr :: Exp3 -> Bool
isSupportedPureExpr = isJust . scalarExprClass

-- | Free occurrences of each variable, as a multiset.
--
-- Used to decide whether a binding may be substituted at its uses.  Binders are
-- not removed from the count, so a shadowed use is counted too; that can only
-- make a binding look MORE used than it is, which errs toward keeping the
-- traversal scalar rather than toward duplicating work.
occurrenceCounts :: Exp3 -> M.Map Var Int
occurrenceCounts = go
  where
    go ex =
      case ex of
        VarE v -> M.singleton v 1
        LetE (_, _, _, rhs) bod -> M.unionWith (+) (go rhs) (go bod)
        IfE a b c -> M.unionsWith (+) (map go [a, b, c])
        PrimAppE _ args -> M.unionsWith (+) (map go args)
        AppE _ _ _ args -> M.unionsWith (+) (map go args)
        ProjE _ e -> go e
        MkProdE es -> M.unionsWith (+) (map go es)
        CaseE scrt brs -> M.unionsWith (+) (go scrt : [ go r | (_, _, r) <- brs ])
        DataConE _ _ es -> M.unionsWith (+) (map go es)
        TimeIt e _ _ -> go e
        WithArenaE _ e -> go e
        SpawnE _ _ args -> M.unionsWith (+) (map go args)
        MapE (_, _, e1) e2 -> M.unionWith (+) (go e1) (go e2)
        FoldE (_, _, e1) (_, _, e2) e3 -> M.unionsWith (+) (map go [e1, e2, e3])
        Ext (ForE _ bound bod) -> M.unionWith (+) (go bound) (go bod)
        Ext (WhileCursor _ bod) -> go bod
        Ext (WhileCursorEnd _ _ bod) -> go bod
        Ext (WriteScalar _ _ rhs) -> go rhs
        Ext (WriteTaggedCursor _ rhs) -> go rhs
        Ext (WriteCursorMutable _ rhs) -> go rhs
        Ext (WriteList _ rhs _) -> go rhs
        Ext (WriteVector _ rhs _) -> go rhs
        Ext (AddCursor _ rhs) -> go rhs
        Ext (BumpCursorMutable _ rhs) -> go rhs
        Ext (AddrOfCursor rhs) -> go rhs
        Ext (LetAvail _ bod) -> go bod
        Ext (Assert rhs) -> go rhs
        _ -> M.empty

collectMentionedDataCons :: Exp3 -> [DataCon]
collectMentionedDataCons ex =
  case ex of
    VarE{} -> []
    LitE{} -> []
    CharE{} -> []
    FloatE{} -> []
    LitSymE{} -> []
    AppE _ _ _ args -> concatMap collectMentionedDataCons args
    PrimAppE _ args -> concatMap collectMentionedDataCons args
    LetE (_, _, _, rhs) bod ->
      collectMentionedDataCons rhs ++ collectMentionedDataCons bod
    IfE a b c ->
      collectMentionedDataCons a
        ++ collectMentionedDataCons b
        ++ collectMentionedDataCons c
    MkProdE ls -> concatMap collectMentionedDataCons ls
    ProjE _ e -> collectMentionedDataCons e
    CaseE scrt brs ->
      collectMentionedDataCons scrt
        ++ concatMap
          (\(dcon, _, rhs) -> dcon : collectMentionedDataCons rhs)
          brs
    DataConE _ dcon args -> dcon : concatMap collectMentionedDataCons args
    TimeIt e _ _ -> collectMentionedDataCons e
    WithArenaE _ e -> collectMentionedDataCons e
    SpawnE _ _ args -> concatMap collectMentionedDataCons args
    SyncE -> []
    MapE (_, _, e1) e2 ->
      collectMentionedDataCons e1 ++ collectMentionedDataCons e2
    FoldE (_, _, e1) (_, _, e2) e3 ->
      collectMentionedDataCons e1
        ++ collectMentionedDataCons e2
        ++ collectMentionedDataCons e3
    Ext ext ->
      case ext of
        ReadScalar{} -> []
        WriteScalar _ _ rhs -> collectMentionedDataCons rhs
        ReadTag{} -> []
        WriteTag dcon _ -> [dcon]
        WriteTagPacked _ rhs -> collectMentionedDataCons rhs
        TagCursor{} -> []
        WriteCursorIndirection{} -> []
        WriteCursorSelectiveIndirection _ _ _ mask -> collectMentionedDataCons mask
        UnwrapSelectiveIndirections{} -> []
        WriteTaggedCursor _ rhs -> collectMentionedDataCons rhs
        MemCpy{} -> []
        ReadTaggedCursor{} -> []
        ReadCursor{} -> []
        GrowRegion{} -> []
        WriteCursorMutable _ rhs -> collectMentionedDataCons rhs
        ReadList{} -> []
        WriteList _ rhs _ -> collectMentionedDataCons rhs
        ReadVector{} -> []
        WriteVector _ rhs _ -> collectMentionedDataCons rhs
        MakeCursorArray{} -> []
        IndexCursorArray{} -> []
        AddCursor _ rhs -> collectMentionedDataCons rhs
        BumpCursorMutable _ rhs -> collectMentionedDataCons rhs
        AddrOfCursor rhs -> collectMentionedDataCons rhs
        DerefMutCursor{} -> []
        CastPtr{} -> []
        SubPtr{} -> []
        NewBuffer{} -> []
        ScopedBuffer{} -> []
        NewParBuffer{} -> []
        ScopedParBuffer{} -> []
        EndOfBuffer{} -> []
        MMapFileSize{} -> []
        SizeOfPacked{} -> []
        SizeOfScalar{} -> []
        BoundsCheck{} -> []
        BoundsCheckVector{} -> []
        IndirectionBarrier{} -> []
        BumpArenaRefCount{} -> []
        NullCursor -> []
        InitCursor{} -> []
        RetE ls -> concatMap collectMentionedDataCons ls
        GetCilkWorkerNum -> []
        LetAvail _ bod -> collectMentionedDataCons bod
        AllocateTagHere{} -> []
        AllocateScalarsHere{} -> []
        StartTagAllocation{} -> []
        EndTagAllocation{} -> []
        StartScalarsAllocation{} -> []
        EndScalarsAllocation{} -> []
        ScalarCountBump dcon _ -> [dcon]
        ScalarCountBind{} -> []
        ScalarCountFinalize{} -> []
        ScalarCountSet{} -> []
        ScalarCountCopyAll{} -> []
        ReadScalarCount{} -> []
        ReadScalarCountFirstFooter{} -> []
        ReadScalarCountNextFooter{} -> []
        ForE _ bound bod ->
          collectMentionedDataCons bound ++ collectMentionedDataCons bod
        WhileCursor _ bod -> collectMentionedDataCons bod
        WhileCursorEnd _ _ bod -> collectMentionedDataCons bod
        VecBroadcast _ _ val -> collectMentionedDataCons val
        VecLoad{} -> []
        VecAdd _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecSub _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecMul _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecDiv _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecMod _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecCmp _ _ _ a b -> collectMentionedDataCons a ++ collectMentionedDataCons b
        VecSelect _ _ m a b -> collectMentionedDataCons m ++ collectMentionedDataCons a ++ collectMentionedDataCons b
        VecStore _ _ _ val -> collectMentionedDataCons val
        SSPush{} -> []
        SSPop{} -> []
        Assert rhs -> collectMentionedDataCons rhs
