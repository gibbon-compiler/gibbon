{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

-- | The compiler pipeline, assembled from several passes.

module Gibbon.Compiler
    ( -- * Compiler entrypoints
      compile, compileCmd
      -- * Configuration options and parsing
     , Config (..), Mode(..), Input(..)
     , configParser, configWithArgs, defaultConfig
      -- * Some other helper fns
     , compileAndRunExe
    )
  where

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad.State.Strict
import           Control.Monad.Reader (ask)
import           Data.Set as S hiding (map)
#if !MIN_VERSION_base(4,11,0)
import           Data.Monoid
#endif
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.IO.Error (isDoesNotExistError)
import           System.Process
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.Interp
import           Gibbon.DynFlags
import qualified Gibbon.HaskellFrontend as HS
import qualified Gibbon.L1.Syntax as L1
import qualified Gibbon.L2.Syntax as L2
-- import qualified Gibbon.L3.Syntax as L3
import qualified Gibbon.L4.Syntax as L4
import qualified Gibbon.SExpFrontend as SExp
import qualified Gibbon.L1.Interp as SI
import           Gibbon.TargetInterp (Val (..), execProg)

-- Compiler passes
import qualified Gibbon.L1.Typecheck as L1
import qualified Gibbon.L2.Typecheck as L2
import qualified Gibbon.L3.Typecheck as L3
import           Gibbon.Passes.Freshen        (freshNames)
import           Gibbon.Passes.Flatten        (flattenL1, flattenL2, flattenL3)
import           Gibbon.Passes.InlineTriv     (inlineTriv)

import           Gibbon.Passes.DirectL3       (directL3)
import           Gibbon.Passes.InferLocations (inferLocs)
import           Gibbon.Passes.RepairProgram  (repairProgram)
import           Gibbon.Passes.RemoveCopies   (removeCopies)
import           Gibbon.Passes.InferMultiplicity (inferRegScope)
import           Gibbon.Passes.BoundsCheck    (boundsCheck)
import           Gibbon.Passes.ThreadRegions  (threadRegions)
import           Gibbon.Passes.InferEffects   (inferEffects)
import           Gibbon.Passes.RouteEnds      (routeEnds)
import           Gibbon.Passes.Cursorize      (cursorize)
-- import           Gibbon.Passes.FindWitnesses  (findWitnesses)
-- import           Gibbon.Passes.ShakeTree      (shakeTree)
import           Gibbon.Passes.HoistNewBuf    (hoistNewBuf)
import           Gibbon.Passes.Unariser       (unariser)
import           Gibbon.Passes.Lower          (lower)
import           Gibbon.Passes.FollowRedirects(followRedirects)
import           Gibbon.Passes.RearrangeFree  (rearrangeFree)
import           Gibbon.Passes.Codegen        (codegenProg)
import           Gibbon.Pretty
#ifdef LLVM_ENABLED
import qualified Gibbon.Passes.LLVM.Codegen as LLVM
#endif

----------------------------------------
-- PASS STUBS
----------------------------------------
-- All of these need to be implemented, but are just the identity
-- function for now.  Move to Passes/ when implemented


-- | Find all local variables bound by case expressions which must be
-- traversed, but which are not by the current program.
findMissingTraversals :: L2.Prog2 -> PassM (Set Var)
findMissingTraversals _ = pure S.empty

-- | Add calls to an implicitly-defined, polymorphic "traverse"
-- function of type `p -> ()` for any packed type p.
addTraversals :: Set Var -> L2.Prog2 -> PassM L2.Prog2
addTraversals _ p = pure p

-- | Generate code
lowerCopiesAndTraversals :: L2.Prog2 -> PassM L2.Prog2
lowerCopiesAndTraversals p = pure p


-- Configuring and launching the compiler.
--------------------------------------------------------------------------------

suppress_warnings :: String
suppress_warnings = " -Wno-incompatible-pointer-types -Wno-int-conversion -Wno-int-to-pointer-cast "

configParser :: Parser Config
configParser = Config <$> inputParser
                      <*> modeParser
                      <*> ((Just <$> strOption (long "bench-input" <> metavar "FILE" <>
                                      help ("Hard-code the input file for --bench-fun, otherwise it"++
                                            " becomes a command-line argument of the resulting binary."++
                                            " Also we RUN the benchmark right away if this is provided.")))
                          <|> pure Nothing)
                      <*> (option auto (short 'v' <> long "verbose" <>
                                       help "Set the debug output level, 1-5, mirrors DEBUG env var.")
                           <|> pure 1)
                      <*> ((strOption $ long "cc" <> help "Set C compiler, default 'gcc'")
                            <|> pure (cc defaultConfig))
                      <*> ((strOption $ long "optc" <> help "Set C compiler options, default '-std=gnu11 -O3'")
                           <|> pure (optc defaultConfig))
                      <*> ((fmap Just (strOption $ long "cfile" <> help "Set the destination file for generated C code"))
                           <|> pure (cfile defaultConfig))
                      <*> ((fmap Just (strOption $ short 'o' <> long "exefile" <>
                                       help "Set the destination file for the executable"))
                           <|> pure (exefile defaultConfig))
                      <*> backendParser
                      <*> dynflagsParser
 where
  inputParser :: Parser Input
                -- I'd like to display a separator and some more info.  How?
  inputParser = -- infoOption "foo" (help "bar") <*>
                flag' Haskell (long "hs")  <|>
                flag Unspecified SExpr (long "gib")

  modeParser = -- infoOption "foo" (help "bar") <*>
               flag' ToParse (long "parse" <> help "Only parse, then print & stop") <|>
               flag' ToC     (long "toC" <> help "Compile to a C file, named after the input") <|>
               flag' Interp1 (long "interp1" <> help "run through the interpreter early, right after parsing") <|>
               flag' Interp2 (short 'i' <> long "interp2" <>
                              help "Run through the interpreter after cursor insertion") <|>
               flag' RunExe  (short 'r' <> long "run"     <> help "Compile and then run executable") <|>
               (Bench <$> toVar <$> strOption (short 'b' <> long "bench-fun" <> metavar "FUN" <>
                                     help ("Generate code to benchmark a 1-argument FUN against a input packed file."++
                                           "  If --bench-input is provided, then the benchmark is run as well.")))

  -- use C as the default backend
  backendParser :: Parser Backend
  backendParser = flag C LLVM (long "llvm" <> help "use the llvm backend for compilation")


-- | Parse configuration as well as file arguments.
configWithArgs :: Parser (Config,[FilePath])
configWithArgs = (,) <$> configParser
                     <*> some (argument str (metavar "FILES..."
                                             <> help "Files to compile."))

--------------------------------------------------------------------------------

-- | Command line version of the compiler entrypoint.  Parses command
-- line arguments given as string inputs.  This also allows us to run
-- conveniently from within GHCI.  For example:
--
-- >  compileCmd $ words $ " -r -p -v5 examples/test11c_funrec.gib "
--
compileCmd :: [String] -> IO ()
compileCmd args = withArgs args $
    do (cfg,files) <- execParser opts
       case files of
         [f] -> compile cfg f
         _ -> do dbgPrintLn 1 $ "Compiling multiple files:  "++show files
                 mapM_ (compile cfg) files
  where
    opts = info (helper <*> configWithArgs)
      ( fullDesc
     <> progDesc "Compile FILES according to the below options."
     <> header "A compiler for a minature tree traversal language" )


sepline :: String
sepline = replicate 80 '='


data CompileState = CompileState
    { cnt :: Int -- ^ Gensym counter
    , result :: Maybe Value -- ^ Result of evaluating output of prior pass, if available.
    }

-- | Compiler entrypoint, given a full configuration and a list of
-- files to process, do the thing.
compile :: Config -> FilePath -> IO ()
compile config@Config{mode,input,verbosity,backend,cfile,dynflags} fp0 = do
  -- set the env var DEBUG, to verbosity, when > 1
  setDebugEnvVar verbosity

  -- parse the input file
  (parsed, fp) <- parseInput input fp0
  (l1, cnt0) <- parsed

  case mode of
    Interp1 -> runL1 l1
    ToParse -> dbgPrintLn 0 $ sdoc l1

    _ -> do
      dbgPrintLn passChatterLvl $
          " [compiler] pipeline starting, parsed program: "++
            if dbgLvl >= passChatterLvl+1
            then "\n"++sepline ++ "\n" ++ sdoc l1
            else show (length (sdoc l1)) ++ " characters."

      -- (Stage 1) Run the program through the interpreter
      initResult <- withPrintInterpProg l1

      -- (Stage 2) C/LLVM codegen
      let outfile = getOutfile backend fp cfile

      -- run the initial program through the compiler pipeline
      stM <- return $ passes config l1
      l4  <- evalStateT stM (CompileState {cnt=cnt0, result=initResult})

      if mode == Interp2
      then do
        l4res <- execProg l4
        mapM_ (\(IntVal v) -> liftIO $ print v) l4res
        exitSuccess
      else do
        str <- case backend of
                 C    -> codegenProg dynflags l4
#ifdef LLVM_ENABLED
                 LLVM -> LLVM.codegenProg True l4
#endif
                 LLVM -> error $ "Cannot execute through the LLVM backend. To build Gibbon with LLVM: "
                         ++ "stack build --flag gibbon:llvm_enabled"

        -- The C code is long, so put this at a higher verbosity level.
        dbgPrint passChatterLvl $ " [compiler] Final C codegen: " ++show (length str) ++" characters."
        dbgPrintLn 4 $ sepline ++ "\n" ++ str

        clearFile outfile
        writeFile outfile str

        -- (Stage 3) Code written, now compile if warranted.
        when (mode == ToExe || mode == RunExe || isBench mode ) $ do
          compileAndRunExe config fp >>= putStr
          return ()


-- | The compiler's policy for running/printing L1 programs.
runL1 :: L1.Prog1 -> IO ()
runL1 l1 = do
    -- FIXME: no command line option atm.  Just env vars.
    runConf <- getRunConfig []
    dbgPrintLn 2 $ "Running the following through L1.Interp:\n "++sepline ++ "\n" ++ sdoc l1
    SI.execAndPrint runConf l1
    exitSuccess

-- | The compiler's policy for running/printing L2 programs.
runL2 :: L2.Prog2 -> IO ()
runL2 l2 = runL1 (L2.revertToL1 l2)

-- | Set the env var DEBUG, to verbosity, when > 1
-- TERRIBLE HACK!!
-- This verbosity value is global, "pure" and can be read anywhere
--
setDebugEnvVar :: Int -> IO ()
setDebugEnvVar verbosity =
  when (verbosity > 1) $ do
    setEnv "DEBUG" (show verbosity)
    l <- evaluate dbgLvl
    hPutStrLn stderr$ " ! We set DEBUG based on command-line verbose arg: "++show l


-- |
parseInput :: Input -> FilePath -> IO (IO (L1.Prog1, Int), FilePath)
parseInput ip fp =
  case ip of
    Haskell -> return (HS.parseFile fp, fp)
    SExpr   -> return (SExp.parseFile fp, fp)
    Unspecified ->
      case takeExtension fp of
        ".hs" -> return (HS.parseFile fp, fp)
        ".sexp" -> return (SExp.parseFile fp, fp)
        ".rkt"  -> return (SExp.parseFile fp, fp)
        ".gib"  -> return (SExp.parseFile fp, fp)
        oth -> do
          -- A silly hack just out of sheer laziness vis-a-vis tab completion:
          let f1 = fp ++ ".gib"
              f2 = fp ++ "gib"
          f1' <- doesFileExist f1
          f2' <- doesFileExist f2
          if f1' && oth == ""
            then return (SExp.parseFile f1, f2)
            else if f2' && oth == "."
                   then return (SExp.parseFile f2, f2)
                   else error$ "compile: unrecognized file extension: "++
                        show oth++"  Please specify compile input format."


-- |
withPrintInterpProg :: L1.Prog1 -> IO (Maybe Value)
withPrintInterpProg l1 =
  if dbgLvl >= interpDbgLevel
  then do
    -- FIXME: no command line option atm.  Just env vars.
    runConf <- getRunConfig []
    (val,_stdout) <- interpProg runConf l1
    dbgPrintLn 2 $ " [eval] Init prog evaluated to: "++show val
    return $ Just val
  else
    return Nothing

-- | Compile and run the generated code if appropriate
--
compileAndRunExe :: Config -> FilePath -> IO String
compileAndRunExe cfg@Config{backend,benchInput,mode,cfile,exefile} fp = do
  exepath <- makeAbsolute exe
  clearFile exepath

  -- (Stage 4) Codegen finished, generate a binary
  dbgPrintLn minChatLvl cmd
  cd <- system cmd
  case cd of
    ExitFailure n -> error$ (show backend) ++" compiler failed!  Code: "++show n
    ExitSuccess -> do
      -- (Stage 5) Binary compiled, run if appropriate
      let runExe extra = do
            (_,Just hout,_, phandle) <- createProcess (shell (exepath++extra))
                                                 { std_out = CreatePipe }
            exitCode <- waitForProcess phandle
            case exitCode of
                ExitSuccess   -> hGetContents hout
                ExitFailure n -> die$ "Treelang program exited with error code  "++ show n

      runConf <- getRunConfig [] -- FIXME: no command line option atm.  Just env vars.
      case benchInput of
        -- CONVENTION: In benchmark mode we expect the generated executable to take 2 extra params:
        Just _ | isBench mode   -> runExe $ " " ++show (rcSize runConf) ++ " " ++ show (rcIters runConf)
        _      | mode == RunExe -> runExe ""
        _                                -> return ""
  where outfile = getOutfile backend fp cfile
        exe = getExeFile backend fp exefile
        pointer = gopt Opt_Pointer $ dynflags cfg
        links = if pointer then " -lgc " else ""
        cmd = compilationCmd backend cfg ++ outfile ++ links ++ " -o " ++ exe


-- | Return the correct filename to store the generated code,
-- based on the backend used, and override options specified
--
getOutfile :: Backend -> FilePath -> Maybe FilePath -> FilePath
getOutfile _ _ (Just override) = override
getOutfile backend fp Nothing =
  replaceExtension fp $
    case backend of
      C    -> ".c"
      LLVM -> ".ll"

-- | Return the correct filename for the generated exe,
-- based on the backend used, and override options specified
--
getExeFile :: Backend -> FilePath -> Maybe FilePath -> FilePath
getExeFile _ _ (Just override) = override
getExeFile backend fp Nothing =
  let fp' = case backend of
               C -> fp
               LLVM -> replaceFileName fp ((takeBaseName fp) ++ "_llvm")
  in replaceExtension fp' ".exe"

-- | Compilation command
--
compilationCmd :: Backend -> Config -> String
compilationCmd LLVM _   = "clang-5.0 lib.o "
compilationCmd C config = (cc config) ++" -std=gnu11 "
                          ++(if bumpAlloc then "-DBUMPALLOC " else "")
                          ++(if pointer then "-D_POINTER " else "")
                          ++(optc config)++"  "
                          ++(if warnc then "" else suppress_warnings)
  where dflags = dynflags config
        bumpAlloc = gopt Opt_BumpAlloc dflags
        pointer = gopt Opt_Pointer dflags
        warnc = gopt Opt_Warnc dflags

-- |
isBench :: Mode -> Bool
isBench (Bench _) = True
isBench _ = False

-- | The debug level at which we start to call the interpreter on the program during compilation.
interpDbgLevel :: Int
interpDbgLevel = 1

-- |
clearFile :: FilePath -> IO ()
clearFile fileName = removeFile fileName `catch` handleErr
  where
   handleErr e | isDoesNotExistError e = return ()
               | otherwise = throwIO e

--------------------------------------------------------------------------------

-- | Replace the main function with benchmark code
--
benchMainExp :: L1.Prog1 -> PassM L1.Prog1
benchMainExp l1 = do
  Config{benchInput,dynflags,mode} <- ask
  case mode of
    Bench fnname -> do
      let tmp = "bnch"
          (arg@(L1.PackedTy tyc _),ret) = L1.getFunTy fnname l1
          -- At L1, we assume ReadPackedFile has a single return value:
          newExp = L1.LetE (toVar tmp, [],
                            arg,
                            l$ L1.PrimAppE
                            (L1.ReadPackedFile benchInput tyc arg) [])
                   $ l$ L1.LetE (toVar "benchres", [],
                             ret,
                             l$ L1.TimeIt
                             (l$ L1.AppE fnname []
                              (l$ L1.VarE (toVar tmp))) ret True)
                   $
                    -- FIXME: should actually return the result,
                    -- as soon as we are able to print it.
                   (if (gopt Opt_BenchPrint dynflags)
                    then l$ L1.VarE (toVar "benchres")
                    else l$ L1.PrimAppE L1.MkTrue [])
      -- Initialize the main expression with a void type. The typechecker will fix it later.
      return $ l1{ L1.mainExp = Just $ (l$ newExp, L1.ProdTy []) }
    _ -> return l1

-- | The main compiler pipeline
passes :: Config -> L1.Prog1 -> StateT CompileState IO L4.Prog
passes config@Config{dynflags} l1 = do
      let packed     = gopt Opt_Packed dynflags
          biginf     = gopt Opt_BigInfiniteRegions dynflags
          gibbon1    = gopt Opt_Gibbon1 dynflags
          no_rcopies = gopt Opt_No_RemoveCopies dynflags
      l1 <- goE "typecheck"  L1.tcProg                  l1
      l1 <- goE "freshNames" freshNames                 l1

      -- If we are executing a benchmark, then we
      -- replace the main function with benchmark code:
      l1 <- goE "benchMainExp" benchMainExp             l1

      l1 <- goE "typecheck"     L1.tcProg               l1
      l1 <- goE "flatten"       flattenL1               l1
      l1 <- goE "inlineTriv"    inlineTriv              l1

      -- TODO: Write interpreters for L2 and L3
      l3 <- if packed
            then do
              -- TODO: push data contstructors under conditional
              -- branches before InferLocations.

              -- Note: L1 -> L2
              l2 <- go "inferLocations"   inferLocs     l1
              l2 <- go "L2.flatten"       flattenL2     l2

              l2 <- if gibbon1 || no_rcopies
                    then return l2
                    else go "removeCopies" removeCopies l2

              l2 <- go "inferEffects"     inferEffects  l2

              l2 <- go "repairProgram"(repairProgram l1) l2

              l2 <- go "inferRegScope"    inferRegScope l2

              l2 <- go "L2.typecheck"     L2.tcProg     l2
              l2 <- go "routeEnds"        routeEnds     l2
              l2 <- go "L2.typecheck"     L2.tcProg     l2

              l2 <- if gibbon1 || biginf
                    then return l2
                    else go "boundsCheck" boundsCheck   l2

              l2 <- go "threadRegions"    threadRegions l2
              -- Note: L2 -> L3
              l3 <- go "cursorize"        cursorize     l2
              l3 <- go "L3.flatten"       flattenL3     l3
              l3 <- go "L3.typecheck"     L3.tcProg     l3
              l3 <- go "hoistNewBuf"      hoistNewBuf   l3
              return l3
            else do
              l3 <- go "directL3"         directL3      l1
              return l3

      l3 <- go "L3.typecheck"   L3.tcProg               l3
      l3 <- go "unariser"       unariser                l3
      l3 <- go "L3.typecheck"   L3.tcProg               l3
      l3 <- go "L3.flatten"     flattenL3               l3
      -- Note: L3 -> L4
      l4 <- go "lower"          lower                   l3

      l4 <- if gibbon1
            then return l4
            else go "followRedirects" followRedirects   l4
      l4 <- go "rearrangeFree"  rearrangeFree           l4
      return l4
  where
      go :: PassRunner a b
      go = pass config

      goE :: (Interp b) => PassRunner a b
      goE = passE config

type PassRunner a b = (Printer b, Out b, NFData a, NFData b) =>
                      String -> (a -> PassM b) -> a -> StateT CompileState IO b


-- | Run a pass and return the result
--
pass :: Config -> PassRunner a b
pass config who fn x = do
  cs@CompileState{cnt} <- get
  x' <- if dbgLvl >= passChatterLvl
        then lift $ evaluate $ force x
        else return x
  lift$ dbgPrint passChatterLvl $ " [compiler] Running pass, " ++who

  let (y,cnt') = runPassM config cnt (fn x')
  put cs{cnt=cnt'}
  y' <- if dbgLvl >= passChatterLvl
        then lift $ evaluate $ force y
        else return y
  if dbgLvl >= passChatterLvl+1
     then lift$ dbgPrintLn (passChatterLvl+1) $ "Pass output:\n"++sepline++"\n"++pprinter y'
     -- TODO: Switch to a node-count for size output (add to GenericOps):
     else lift$ dbgPrintLn passChatterLvl $ "   => "++ show (length (sdoc y')) ++ " characters output."
  return y'


passChatterLvl :: Int
passChatterLvl = 3


-- | Like 'pass', but also evaluates and checks the result.
--
passE :: Config -> Interp p2 => PassRunner p1 p2
passE config@Config{mode} = wrapInterp mode (pass config)


-- | An alternative version that allows FAILURE while running
-- the interpreter part.
-- FINISHME! For now not interpreting.
--
passF :: Config -> PassRunner p1 p2
passF config = pass config


-- | Wrapper to enable running a pass AND interpreting the result.
--
wrapInterp :: (NFData p1, NFData p2, Interp p2, Out p2, Printer p2) =>
              Mode -> PassRunner p1 p2 -> String -> (p1 -> PassM p2) -> p1 ->
              StateT CompileState IO p2
wrapInterp mode pass who fn x =
  do CompileState{result} <- get
     p2 <- pass who fn x
     -- In benchmark mode we simply turn OFF the interpreter.
     -- This decision should be finer grained.
     when (dbgLvl >= interpDbgLevel && not (isBench mode)) $ lift $ do
       let Just res1 = result
       -- FIXME: no command line option atm.  Just env vars.
       runConf <- getRunConfig []
       let res2 = interpNoLogs runConf p2
       res2' <- catch (evaluate (force res2))
                (\exn -> error $ "Exception while running interpreter on pass result:\n"++sepline++"\n"
                         ++ show (exn::SomeException) ++ "\n"++sepline++"\nProgram was: "++abbrv 300 p2)
       unless (show res1 == res2') $
         error $ "After pass "++who++", evaluating the program yielded the wrong answer.\nReceived:  "
         ++show res2'++"\nExpected:  "++show res1
       dbgPrintLn 5 $ " [interp] answer was: "++sdoc res2'
     return p2
