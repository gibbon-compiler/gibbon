module TestRunner
    (main) where

import Data.List
import Data.Foldable
import Options.Applicative hiding (empty)
import System.Clock
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.PrettyPrint hiding ((<>))

import qualified Text.PrettyPrint as PP
import qualified Data.Map as M

--------------------------------------------------------------------------------
-- A single test

data Test = Test
    { name   :: String
    , dir    :: FilePath
    , expect :: Expect
    }
  deriving (Show, Eq, Read)

instance Ord Test where
    compare t1 t2 = compare (name t1) (name t2)

data Expect = Pass | Fail
  deriving (Show, Eq, Read, Ord)

findTestFiles :: [(FilePath, Expect)] -> IO [Test]
findTestFiles dirs = concat <$> mapM go dirs
  where
    go :: (FilePath, Expect) -> IO [Test]
    go (dir, expect) =
        map (\fp -> Test fp dir expect) <$>
        filter isGibbonTestFile <$>
        listDirectory dir

isGibbonTestFile :: FilePath -> Bool
isGibbonTestFile fp =
    -- Add a .hs extension here soon...
    takeExtension fp `elem` [".gib"]

--------------------------------------------------------------------------------
-- Test configuration

data TestConfig = TestConfig
    { runFailing  :: Bool     -- ^ Allows us to inspect all failures in a single report
    , verbosity   :: Int      -- ^ Ranges from [0..5], and is passed on to Gibbon
    , summaryFile :: FilePath -- ^ File in which to store the test summary
    , tempdir     :: FilePath -- ^ Temporary directory to store the build artifacts
    }
  deriving (Show, Eq, Read, Ord)

defaultTestConfig :: TestConfig
defaultTestConfig = TestConfig
    { runFailing  = False
    , verbosity   = 1
    , summaryFile = "gibbon-test-summary.txt"
    , tempdir     = "examples/build_tmp"
    }


configParser :: Parser TestConfig
configParser = TestConfig
                   <$> switch (long "run-failing" <>
                               help "Run tests in the error/ directory too." <>
                               showDefault)
                   <*> option auto (short 'v' <>
                                    help "Verbosity level." <>
                                    showDefault <>
                                    value (verbosity defaultTestConfig))
                   <*> strOption (long "summary-file" <>
                                  help "File in which to store the test summary" <>
                                  showDefault <>
                                  value (summaryFile defaultTestConfig))
                   <*> strOption (long "tempdir" <>
                                  help "Temporary directory to store the build artifacts" <>
                                  showDefault <>
                                  value (tempdir defaultTestConfig))
-- TODO: add a parser to allow specifying overrides via command line

-- Not used atm.
-- | Gibbon mode to run programs in
data Mode = Packed | Pointer | Interp1
  deriving (Eq, Read, Ord)

data TestRun = TestRun
    { tests :: [Test]
    , startTime :: TimeSpec
    , expectedPasses :: [Test]
    , unexpectedPasses :: [Test]
    , expectedFailures :: [Test]
    , unexpectedFailures :: [Test]
    , errors :: M.Map String String
    }
  deriving (Show, Eq, Read, Ord)

clk :: Clock
clk = RealtimeCoarse

getTestRun :: TestConfig -> IO TestRun
getTestRun tc = do
    tests <- findTestFiles rootDirs
    time <- getTime clk
    return $ TestRun
        { tests = tests
        , startTime = time
        , expectedPasses = []
        , unexpectedPasses = []
        , expectedFailures = []
        , unexpectedFailures = []
        , errors = M.empty
        }
  where
    testsDir = "examples"
    errorTestsDir = "examples/error"

    rootDirs = if (runFailing tc)
               then [(testsDir, Pass), (errorTestsDir, Fail)]
               else [(testsDir, Pass)]

--------------------------------------------------------------------------------
-- The main event

data TestResult
    = EP -- ^ Expected pass
    | UP -- ^ Unexpected pass
    | EF String -- ^ Expected failure
    | UF String -- ^ Unexpected failure
  deriving (Eq, Read, Ord)

instance Show TestResult where
    show EP = "Expected pass"
    show UP = "Unexpected pass"
    show (EF s) = "Expected failure\n" ++ s
    show (UF s) = "Unexpected failure\n" ++ s

runTests :: TestConfig -> TestRun -> IO TestRun
runTests tc tr = foldlM (\acc t -> do
                             -- putStrLn (name t)
                             putStr "."
                             go t acc)
                 tr (sort $ tests tr)
  where
    go test acc = do
        res <- runTest tc test
        return $ case res of
            EP -> acc { expectedPasses   = expectedPasses acc ++ [test]   }
            UP -> acc { unexpectedPasses = unexpectedPasses acc ++ [test] }
            EF err -> acc { expectedFailures = expectedFailures acc ++ [test]
                          , errors = M.insert (name test) err (errors acc)
                          }
            UF err -> acc { unexpectedFailures = unexpectedFailures acc ++ [test]
                          , errors = M.insert (name test) err (errors acc)
                          }


runTest :: TestConfig -> Test -> IO TestResult
runTest tc (Test name dir expect) = do
    (_, Just hout, Just herr, phandle) <-
        createProcess (proc cmd compileOptions) { std_out = CreatePipe
                                                , std_err = CreatePipe }
    exitCode <- waitForProcess phandle
    case exitCode of
        ExitSuccess -> do
            -- Write the output to a file
            out <- hGetContents hout
            writeFile outpath out
            -- Diff the output and the answer
            actual <- diff anspath outpath
            case (actual, expect) of
                -- Nothing == No difference between the expected and actual answers
                (Nothing, Pass) -> return EP
                (Nothing, Fail) -> return UP
                (Just d , Fail) -> return (EF d)
                (Just d , Pass) -> return (UF d)

        ExitFailure _ -> do
            case expect of
                Fail -> EF <$> hGetContents herr
                Pass -> UF <$> hGetContents herr
  where
    tmppath  = tempdir tc </> name
    outpath = replaceExtension (replaceBaseName tmppath (takeBaseName tmppath ++ ".packed")) ".out"
    anspath = replaceExtension tmppath ".ans"

    cmd = "gibbon"
    compileOptions = [ "--run"
                     , "--packed"
                     , "--cfile=" ++ replaceExtension tmppath ".c"
                     , "--exefile=" ++ replaceExtension tmppath ".exe"
                     , dir </> name
                     ]

diff :: FilePath -> FilePath -> IO (Maybe String)
diff a b = do
    (_, Just hout, _, phandle) <-
        createProcess (proc "diff" [a, b]) { std_out = CreatePipe
                                           , std_err = CreatePipe }
    exitCode <- waitForProcess phandle
    case exitCode of
        ExitSuccess -> return Nothing
        ExitFailure _ -> do
            d <- hGetContents hout
            -- If we're running a benchmark, the Gibbon output may not match the answer generated by Racket.
            -- We ignore such a diff for now. Later, we could add a "bench" mode, which ensures that
            -- the result is within some expected range.
            if isBenchOutput d
            then return Nothing
            else return (Just d)

isBenchOutput :: String -> Bool
isBenchOutput s = isInfixOf "BATCHTIME" s || isInfixOf "SELFTIMED" s

summary :: TestConfig -> TestRun -> IO String
summary tc tr = do
    endTime <- getTime clk
    let timeTaken = quot (toNanoSecs (diffTimeSpec endTime (startTime tr))) (10^9)
    return $ render (go timeTaken)
  where
    go :: (Num a, Show a) => a -> Doc
    go timeTaken =
        text "\n\nGibbon testsuite summary:" $$
        text "--------------------------------------------------------------------------------" $$
        text "Time taken:" <+> text (show timeTaken) PP.<> text "s" $$
        text "There were:" $$
        (int $ length $ expectedPasses tr) <+> text "expected passes"  $$
        (int $ length $ unexpectedPasses tr) <+> text "unexpected passes" $$
        (int $ length $ expectedFailures tr) <+> text "expected failures" $$
        (int $ length $ unexpectedFailures tr) <+> text "unexpected failures" $$
        (case unexpectedPasses tr of
             [] -> empty
             ls -> text "\nUnexpected passes:" $$
                   text "--------------------------------------------------------------------------------" $$
                   vcat (map (text . name) ls)) $$
        (case expectedFailures tr of
             [] -> empty
             ls -> if (verbosity tc) >= 2
                   then  text "\nExpected failures:" $$
                         text "--------------------------------------------------------------------------------" $$
                         vcat (map
                               (\t -> text (name t) <+>
                                      (if (verbosity tc) >= 2
                                       then text "=>" $$ text (errors tr M.! name t)
                                       else empty))
                               ls)
                   else empty
        ) $$
        (case unexpectedFailures tr of
             [] -> empty
             ls -> text "\nUnexpected failures:" $$
                   text "--------------------------------------------------------------------------------" $$
                   vcat (map
                         (\t -> text (name t) <+>
                                (if (verbosity tc) >= 2
                                 then text "=>" $$ text (errors tr M.! name t)
                                 else empty))
                         ls))

--------------------------------------------------------------------------------

main :: IO ()
main = do
    tc <- execParser opts
    test_run <- getTestRun tc
    test_run' <- runTests tc test_run
    report <- summary tc test_run'
    writeFile (summaryFile tc) report
    putStrLn $ "Wrote " ++ (summaryFile tc) ++ "."
    putStrLn report
    case (unexpectedFailures test_run' , unexpectedPasses test_run') of
        ([],[]) -> return ()
        _ -> exitFailure
  where
     opts = info (configParser <**> helper)
         (fullDesc
              <> progDesc "Print a greeting for TARGET"
              <> header "hello - a test for optparse-applicative" )
