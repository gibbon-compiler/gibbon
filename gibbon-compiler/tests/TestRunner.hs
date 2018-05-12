module TestRunner
    (main) where

import Data.List (intercalate)
import System.Clock
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process

--------------------------------------------------------------------------------
-- A single test

data Test = Test
    { name   :: String
    , dir    :: FilePath
    , expect :: Expect
    }
  deriving (Show, Eq, Read, Ord)

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
    , summaryFile = "gibbon-test-summary.json"
    , tempdir     = "examples/build_tmp"
    }

-- TODO: add a parser to allow specifying overrides via command line

-- Not used atm.
-- | Gibbon mode to run programs in
data Mode = Packed | Pointer | Interp1
  deriving (Eq, Read, Ord)

data TestRun = TestRun
    { tests :: [Test]
    , startTime  :: TimeSpec
    , expectedPasses :: [Test]
    , unexpectedPasses :: [Test]
    , expectedFailures :: [Test]
    , unexpectedFailures :: [Test]
    }
  deriving (Show, Eq, Read, Ord)

getTestRun :: TestConfig -> IO TestRun
getTestRun tc = do
    tests <- findTestFiles rootDirs
    time <- getTime Monotonic
    return $ TestRun
        { tests = tests
        , startTime = time
        , expectedPasses = []
        , unexpectedPasses = []
        , expectedFailures = []
        , unexpectedFailures = []
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

diff :: FilePath -> FilePath -> IO (Maybe String)
diff a b = do
    (_, Just hout, _, phandle) <-
        createProcess (proc "diff" [a, b]) { std_out = CreatePipe
                                           , std_err = CreatePipe }
    exitCode <- waitForProcess phandle
    case exitCode of
        ExitSuccess -> return Nothing
        ExitFailure _ -> do
            Just <$> hGetContents hout

runTest :: TestConfig -> Test -> IO TestResult
runTest tc (Test name dir expect) = do
    (_, Just hout, Just herr, phandle) <-
        createProcess (proc cmd compileOptions) { std_out = CreatePipe
                                                , std_err = CreatePipe }
    exitCode <- waitForProcess phandle
    case exitCode of
        ExitSuccess -> do
            -- Write the out file
            out <- hGetContents hout
            writeFile outpath out

            -- Diff the contents.
            actual <- diff anspath outpath
            case (actual, expect) of
                -- Nothing == No difference between the expected and actual answers
                (Nothing, Pass) -> return EP
                (Nothing, Fail) -> return UP
                (Just d , Fail) -> return (EF d)
                (Just d , Pass) -> return (UF d)

        ExitFailure _ ->
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

main :: IO ()
main = do
    test_run <- getTestRun defaultTestConfig
    let test = head $ tests test_run
    x <- runTest defaultTestConfig test
    putStrLn (show (test, x))
