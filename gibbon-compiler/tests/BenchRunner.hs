{-# LANGUAGE CPP #-}
-- | Aims to minimize the work done by bench_gibbon.sh.
module BenchRunner
    (main) where

import           Data.List
import           Data.Yaml as Y
import           System.Environment ( lookupEnv )
import           System.FilePath
import           System.Process
import           Text.Printf
import           Options.Applicative as OA hiding (empty, str)
import qualified Data.ByteString.Char8 as BS

#if !MIN_VERSION_base(4,11,0)
import           Data.Monoid
#endif

import           TestRunner as TR

main :: IO ()
main = do
    -- Parse the config file
    compiler_dir <- getCompilerDir
    configstr <- readFile (compiler_dir </> configFile)
    let tc_eth :: Either ParseException TestConfig
        tc_eth = Y.decodeEither' (BS.pack configstr)

        tests_eth :: Either ParseException Tests
        tests_eth = Y.decodeEither' (BS.pack configstr)

    case (tc_eth, tests_eth) of
        (Left err,_) -> error ("Couldn't parse the configuration in " ++ configFile
                               ++ ". " ++ show err)
        (_,Left err) -> error ("Couldn't parse the tests in " ++ configFile
                               ++ ". " ++ show err)
        (Right file_tc, Right tests) -> do
            -- Combine the options read from the config file with the command line
            -- arguments (which have higher precedence).
            let opts = info (configParser file_tc <**> helper)
                            (fullDesc <>
                             header "TestRunner - a simple harnness for the Gibbon testsuite.")
            tc <- execParser opts >>= mergeTestConfigWithEnv
            -- Respect ENV overrides.
            tests' <- envOverrides tests

            if (recordBenchmarks tc)
            then bench_main tc tests'
            else test_main tc tests'

-- | Override numTrials and sizeParam with environment variables.
envOverrides :: Tests -> IO Tests
envOverrides tests = do
  trials_env <- lookupEnv "GIBBON_TRIALS"
  tests' <- case trials_env of
              Nothing  -> pure tests
              Just str -> do
                let n = read str :: Int
                    Tests ts = tests
                pure $ Tests $ map (\t -> t { numTrials = n }) ts

  sizeEnv <- lookupEnv "GIBBON_SIZE"
  tests'' <- case sizeEnv of
              Nothing  -> pure tests'
              Just str -> do
                let sz = read str :: Int
                    Tests ts = tests'
                pure $ Tests $ map (\t -> t { sizeParam = sz }) ts

  pure tests''

getHostname :: IO String
getHostname = init <$> readCreateProcess (shell "hostname") ""

bench_main :: TestConfig -> Tests -> IO ()
bench_main tc (Tests tests) = do
    putStrLn "Executing BenchRunner...\n"
    let benchmarks = filter (not . skip) $ filter isBenchmark tests
        modesToBench = [Gibbon1, Gibbon2, Pointer]
    results <- mapM (go modesToBench) benchmarks
    mc <- getHostname
    let csvs = map (\arg -> intercalate "," (mc:arg)) (concat results)
    appendFile (benchSummaryFile tc) (unlines csvs)
    putStrLn $ "Wrote results to " ++ (benchSummaryFile tc) ++ "."
  where
    go :: [Mode] -> Test -> IO [[String]]
    go modes t@Test{name,sizeParam,moreIters,numTrials} = do
        putStrLn $ "Benchmarking " ++ show name
        results <- mapM (\mode ->
                  do trials <- doNTrials tc mode t
                     let res = case trials of
                                   Left err -> err
                                   Right bench_results ->
                                       let (BenchResult median_res) =
                                               medianBenchResult numTrials bench_results
                                       in printf "%e" median_res
                         iters :: Int
                         iters = if mode `elem` moreIters then 10000000 else 1
                     return [takeBaseName name, show mode, show sizeParam, show numTrials, show iters, res])
             modes
        putStrLn (show results)
        return results
