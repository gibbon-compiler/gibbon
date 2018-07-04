{-# LANGUAGE CPP #-}
-- | Aims to minimize the work done by bench_gibbon.sh.
module BenchRunner
    (main) where

import           Data.List
import           Data.Yaml as Y
import           System.Environment
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
    let tc_mb :: Maybe TestConfig
        tc_mb = Y.decode (BS.pack configstr)

        tests_mb :: Maybe Tests
        tests_mb = Y.decode (BS.pack configstr)

    case (tc_mb, tests_mb) of
        (Nothing,_) -> error $ "Couldn't parse the configuration in " ++ configFile
        (_,Nothing) -> error $ "Couldn't parse the tests in " ++ configFile
        (Just file_tc, Just tests) -> do
            -- Combine the options read from the config file with the command line
            -- arguments (which have higher precedence).
            let opts = info (configParser file_tc <**> helper)
                            (fullDesc <>
                             header "TestRunner - a simple harnness for the Gibbon testsuite.")
            tc <- execParser opts >>= mergeTestConfigWithEnv
            if (recordBenchmarks tc)
            then bench_main tc tests
            else test_main tc tests

getHostname :: IO String
getHostname = init <$> readCreateProcess (shell "hostname") ""

bench_main :: TestConfig -> Tests -> IO ()
bench_main tc (Tests tests) = do
    putStrLn "Executing BenchRunner...\n"
    let benchmarks = filter isBenchmark tests
        modesToBench = [Gibbon1, Gibbon2, Pointer]
    results <- mapM (go modesToBench) benchmarks
    mc <- getHostname
    let csvs = map (\arg -> intercalate "," (mc:arg)) (concat results)
    writeFile (benchSummaryFile tc) (unlines csvs)
    putStrLn $ "Wrote results to" ++ (benchSummaryFile tc) ++ "."
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
