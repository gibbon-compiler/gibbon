-- | Aims to minimize the work done by bench_gibbon.sh.
module BenchRunner
    (main) where

import           Data.List
import           Data.Yaml as Y
import           System.Environment
import           System.FilePath
import           System.Process
import           Text.Printf
import qualified Data.ByteString.Char8 as BS

import           TestRunner hiding (main)
import qualified TestRunner as TR

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--benchmarks"] -> bench_main Nothing
        ["--benchmarks", filename] -> bench_main (Just filename)
        _ -> TR.main

getHostname :: IO String
getHostname = init <$> readCreateProcess (shell "hostname") ""

bench_main :: Maybe FilePath -> IO ()
bench_main fp_mb = do
    putStrLn "Executing BenchRunner...\n"

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
        (Just file_tc, Just (Tests tests)) -> do
            let benchmarks = filter isBenchmark tests
                modesToBench = [Gibbon1, Gibbon2, Pointer]
            results <- mapM (go file_tc modesToBench) benchmarks
            mc <- getHostname
            let csvs = map (\arg -> intercalate "," (mc:arg)) (concat results)
            -- writeFile
            case fp_mb of
                Just fp -> do writeFile fp (unlines csvs)
                              putStrLn $ "Wrote results to" ++ fp ++ "."
                Nothing -> putStrLn (show csvs)
  where
    go :: TestConfig -> [Mode] -> Test -> IO [[String]]
    go tc modes t@Test{name,sizeParam,moreIters,numTrials} = do
        putStrLn $ "Benchmarking " ++ show name
        mapM (\mode ->
                  do trials <- doNTrials tc mode t
                     let res = case trials of
                                   Left err -> err
                                   Right bench_results ->
                                       let (BenchResult median_res) =
                                               medianBenchResult numTrials bench_results
                                       in printf "%e" median_res
                         iters = if mode `elem` moreIters then 10000000 else 1
                     return [takeBaseName name, show mode, show sizeParam, show numTrials, show iters, res])
             modes
