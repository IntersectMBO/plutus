{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Main where

import           Paths_plutus_benchmark                   (getDataDir, getDataFileName)

import qualified PlutusCore                               as PLC

import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

import           NaturalSort

import           Criterion.Main
import           Criterion.Main.Options                   (Mode, parseWith)
import           Criterion.Types                          (Config (..))
import           Options.Applicative

import           Control.DeepSeq                          (force)
import           Control.Monad.Trans.Except               (runExceptT)
import qualified Data.ByteString                          as BS
import qualified Data.ByteString.Lazy                     as BSL
import           Data.List                                (isPrefixOf)
import           Flat
import           System.Directory                         (listDirectory)
import           System.FilePath

{- | Benchmarks based on validations obtained using
plutus-use-cases:plutus-use-cases-scripts, which runs various contracts on the
blockchain simulator and dumps the applied validators as flat-encoded
scripts. Generating these scripts is a very lengthy process involving building a
lot of code, so the scripts were generated once and copied to the 'data'
directory here.  Type 'cabal run plutus-use-cases:plutus-use-cases-scripts
plutus-benchmark/validation/data scripts' in the root directory of the Plutus
repository to regenerate them, but *be careful*. It's possible that the name of
the files may change and you could be left with old files that still get
benchmarked, so it might be a good idea to remove the old ones first (and
remember that these are all checked in to git).  Also, the compiler output may
have changed since he scripts were last generated and so the builtins used and
so on could be different, which may confuse benchmark comparisons.  We might
want to have two sets of benchmarks: one for a set of fixed scripts that let us
benchmark the evaluator independently of other factors, and another which is
generated anew every time to allow us to measure changes in the entire
compilation/execution pipeline.

NB. Running these benchmarks with `stack bench` will use copies of the scripts
in `.stack_work` (and accessed via Paths_plutus_benchmark), and if a file in
`data` is removed and the benchmarks are re-run, the benchmarking code may still
be able to access the old copy in stack's files.  --}

{- | The name of the directory where the scripts are kept.  This must match the
   location of the files relative to the directory containing the cabal file.
   IF THE DIRECTORY IS MOVED, THIS MUST BE UPDATED. -}
{- Note also that this directory (and any subdirectories) must be included in the
   "data-files" section of the cabal file to ensure that Paths_plutus_benchmark
   still works. -}
getScriptDirectory :: IO FilePath
getScriptDirectory = do
  root <- getDataDir
  return $ root </> "validation" </> "data"

-- | A small subset of the contracts for quick benchmarking
quickPrefixes :: [String]
quickPrefixes =
    [ "crowdfunding-success"
    , "prism"
    , "token-account"
    , "uniswap"
    ]

-- Given two lists of strings l and ps, return the elements of l which have any
-- element of ps as a prefix
withAnyPrefixFrom :: [String] -> [String] -> [String]
l `withAnyPrefixFrom` ps =
    concatMap (\p -> filter (isPrefixOf p) l) ps

type Term          = UPLC.Term    PLC.Name      PLC.DefaultUni PLC.DefaultFun ()
type Program       = UPLC.Program PLC.Name      PLC.DefaultUni PLC.DefaultFun ()
type DbProgram     = UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()

fromDeBruijn :: DbProgram -> IO Program
fromDeBruijn prog = do
    let namedProgram = UPLC.programMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "v" ix) prog
    case PLC.runQuote $ runExceptT @UPLC.FreeVariableError $ UPLC.unDeBruijnProgram namedProgram of
      Left e  -> errorWithoutStackTrace $ show e
      Right p -> return p

loadFlat :: FilePath -> IO Term
loadFlat file = do
  contents <- BSL.fromStrict <$> BS.readFile file
  case unflat contents of
    Left e  -> errorWithoutStackTrace $ "Flat deserialisation failure for " ++ file ++ ": " ++ show e
    Right r -> do
        p <- fromDeBruijn r
        return $! force $ UPLC.toTerm p
        -- `force` to try to ensure that deserialiation is not included in benchmarking time.

mkCekBM :: Term -> Benchmarkable
mkCekBM program = nf (UPLC.unsafeEvaluateCek UPLC.noEmitter PLC.defaultCekParameters) program

mkScriptBM :: FilePath -> FilePath -> Benchmark
mkScriptBM dir file =
    env (loadFlat $ dir </> file) $ \script -> bench (dropExtension file) $ mkCekBM script

-- Make benchmarks for the given files in the directory
mkBMs :: FilePath -> [FilePath] -> [Benchmark]
mkBMs dir files = map (mkScriptBM dir) files


----------------------- Main -----------------------

{- | The Criterion configuration returned by `getConfig` will cause an HTML report
   to be generated.  If run via stack/cabal this will be written to the
   `plutus-benchmark` directory by default.  The -o option can be used to change
   this, but an absolute path will probably be required (eg,
   "-o=$PWD/report.html") . -}
getConfig :: Double -> IO Config
getConfig limit = do
  templateDir <- getDataFileName "templates"
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "report.html",
                timeLimit = limit
              }

-- Extend the options to include `--quick`: see eg https://github.com/haskell/criterion/pull/206
data BenchOptions = BenchOptions
  { quick        :: Bool
  , otherOptions :: Mode  -- The standard options
  }

parseBenchOptions :: Config -> Parser BenchOptions
parseBenchOptions cfg = BenchOptions
  <$> switch
      (  short 'q'
      <> long "quick"
      <> help "Run only a small subset of the benchmarks")
  <*> parseWith cfg

parserInfo :: Config -> ParserInfo BenchOptions
parserInfo cfg =
    info (helper <*> parseBenchOptions cfg) $ header "Plutus Core validation benchmark suite"

{- Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation --benchmark-options crowdfunding`.
-}
main :: IO ()
main = do
  cfg <- getConfig 20.0  -- Run each benchmark for at least 20 seconds.  Change this with -L or --timeout (longer is better).
  options <- execParser $ parserInfo cfg
  scriptDirectory <- getScriptDirectory
  files0 <- listDirectory scriptDirectory  -- Just the filenames, not the full paths
  let files1 = naturalSort $ filter (isExtensionOf ".flat") files0  -- Just in case there's anything else in the directory.
               -- naturalSort puts the filenames in a better order than Data.List.Sort
      files = if quick options then files1 `withAnyPrefixFrom` quickPrefixes else files1
      benchmarks = mkBMs scriptDirectory files
  runMode (otherOptions options) benchmarks


