-- editorconfig-checker-disable-file
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Common (
      benchWith
    , mkBMs
    , prepareFilePaths
    , getScriptDirectory
    , QuickFlag(..)
    , unsafeUnflat
    , mkEvalCtx
    , benchTermCek
    , peelDataArguments
    , Term
    ) where

import PlutusBenchmark.Common (BenchmarkClass (..), benchTermCek, getConfig, getDataDir, mkEvalCtx)
import PlutusBenchmark.NaturalSort

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Data qualified as PLC
import UntypedPlutusCore qualified as UPLC

import Criterion.Main (runMode)
import Criterion.Main.Options (Mode, parseWith)
import Criterion.Types (Benchmarkable, Config (..))
import Options.Applicative

import Data.ByteString qualified as BS
import Data.List (isPrefixOf)
import Flat
import System.Directory (listDirectory)
import System.FilePath
import Test.Tasty.Options (IsOption (..), safeRead)

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

unsafeUnflat :: String -> BS.ByteString -> UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
unsafeUnflat file contents =
    case unflat contents of
        Left e     -> errorWithoutStackTrace $ "Flat deserialisation failure for " ++ file ++ ": " ++ show e
        Right (UPLC.UnrestrictedProgram prog) -> prog

----------------------- Main -----------------------
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

-- Ingredient for quick option
newtype QuickFlag = MkQuickFlag Bool

instance IsOption QuickFlag where
  defaultValue = MkQuickFlag False
  parseValue = fmap MkQuickFlag . safeRead
  optionName = pure "quick"
  optionHelp = pure "Run only a small subset of the benchmarks"

-- Make benchmarks for the given files in the directory
mkBMs :: forall a. BenchmarkClass a => (FilePath -> BS.ByteString -> a) -> FilePath -> [FilePath] -> [Benchmark a]
mkBMs act dir files = map mkScriptBM files
  where
    mkScriptBM :: FilePath -> Benchmark a
    mkScriptBM file =
        env (BS.readFile $ dir </> file) $ \(~scriptBS) ->
            bench (dropExtension file) $ act file scriptBS

prepareFilePaths :: Bool -> [FilePath] -> [FilePath]
prepareFilePaths isQuick files = if isQuick
  then files1 `withAnyPrefixFrom` quickPrefixes
  else files1
  where
    -- naturalSort puts the filenames in a better order than Data.List.Sort
    files1 = naturalSort $ filter (isExtensionOf ".flat") files -- Just in case there's anything else in the directory.

benchWith :: (FilePath -> BS.ByteString -> Benchmarkable) -> IO ()
benchWith act = do
    cfg <- getConfig 20.0  -- Run each benchmark for at least 20 seconds.  Change this with -L or --timeout (longer is better).
    options <- execParser $ parserInfo cfg
    scriptDirectory <- getScriptDirectory
    files0 <- listDirectory scriptDirectory  -- Just the filenames, not the full paths
    let files = prepareFilePaths (quick options) files0
    runMode (otherOptions options) $ mkBMs act scriptDirectory files

type Term = UPLC.Term UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()

-- | If the term is an application of something to some arguments, peel off
-- those arguments which are 'Data' constants.
peelDataArguments :: Term -> (Term, [PLC.Data])
peelDataArguments = go []
    where
        go acc t@(UPLC.Apply () t' arg) = case PLC.readKnown arg of
            Left _  -> (t, acc)
            Right d -> go (d:acc) t'
        go acc t = (t, acc)
