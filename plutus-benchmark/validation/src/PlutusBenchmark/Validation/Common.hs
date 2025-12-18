-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Validation.Common
  ( benchWith
  , unsafeUnflat
  , mkEvalCtx
  , benchTermCek
  , peelDataArguments
  , Term
  , getScriptDirectory
  ) where

import PlutusBenchmark.Common (benchTermCek, getConfig, getDataDir, mkEvalCtx)
import PlutusBenchmark.NaturalSort

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Data qualified as PLC
import UntypedPlutusCore qualified as UPLC

import Criterion.Main
import Criterion.Main.Options (Mode, parseWith)
import Criterion.Types (Config (..))
import Options.Applicative

import Data.ByteString qualified as BS
import Data.List (isPrefixOf)
import PlutusCore.Flat
import System.Directory (listDirectory)
import System.FilePath

{- Note [Original generation of the .flat files]

The corresponding .hs sources of the test inputs are not part anymore of the
repo since 2021 (commit 0cb5c00add3809d9f247e9ec3f069d9ac3becd95). The .flat
files can therefore not be regenerated. The following is the original
documentation on how they used to be generated:

Benchmarks based on validations obtained using
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

-}

{-| The name of the directory where the scripts are kept.  This must match the
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
    Left e -> errorWithoutStackTrace $ "Flat deserialisation failure for " ++ file ++ ": " ++ show e
    Right (UPLC.UnrestrictedProgram prog) -> prog

----------------------- Main -----------------------

-- Extend the options to include `--quick`: see eg https://github.com/haskell/criterion/pull/206
data BenchOptions = BenchOptions
  { quick :: Bool
  , otherOptions :: Mode -- The standard options
  }

parseBenchOptions :: Config -> Parser BenchOptions
parseBenchOptions cfg =
  BenchOptions
    <$> switch
      ( short 'q'
          <> long "quick"
          <> help "Run only a small subset of the benchmarks"
      )
    <*> parseWith cfg

parserInfo :: Config -> ParserInfo BenchOptions
parserInfo cfg =
  info (helper <*> parseBenchOptions cfg) $ header "Plutus Core validation benchmark suite"

benchWith :: (FilePath -> BS.ByteString -> Benchmarkable) -> IO ()
benchWith act = do
  cfg <- getConfig 20.0 -- Run each benchmark for at least 20 seconds.  Change this with -L or --timeout (longer is better).
  options <- execParser $ parserInfo cfg
  scriptDirectory <- getScriptDirectory
  files0 <- listDirectory scriptDirectory -- Just the filenames, not the full paths
  let
    -- naturalSort puts the filenames in a better order than Data.List.Sort
    files1 = naturalSort $ filter (isExtensionOf ".flat") files0 -- Just in case there's anything else in the directory.
    files =
      if quick options
        then files1 `withAnyPrefixFrom` quickPrefixes
        else files1
  runMode (otherOptions options) $ mkBMs scriptDirectory files
  where
    -- Make benchmarks for the given files in the directory
    mkBMs :: FilePath -> [FilePath] -> [Benchmark]
    mkBMs dir files = map (mkScriptBM dir) files

    mkScriptBM :: FilePath -> FilePath -> Benchmark
    mkScriptBM dir file =
      env (BS.readFile $ dir </> file) $ \(~scriptBS) ->
        bench (dropExtension file) $ act file scriptBS

type Term = UPLC.Term UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()

{-| If the term is an application of something to some arguments, peel off
those arguments which are 'Data' constants. -}
peelDataArguments :: Term -> (Term, [PLC.Data])
peelDataArguments = go []
  where
    go acc t@(UPLC.Apply () t' arg) = case PLC.readKnown arg of
      Left _ -> (t, acc)
      Right d -> go (d : acc) t'
    go acc t = (t, acc)
