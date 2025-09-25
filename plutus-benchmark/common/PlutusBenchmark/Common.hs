{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}

{- | Miscellaneous shared code for benchmarking-related things. -}
module PlutusBenchmark.Common
    ( module Export
    , Program
    , Term
    , getConfig
    , toAnonDeBruijnTerm
    , toNamedDeBruijnTerm
    , compiledCodeToTerm
    , benchProgramCek
    , cekResultMatchesHaskellValue
    , mkEvalCtx
    , mkMostRecentEvalCtx
    , evaluateCekLikeInProd
    , benchTermCek
    , TestSize (..)
    , printHeader
    , printSizeStatistics
    , goldenVsTextualOutput
    , checkGoldenFileExists
    )
-- ### CAUTION! ###.  Changing the number and/or order of the exports here may
-- change the execution times of the validation benchmarks.  See
-- https://github.com/IntersectMBO/plutus/issues/5906.
where

import Paths_plutus_benchmark as Export
import PlutusBenchmark.ProtocolParameters as PP

import PlutusLedgerApi.Common qualified as LedgerApi

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Pretty (Pretty)

import PlutusTx.Test.Util.Compiled (Program, Term, cekResultMatchesHaskellValue, compiledCodeToTerm,
                                    toAnonDeBruijnProg, toAnonDeBruijnTerm, toNamedDeBruijnTerm)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Control.DeepSeq (NFData, force)
import Criterion.Main
import Criterion.Types (Config (..))
import Data.ByteString qualified as BS
import Data.SatInt (fromSatInt)
import GHC.IO.Encoding (setLocaleEncoding)
import PlutusCore.Flat qualified as Flat
import System.Directory
import System.FilePath
import System.IO
import System.IO.Temp
import Test.Tasty
import Test.Tasty.Golden
import Text.Printf (hPrintf, printf)

{- | The Criterion configuration returned by `getConfig` will cause an HTML report
   to be generated.  If run via stack/cabal this will be written to the
   `plutus-benchmark` directory by default.  The -o option can be used to change
   this, but an absolute path will probably be required (eg, "-o=$PWD/report.html") . -}
getConfig :: Double -> IO Config
getConfig limit = do
  templateDir <- getDataFileName ("common" </> "templates")
  -- Include number of iterations in HTML report
  let templateFile = templateDir </> "with-iterations" <.> "tpl"
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "report.html",
                timeLimit = limit
              }

-- | Evaluate a script and return the CPU and memory costs (according to the cost model)
getCostsCek :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun () -> (Integer, Integer)
getCostsCek (UPLC.Program _ _ prog) =
    case Cek.runCekDeBruijn PLC.defaultCekParametersForTesting Cek.tallying Cek.noEmitter prog of
      Cek.CekReport _res (Cek.TallyingSt _ budget) _logs ->
          let ExBudget (ExCPU cpu)(ExMemory mem) = budget
          in (fromSatInt cpu, fromSatInt mem)

-- | Create the evaluation context for the benchmarks. This doesn't exactly
-- match how it's done on-chain, but that's okay because the evaluation context
-- is cached by the ledger, so we're deliberately not including it in the
-- benchmarks.  Different benchmarks may depend on different language versions
-- and semantic variants, so we have to specify those here.
mkEvalCtx
  :: LedgerApi.PlutusLedgerLanguage
  -> BuiltinSemanticsVariant DefaultFun
  -> LedgerApi.EvaluationContext DefaultFun
mkEvalCtx ll semvar =
    case PLC.defaultCostModelParamsForVariant semvar of
        Just p ->
            let errOrCtx =
                    LedgerApi.mkDynEvaluationContext
                        ll
                        (\_ -> PLC.CaserBuiltin PLC.caseBuiltin)
                        [semvar]
                        (const semvar)
                        p
            in case errOrCtx of
                Right ec -> ec
                Left err -> error $ show err
        Nothing -> error $ "Couldn't get cost model params for " ++ (show semvar)

-- Many of our benchmarks should use an evaluation context for the most recent
-- Plutus language version and the ost recent semantic variant.
mkMostRecentEvalCtx :: LedgerApi.EvaluationContext DefaultFun
mkMostRecentEvalCtx = mkEvalCtx maxBound maxBound

-- | Evaluate a term as it would be evaluated using the on-chain evaluator.
evaluateCekLikeInProd
    :: (Pretty fun, PLC.Typeable fun, Eq (BuiltinSemanticsVariant fun))
    => LedgerApi.EvaluationContext fun
    -> UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni fun ()
    -> Either
            (UPLC.CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni fun)
            (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni fun ())
evaluateCekLikeInProd evalCtx term =
    let -- The validation benchmarks were all created from PlutusV1 scripts
        pv = LedgerApi.ledgerLanguageIntroducedIn LedgerApi.PlutusV1
    in Cek.cekResultToEither . Cek._cekReportResult $
        LedgerApi.evaluateTerm UPLC.restrictingEnormous pv LedgerApi.Quiet evalCtx term

-- | Evaluate a term and either throw if evaluation fails or discard the result and return '()'.
-- Useful for benchmarking.
evaluateCekForBench
    :: (Pretty fun, PLC.Typeable fun, Eq (BuiltinSemanticsVariant fun))
    => LedgerApi.EvaluationContext fun
    -> UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni fun ()
    -> ()
evaluateCekForBench evalCtx = either (error . show) (\_ -> ()) . evaluateCekLikeInProd evalCtx

benchTermCek
    :: (NFData fun, Pretty fun, PLC.Typeable fun, Eq (BuiltinSemanticsVariant fun))
    => LedgerApi.EvaluationContext fun
    -> UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni fun ()
    -> Benchmarkable
benchTermCek evalCtx term =
    let !term' = force term
    in whnf (evaluateCekForBench evalCtx) term'

benchProgramCek
    :: (NFData fun, Pretty fun, PLC.Typeable fun, Eq (BuiltinSemanticsVariant fun))
    => LedgerApi.EvaluationContext fun
    -> UPLC.Program UPLC.NamedDeBruijn DefaultUni fun ()
    -> Benchmarkable
benchProgramCek evalCtx (UPLC.Program _ _ term) =
  benchTermCek evalCtx term

---------------- Printing tables of information about costs ----------------

data TestSize =
    NoSize
  | TestSize Integer

stringOfTestSize :: TestSize -> String
stringOfTestSize =
    \case
     NoSize     -> "-"
     TestSize n -> show n

-- Printing utilities
percentage :: (Integral a, Integral b) => a -> b -> Double
percentage a b =
    let a' = fromIntegral a :: Double
        b' = fromIntegral b :: Double
    in (a'* 100) / b'

percentTxt :: (Integral a, Integral b) => a -> b -> String
percentTxt a b = printf "(%.1f%%)" (percentage a b)

-- | Print a header to be followed by a list of size statistics.
printHeader :: Handle -> IO ()
printHeader h = do
  hPrintf h "    n     Script size             CPU usage               Memory usage\n"
  hPrintf h "  ----------------------------------------------------------------------\n"

-- | Evaluate a script and print out the serialised size and the CPU and memory
-- usage, both as absolute values and percentages of the maxima specified in the
-- protocol parameters.
printSizeStatistics
    :: Handle
    -> TestSize
    -> UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> IO ()
printSizeStatistics h n script = do
    let serialised = Flat.flat (UPLC.UnrestrictedProgram $ toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = getCostsCek script
    hPrintf h "  %3s %7d %8s %15d %8s %15d %8s \n"
           (stringOfTestSize n)
           size (percentTxt size PP.max_tx_size)
           cpu  (percentTxt cpu  PP.max_tx_ex_steps)
           mem  (percentTxt mem  PP.max_tx_ex_mem)


---------------- Golden tests for tabular output ----------------

{- | Run a program which produces textual output and compare the results with a
   golden file.  This is intended for tests which produce a lot of formatted
   text.  The output is written to a file in the system temporary directory and
   deleted if the test passes.  If the test fails then the output is retained
   for further inspection. -}
goldenVsTextualOutput
    :: TestName          -- The name of the test.
    -> FilePath          -- The path to the golden file.
    -> FilePath          -- The name of the results file (may be extended to make it unique).
    -> (Handle -> IO a)  -- A function which runs tests and writes output to the given handle.
    -> IO ()
goldenVsTextualOutput testName goldenFile filename runTest =  do
  setLocaleEncoding utf8
  tmpdir <- getCanonicalTemporaryDirectory
  (resultsFile, handle) <- openBinaryTempFile tmpdir filename
  -- ^ Binary mode to avoid problems with line endings.  See documentation for Test.Tasty.Golden
  Test.Tasty.defaultMain $
    localOption OnPass $  -- Delete the output if the test succeeds.
      goldenVsFileDiff
        testName
        (\expected actual -> ["diff", "-u", expected, actual])  -- How to to display differences.
        goldenFile
        resultsFile
        (runTest handle >> hClose handle)

{- Note [Paths to golden files]
   Some of our tests contain hard-coded relative paths to golden files.  This is
   a little unsatisfactory because if for example we change the name of the
   directory containing the file then it won't be found during the test but the
   test will succeed and a new golden file will be created in the new directory,
   leading to the possibility that a change in the output won't be detected.  A
   similar thing will happen if someone forgets to check a golden file into the
   repository and the test is run in a new checkout.  Golden tests from
   tasty-golden do print out a message when the golden file doesn't exist, but
   it's in a very unobtrusive colour and easy to miss.  Another issue is that
   tests can be run from cabal using either `cabal test` or `cabal run`. If
   `cabal test` is used, cabal sets the working directory of the test program
   (which is used as the root for relative paths) to be the directory containing
   the relevant .cabal file, which is what our tests expect.  However, if `cabal
   run` is used then cabal sets the working directory to the current shell
   directory, and this can again lead to the wrong path being used with the
   possibility of a change being missed; also new golden files may be produced
   in unexpected places.  This function is used to mitigate these risks by
   checking that a golden file already exists in the expected place and issuing
   an error if it isn't.  This does mean that an error may occur the first time
   a golden test is run.  To avoid this, create an initial version of the file
   manually and if necessary use the `--accept` option to overwrite its
   contents.
   -}
checkGoldenFileExists :: FilePath -> IO ()
checkGoldenFileExists path = do
  fullPath <- makeAbsolute path
  fileExists <- doesFileExist path
  if not fileExists
  then errorWithExplanation $ "golden file " ++ fullPath ++ " does not exist."
  else do
    perms <- getPermissions path
    if not (writable perms)
    then errorWithExplanation $ "golden file " ++ fullPath ++ " is not writable."
    else pure ()
    where errorWithExplanation s =
              let msg = "\n* ERROR: " ++ s ++ "\n"
                        ++ "* To ensure that the correct path is used, either use `cabal test` "
                        ++ "or run the test in the root directory of the relevant package.\n"
                        ++ "* If this is the first time this test has been run, create an "
                        ++ "initial golden file manually."
              in error msg
