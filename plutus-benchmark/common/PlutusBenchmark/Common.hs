{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

{- | Miscellaneous shared code for benchmarking-related things. -}
module PlutusBenchmark.Common
    ( module Export
    , Term
    , getConfig
    , toAnonDeBruijnTerm
    , toNamedDeBruijnTerm
    , compiledCodeToTerm
    , haskellValueToTerm
    , benchTermCek
    , benchProgramCek
    , unsafeRunTermCek
    , runTermCek
    , cekResultMatchesHaskellValue
    , TestSize (..)
    , printHeader
    , printSizeStatistics
    , goldenVsTextualOutput
    , checkGoldenFileExists
    )
where

import Paths_plutus_benchmark as Export
import PlutusBenchmark.ProtocolParameters as PP

import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import Criterion.Main
import Criterion.Types (Config (..))
import Data.ByteString qualified as BS
import Data.SatInt (fromSatInt)
import Data.Text (Text)
import Flat qualified
import GHC.IO.Encoding (setLocaleEncoding)
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

type Term = UPLC.Term PLC.NamedDeBruijn DefaultUni DefaultFun ()
type Program = UPLC.Program PLC.NamedDeBruijn DefaultUni DefaultFun ()

{- | Given a DeBruijn-named term, give every variable the name "v".  If we later
   call unDeBruijn, that will rename the variables to things like "v123", where
   123 is the relevant de Bruijn index.-}
toNamedDeBruijnTerm
    :: UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
toNamedDeBruijnTerm = UPLC.termMapNames UPLC.fakeNameDeBruijn

{- | Remove the textual names from a NamedDeBruijn term -}
toAnonDeBruijnTerm
    :: Term
    -> UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
toAnonDeBruijnTerm = UPLC.termMapNames UPLC.unNameDeBruijn

toAnonDeBruijnProg
    :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> UPLC.Program UPLC.DeBruijn      DefaultUni DefaultFun ()
toAnonDeBruijnProg (UPLC.Program () ver body) =
    UPLC.Program () ver $ toAnonDeBruijnTerm body


{- | Just extract the body of a program wrapped in a 'CompiledCodeIn'.  We use this a lot. -}
compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> Term
compiledCodeToTerm (Tx.getPlcNoAnn -> UPLC.Program _ _ body) = body

{- | Lift a Haskell value to a PLC term.  The constraints get a bit out of control
   if we try to do this over an arbitrary universe.-}
haskellValueToTerm
    :: Tx.Lift DefaultUni a => a -> Term
haskellValueToTerm = compiledCodeToTerm . Tx.liftCodeDef


{- | Convert a de-Bruijn-named UPLC term to a Benchmark -}
benchTermCek :: Term -> Benchmarkable
benchTermCek term =
    nf (unsafeRunTermCek) $! term -- Or whnf?

{- | Convert a de-Bruijn-named UPLC term to a Benchmark -}
benchProgramCek :: Program -> Benchmarkable
benchProgramCek (UPLC.Program _ _ term) =
    nf (unsafeRunTermCek) $! term -- Or whnf?

{- | Just run a term to obtain an `EvaluationResult` (used for tests etc.) -}
unsafeRunTermCek :: Term -> EvaluationResult Term
unsafeRunTermCek =
    unsafeExtractEvaluationResult
        . (\(res, _, _) -> res)
        . runCekDeBruijn PLC.defaultCekParameters Cek.restrictingEnormous Cek.noEmitter

-- | Just run a term.
runTermCek ::
    Term ->
    ( Either (CekEvaluationException UPLC.NamedDeBruijn DefaultUni DefaultFun) Term
    , [Text]
    )
runTermCek =
    (\(res, _, logs) -> (res, logs))
        . runCekDeBruijn PLC.defaultCekParameters Cek.restrictingEnormous Cek.logEmitter

-- | Evaluate a script and return the CPU and memory costs (according to the cost model)
getCostsCek :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun () -> (Integer, Integer)
getCostsCek (UPLC.Program _ _ prog) =
    case Cek.runCekDeBruijn PLC.defaultCekParameters Cek.tallying Cek.noEmitter prog of
      (_res, Cek.TallyingSt _ budget, _logs) ->
          let ExBudget (ExCPU cpu)(ExMemory mem) = budget
          in (fromSatInt cpu, fromSatInt mem)

{- | Evaluate a PLC term and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties.  -}
cekResultMatchesHaskellValue
    :: Tx.Lift DefaultUni a
    => Term
    -> (EvaluationResult Term -> EvaluationResult Term -> b)
    -> a
    -> b
cekResultMatchesHaskellValue term matches value =
    (unsafeRunTermCek term) `matches` (unsafeRunTermCek $ haskellValueToTerm value)

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
    -> String            -- The name of the results file (may be extended to make it unique).
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

{- | Note [Paths to golden files]
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
