{-| Round-trip check: test cases written by the conformance generators are read
back by the harness that consumes them. The sample covers equality pairs,
group-valued results, expected failures and the Hedgehog generators. -}
module Main (main) where

import Evaluation.Builtins.BLS12_381 (generate_bls12_381_properties)
import Evaluation.Builtins.Bitwise.CIP0122 (generate_bitwise_cip0122_properties)
import Evaluation.Builtins.Conformance (CheckMode (..), OutputFormat (Both), propertyIdText)
import Evaluation.Builtins.Integer.RingProperties (generate_integer_ring_properties)
import PlutusExecutables.Conformance.Info
  ( InfoDetails (..)
  , InfoSummary (..)
  , readInfoSummary
  , writeInfo
  )

import PlutusConformance.CekEvaluator (mkCekEvaluator)
import PlutusConformance.Common (Format (..), discoverTests)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParamsForTesting)
import UntypedPlutusCore.Evaluation.Machine.Cek (runCekNoEmit)

import Control.Exception (finally)
import Control.Monad (forM, when)
import Data.List (isInfixOf, isSuffixOf)
import Data.Maybe (fromJust)
import System.Directory
  ( createDirectory
  , doesDirectoryExist
  , getTemporaryDirectory
  , listDirectory
  , removeFile
  , removePathForcibly
  )
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)
import Test.QuickCheck.Random (mkQCGen)
import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main = withGeneratedTests $ \dir -> do
  -- Guard against a vacuous pass: the generators match properties by name, so
  -- assert that the sample actually produced programs before discovering them.
  programs <- countFiles ".flat.expected" dir
  when (programs < 20) $
    ioError . userError $
      "expected at least 20 generated programs, found " <> show programs
  checkInfo dir
  let evaluator = mkCekEvaluator runCekNoEmit
      params = fromJust defaultCostModelParamsForTesting
      noneExpected _ = False
  textualTree <- discoverTests Textual evaluator params noneExpected noneExpected dir
  flatTree <- discoverTests Flat evaluator params noneExpected noneExpected dir
  defaultMain $
    testGroup
      "generated tests"
      [ testGroup "textual" [textualTree]
      , testGroup "flat" [flatTree]
      ]

-- | Count files with the given suffix anywhere below a directory.
countFiles :: String -> FilePath -> IO Int
countFiles suffix dir = do
  entries <- listDirectory dir
  fmap sum . forM entries $ \entry -> do
    let path = dir </> entry
    isDir <- doesDirectoryExist path
    if isDir
      then countFiles suffix path
      else pure $ if suffix `isSuffixOf` entry then 1 else 0

-- | Count every file below a directory.
countAllFiles :: FilePath -> IO Int
countAllFiles dir = do
  entries <- listDirectory dir
  fmap sum . forM entries $ \entry -> do
    let path = dir </> entry
    isDir <- doesDirectoryExist path
    if isDir then countAllFiles path else pure 1

{-| The info file must describe exactly what was written: every file on disk
apart from the info file itself, and a complete tree. -}
checkInfo :: FilePath -> IO ()
checkInfo dir = do
  summary <- readInfoSummary dir
  case summary of
    Nothing -> ioError (userError "the generators did not write an info file")
    Just s -> do
      files <- countAllFiles dir
      when (summaryFiles s /= files - 1) $
        ioError . userError $
          "the info file reports "
            <> show (summaryFiles s)
            <> " files but the directory contains "
            <> show (files - 1)
      when (not (summaryCompleteTree s)) $
        ioError (userError "the info file does not describe a complete tree")
      when (summaryProperties s < 5) $
        ioError . userError $
          "the info file reports only " <> show (summaryProperties s) <> " properties"

{-| Fill a fresh unique directory with generated cases and remove it
afterwards. Uses a temporary file to obtain a unique name. -}
withGeneratedTests :: (FilePath -> IO a) -> IO a
withGeneratedTests action = do
  tmp <- getTemporaryDirectory
  (probe, handle) <- openTempFile tmp "conformance-tests"
  hClose handle
  removeFile probe
  let dir = probe <> "-dir"
  createDirectory dir
  (generateTests dir >> action dir) `finally` removePathForcibly dir

generateTests :: FilePath -> IO ()
generateTests dir = do
  let seed = mkQCGen 42
      numFiles = 2
      matching fragment propertyId = fragment `isInfixOf` propertyIdText propertyId
  reports <-
    mconcat
      <$> sequence
        [ generate_integer_ring_properties Both FullCheck (matching "addition_associative") dir numFiles seed
        , generate_bitwise_cip0122_properties Both FullCheck (matching "getSet") dir numFiles seed
        , generate_bls12_381_properties Both FullCheck (matching "add_assoc") dir numFiles seed
        , generate_bls12_381_properties Both FullCheck (matching "compression_bit_set") dir numFiles seed
        , generate_bls12_381_properties Both FastCheck (matching "uncompress_out_of_group") dir numFiles seed
        , generate_bls12_381_properties Both FastCheck (matching "no_hash_collisions") dir numFiles seed
        ]
  -- The executable writes this; write one here so the check exercises the
  -- same format the consumer will see.
  _ <-
    writeInfo
      dir
      InfoDetails
        { infoTool = "generated-conformance-cases-roundtrip"
        , infoVersion = "0"
        , infoFormat = "both"
        , infoNumFiles = numFiles
        , infoSeed = 42
        , infoMatch = []
        , infoClean = True
        , infoCheck = "full"
        , infoCompleteTree = True
        }
      reports
  pure ()
