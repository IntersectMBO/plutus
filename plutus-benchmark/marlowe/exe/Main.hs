{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Cardano.Binary (serialize')
import Data.ByteString qualified as BS (writeFile)
import Data.ByteString.Base16 qualified as B16 (encode)
import Data.Foldable
import Data.Functor (void)
import Data.List (intercalate)
import PlutusBenchmark.Common (getDataDir)
import PlutusBenchmark.Marlowe.BenchUtil
  ( rolePayoutBenchmarks
  , semanticsBenchmarks
  , tabulateResults
  , writeFlat
  , writeFlatUPLCs
  )
import PlutusBenchmark.Marlowe.RolePayout qualified as RolePayout
import PlutusBenchmark.Marlowe.Scripts.Data.RolePayout qualified as DataRolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Data.Semantics qualified as DataSemantics (marloweValidator)
import PlutusBenchmark.Marlowe.Scripts.RolePayout qualified as RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics qualified as Semantics (marloweValidator)
import PlutusBenchmark.Marlowe.Semantics qualified as Semantics
import PlutusLedgerApi.V2 (ScriptHash, SerialisedScript)
import PlutusTx.Code (getPlc)
import System.FilePath (normalise, (</>))

{- Generates the UPLC .flat files for benchmarking the two marlowe validators.
Each flat file is consists of the compiled validator applied to a set of
fixed arguments (redeemer, input and datum), read from file.

Additionally:
- Saves both validators without arguments to file
- Prints table of the reference
-}
main :: IO ()
main = do
  dir <- normalise <$> getDataDir

  let semanticsUplcDir = dir </> "marlowe/scripts/semantics"
      semanticsValidatorExportDir = dir </> "marlowe/exe/marlowe-semantics"
      semanticsValidatorResults = dir </> "marlowe/exe/marlowe-semantics.tsv"

  let rolePayoutUplcDir = dir </> "marlowe/scripts/rolepayout"
      rolePayoutValidatorExportDir = dir </> "marlowe/exe/marlowe-rolepayout"
      rolePayoutValidatorResults = dir </> "marlowe/exe/marlowe-rolepayout.tsv"

  -- Read the benchmark arguments for semantics validator
  benchmarks <- either error id <$> semanticsBenchmarks

  -- Write the tabulation of semantics benchmark results.
  writeFile semanticsValidatorResults . unlines . (intercalate "\t" <$>) $
    tabulateResults
      "Semantics"
      Semantics.validatorHash
      Semantics.validatorBytes
      benchmarks

  -- Write the flat UPLC files for the semantics benchmarks.
  writeFlatUPLCs Semantics.writeUPLC benchmarks semanticsUplcDir

  -- Write flat validators
  let
    vs =
      [ (semanticsUplcDir </> "validator.flat", Semantics.marloweValidator)
      , (semanticsUplcDir </> "validator-data.flat", DataSemantics.marloweValidator)
      , (rolePayoutUplcDir </> "validator.flat", RolePayout.rolePayoutValidator)
      , (rolePayoutUplcDir </> "validator-data.flat", DataRolePayout.rolePayoutValidator)
      ]

  for_ vs $ \(path, validator) ->
    writeFlat path (void . getPlc $ validator)

  -- Print the semantics validator, and write the plutus file.
  printValidator
    "Semantics"
    semanticsValidatorExportDir
    Semantics.validatorHash
    Semantics.validatorBytes

  -- Read the role-payout benchmarks.
  benchmarks' <- either error id <$> rolePayoutBenchmarks

  -- Write the tabulation of role-payout benchmark results.
  writeFile rolePayoutValidatorResults . unlines . (intercalate "\t" <$>) $
    tabulateResults
      "Role Payout"
      RolePayout.validatorHash
      RolePayout.validatorBytes
      benchmarks'

  -- Write the flat UPLC files for the role-payout benchmarks.
  writeFlatUPLCs RolePayout.writeUPLC benchmarks' rolePayoutUplcDir

  -- Print the role-payout validator, and write the plutus file.
  printValidator
    "Role payout"
    rolePayoutValidatorExportDir
    RolePayout.validatorHash
    RolePayout.validatorBytes

-- | Print information about a validator.
printValidator
  :: String
  -- ^ The name of the validator.
  -> FilePath
  -- ^ The base file path for exported files.
  -> ScriptHash
  -- ^ The hash of the validator script.
  -> SerialisedScript
  -- ^ The serialised validator.
  -> IO ()
  {-^ Action to print the information about the benchmarking,
  and write the files. -}
printValidator name file hash validator = do
  putStrLn $ name <> ":"
  putStrLn $ "  Validator hash: " <> show hash
  putStrLn $ "  Validator file: " <> file <> ".plutus"
  putStrLn $ "  Measurements file: " <> file <> ".tsv"
  BS.writeFile (file <> ".plutus") $
    "{\"type\": \"PlutusScriptV2\", \"description\": \"\", \"cborHex\": \""
      <> B16.encode (serialize' validator)
      <> "\"}"
  putStrLn ""
