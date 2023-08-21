

-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Run benchmarks for Marlowe validators.
--
-----------------------------------------------------------------------------


{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}


module Main (
  -- * Entry point
  main
) where


import Cardano.Binary (serialize')
import Data.ByteString qualified as BS (writeFile)
import Data.ByteString.Base16 qualified as B16 (encode)
import Data.List (intercalate)
import PlutusBenchmark.Common (getDataDir)
import PlutusBenchmark.Marlowe.BenchUtil (semanticsBenchmarks, tabulateResults, writeFlatUPLCs)
import PlutusBenchmark.Marlowe.RolePayout qualified as RolePayout (benchmarks, validatorBytes,
                                                                   validatorHash, writeUPLC)
import PlutusBenchmark.Marlowe.Semantics qualified as Semantics (validatorBytes, validatorHash,
                                                                 writeUPLC)
import PlutusLedgerApi.V2 (ScriptHash, SerialisedScript)

-- | Run the benchmarks and export information about the validators and the benchmarking results.
main :: IO ()
main =
  do
    dir <- getDataDir

    -- Read the semantics benchmarks.
    benchmarks <- either error id <$> semanticsBenchmarks

    -- Write the tabulation of semantics benchmark results.
    writeFile (dir <> "/marlowe/exe/marlowe-semantics.tsv")
      . unlines . fmap (intercalate "\t")
      $ tabulateResults "Semantics" Semantics.validatorHash Semantics.validatorBytes benchmarks

    -- Write the flat UPLC files for the semantics benchmarks.
    writeFlatUPLCs Semantics.writeUPLC benchmarks
      (dir <> "/marlowe/scripts/semantics")

    -- Print the semantics validator, and write the plutus file.
    printValidator
      "Semantics"
      (dir <> "/marlowe/exe/marlowe-semantics")
      Semantics.validatorHash
      Semantics.validatorBytes

    -- Read the role-payout benchmarks.
    benchmarks' <- either error id <$> RolePayout.benchmarks

    -- Write the tabulation of role-payout benchmark results.
    writeFile (dir <> "/marlowe/exe/marlowe-rolepayout.tsv")
      . unlines . fmap (intercalate "\t")
      $ tabulateResults "Role Payout" RolePayout.validatorHash RolePayout.validatorBytes benchmarks'

    -- Write the flat UPLC files for the role-payout benchmarks.
    writeFlatUPLCs RolePayout.writeUPLC benchmarks'
      (dir <> "/marlowe/scripts/rolepayout")

    -- Print the role-payout validator, and write the plutus file.
    printValidator
      "Role payout"
      (dir <> "/marlowe/exe/marlowe-rolepayout")
      RolePayout.validatorHash
      RolePayout.validatorBytes


-- | Print information about a validator.
printValidator
  :: String  -- ^ The name of the validator.
  -> FilePath  -- ^ The base file path for exported files.
  -> ScriptHash  -- ^ The hash of the validator script.
  -> SerialisedScript  -- ^ The serialised validator.
  -> IO ()  -- ^ Action to print the information about the benchmarking, and write the files.
printValidator name file hash validator =
  do
    putStrLn $ name <> ":"
    putStrLn $ "  Validator hash: " <> show hash
    putStrLn $ "  Validator file: " <> file <> ".plutus"
    putStrLn $ "  Measurements file: " <> file <> ".tsv"
    BS.writeFile (file <> ".plutus")
      $ "{\"type\": \"PlutusScriptV2\", \"description\": \"\", \"cborHex\": \""
      <> B16.encode (serialize' validator) <> "\"}"
    putStrLn ""
