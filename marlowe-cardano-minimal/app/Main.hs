{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}


module Main (
  main
) where


import Benchmark.Marlowe (executeBenchmark)
import Benchmark.Marlowe.Types (Benchmark (bReferenceCost))
import Language.Marlowe.Scripts (rolePayoutValidatorBytes, rolePayoutValidatorHash)
import PlutusLedgerApi.V2 (SerialisedScript)
import Cardano.Binary (serialize')
import Language.Marlowe.Scripts (marloweValidatorBytes, marloweValidatorHash,
                                 rolePayoutValidatorBytes, rolePayoutValidatorHash)
import PlutusLedgerApi.V2 (ScriptHash, SerialisedScript)

import Benchmark.Marlowe.RolePayout qualified as RP
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as B16


main :: IO ()
main =
  do

    printValidator
      "Semantics"
      "marlowe-semantics.plutus"
      marloweValidatorHash
      marloweValidatorBytes

    printValidator
      "Role payout"
      "marlowe-rolepayout.plutus"
      rolePayoutValidatorHash
      rolePayoutValidatorBytes

    -- FIXME: Work in progress on benchmarks for semantics validator.
    mapM_ (printResult RP.serialisedValidator) RP.benchmarks

printValidator
  :: String
  -> FilePath
  -> ScriptHash
  -> SerialisedScript
  -> IO ()
printValidator name file hash validator =
  do
    putStrLn $ name <> ":"
    putStrLn $ "  Validator hash: " <> show hash
    putStrLn $ "  Validator file: " <> file
    BS.writeFile file
      $ "{\"type\": \"PlutusScriptV2\", \"description\": \"\", \"cborHex\": \""
      <> B16.encode (serialize' validator) <> "\"}"
    putStrLn ""


printResult
  :: SerialisedScript
  -> Benchmark
  -> IO ()
printResult validator benchmark =
  case executeBenchmark validator benchmark of
    Right (_, Right budget) -> putStrLn
                                 $ "actual = " <> show budget
                                 <> " vs expected = " <> show (bReferenceCost benchmark)
    Right (logs, Left msg) -> print (msg, logs)
    Left msg -> print msg
