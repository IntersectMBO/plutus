{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}


module Main (
  main
) where


import Benchmark.Marlowe ( executeBenchmark )
import Benchmark.Marlowe.Types ( Benchmark(bReferenceCost) )
import Language.Marlowe.Scripts
    ( rolePayoutValidatorBytes, rolePayoutValidatorHash )
import PlutusLedgerApi.V2 ( SerialisedScript )

import Benchmark.Marlowe.RolePayout qualified as RP
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as B16
import Data.ByteString.Short qualified as SBS


main :: IO ()
main =
  do

    -- FIXME: Work in progress on benchmarks for semantics validator.
--  putStrLn $ "Semantics validator hash:   " <> show marloweValidatorHash
--  BS.writeFile "marlowe-semantics.plutus"
--    $ "{\"type\": \"PlutusScriptV2\", \"description\": \"\", \"cborHex\": \""
--    <> B16.encode (SBS.fromShort marloweValidatorBytes) <> "\"}"

    putStrLn $ "Role-payout validator hash: " <> show rolePayoutValidatorHash
    -- FIXME: I suspect that this serialization is incorrect because hashing it
    --        with `cardano-cli` does not agree with the hash computed above.
    BS.writeFile "marlowe-rolepayout.plutus"
      $ "{\"type\": \"PlutusScriptV2\", \"description\": \"\", \"cborHex\": \""
      <> B16.encode (SBS.fromShort rolePayoutValidatorBytes) <> "\"}"

    mapM_ (printResult RP.serialisedValidator) RP.benchmarks

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
