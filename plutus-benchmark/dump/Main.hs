module Main where

import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS
import PlutusBenchmark.Marlowe.Scripts.Semantics
import PlutusLedgerApi.Common (serialiseCompiledCode)

main :: IO ()
main = do
  let cc = marloweValidator
      name = "marlowe.uplc"
      bytes = SBS.fromShort $ serialiseCompiledCode cc
  B.writeFile name bytes
