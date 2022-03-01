module Main where

import Codec.Serialise qualified as Serialise (serialise)
import Common
import Criterion
import Data.ByteString as BS
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short (toShort)
import Plutus.V1.Ledger.Api

{-|
for each data/*.flat validation script, it benchmarks
the time taken to only flat-deserialize the script

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation-decode --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation-decode --benchmark-options crowdfunding`.
-}
main :: IO ()
main = benchWith mkDecBM
  where
    mkDecBM :: FilePath -> BS.ByteString -> Benchmarkable
    mkDecBM _file bsFlat =
        let
            -- just "envelope" the flat strict-bytestring into a cbor's lazy serialised bytestring
            bslCBOR :: BSL.ByteString = Serialise.serialise bsFlat
            -- strictify and "short" the result cbor to create a real `SerializedScript`
            benchScript :: SerializedScript = toShort . BSL.toStrict $ bslCBOR
        in whnf isScriptWellFormed benchScript

