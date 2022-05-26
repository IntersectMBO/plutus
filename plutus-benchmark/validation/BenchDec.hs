module Main where

import PlutusLedgerApi.V1
import PlutusLedgerApi.V1.Scripts
import UntypedPlutusCore qualified as UPLC

import Codec.Serialise qualified as Serialise (serialise)
import Common
import Criterion
import Data.ByteString as BS
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short (toShort)

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
    mkDecBM file bsFlat =
        let
            UPLC.Program _ v (fullyApplied :: Term) = unsafeUnflat file bsFlat

            -- script arguments are not 64-byte size limited, so we make
            -- sure to remove them from the fully-applied script, and then decode back just the "unsaturated" script
            -- See Note [Deserialization size limits]
            (unsaturated, _args) = peelDataArguments fullyApplied

            -- we then have to re-encode it
            bslCBOR :: BSL.ByteString = Serialise.serialise (Script $ UPLC.Program () v unsaturated)
            -- strictify and "short" the result cbor to create a real `SerializedScript`

            benchScript :: SerializedScript = toShort . BSL.toStrict $ bslCBOR

            -- Deserialize using 'FakeNamedDeBruijn' to get the fake names added
        in whnf (\ s ->
                     isScriptWellFormed (ProtocolVersion 6 0) s
                     || error "validation script failed to decode"
                ) benchScript

