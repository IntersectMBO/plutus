module Main where

import PlutusLedgerApi.V1
import UntypedPlutusCore qualified as UPLC

import Common
import Control.Exception
import Criterion
import Data.ByteString as BS

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
            -- sure to remove them from the fully-applied script, and then decode back just the
            -- "unsaturated" script
            -- See Note [Deserialization size limits]
            (unsaturated, _args) = peelDataArguments fullyApplied

            -- we then have to re-encode and serialise it
            benchScript :: SerialisedScript = serialiseUPLC $ UPLC.Program () v unsaturated

            -- Deserialize using 'FakeNamedDeBruijn' to get the fake names added
        in whnf (either throw id . assertScriptWellFormed (ProtocolVersion 6 0)
                ) benchScript
