module Main where

import Plutus.Ledger.Test.EvaluationContext (evalCtxForTesting)
import Plutus.V1.Ledger.Api
import Plutus.V1.Ledger.Scripts


import Codec.Serialise qualified as Serialise (serialise)
import Common
import Criterion
import Data.ByteString as BS
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short (toShort)
import Data.Either

import PlutusCore.Evaluation.Machine.ExBudget
import UntypedPlutusCore qualified as UPLC

{-|
for each data/*.flat validation script, it benchmarks
the whole time taken from script deserialization to script execution result.

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation-full --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation-full --benchmark-options crowdfunding`.
-}
main :: IO ()
main = benchWith mkFullBM
  where
    mkFullBM :: FilePath -> BS.ByteString -> Benchmarkable
    mkFullBM file bsFlat =
        let
            body :: Term
            (UPLC.Program _ v body) = unsafeUnflat file bsFlat

            -- We make some effort to mimic what happens on-chain, including the provision of the
            -- script arguments. However, the inputs we have are *fully applied*. So we try and reverse
            -- that by stripping off the arguments here. Conveniently, we know that they will be
            -- Data constants. Annoyingly we can't just assume it's the first 3 arguments, since some
            -- of them are policy scripts with only 2.
            (term, args) = peelDataArguments body

            bslCBOR :: BSL.ByteString = Serialise.serialise (Script $ UPLC.Program () v term)
            -- strictify and "short" the result cbor to create a real `SerializedScript`
            benchScript :: SerializedScript = toShort . BSL.toStrict $ bslCBOR

        in  whnf (\ script ->
                      (isRight $ snd $ evaluateScriptRestricting
                        (ProtocolVersion 6 0)
                        -- no logs
                        Quiet
                        evalCtxForTesting
                        -- uses restricting(enormous) instead of counting to include the periodic budget-overspent check
                        (unExRestrictingBudget enormousBudget)
                        script
                        args)
                      || error "script failed to run"
                 )
            benchScript
