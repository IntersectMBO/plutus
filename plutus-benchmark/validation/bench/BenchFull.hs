{-# LANGUAGE BangPatterns #-}
module Main where

import PlutusCore.Evaluation.Machine.ExBudget
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.V1
import UntypedPlutusCore qualified as UPLC

import Common
import Control.DeepSeq (force)
import Control.Exception
import Criterion
import Data.ByteString as BS

{-|
for each data/*.flat validation script, it benchmarks
the whole time taken from script deserialization to script execution result.

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation-full --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation-full --benchmark-options crowdfunding`.
-}
main :: IO ()
main = do
    evalCtx <- evaluate $ force mkEvalCtx
    let mkFullBM :: FilePath -> BS.ByteString -> Benchmarkable
        mkFullBM file bsFlat =
            let UPLC.Program () ver body = unsafeUnflat file bsFlat
                -- We make some effort to mimic what happens on-chain, including the provision of
                -- the script arguments. However, the inputs we have are *fully applied*. So we try
                -- and reverse that by stripping off the arguments here. Conveniently, we know that
                -- they will be Data constants. Annoyingly we can't just assume it's the first 3
                -- arguments, since some of them are policy scripts with only 2.
                (term, args) = peelDataArguments body
                -- strictify and "short" the result cbor to create a real `SerialisedScript`
                !benchScript = force . serialiseUPLC $ UPLC.Program () ver term
                eval script =
                    either (error . show) (\_ -> ()) . snd $ evaluateScriptRestricting
                        futurePV
                        -- no logs
                        Quiet
                        evalCtx
                        -- uses restricting(enormous) instead of counting to include the periodic
                        -- budget-overspent check
                        (unExRestrictingBudget enormousBudget)
                        (either (error . show) id $ deserialiseScript futurePV script)
                        args
            in whnf eval benchScript
    benchWith mkFullBM
