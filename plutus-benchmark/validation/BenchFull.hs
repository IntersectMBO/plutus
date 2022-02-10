{-# LANGUAGE TypeApplications #-}
module Main where

import Codec.Serialise qualified as Serialise (serialise)
import Common
import Criterion
import Data.ByteString.Lazy (toStrict)
import Data.ByteString.Short
import Data.Maybe
import Flat.Run
import Plutus.V1.Ledger.Api
import Plutus.V1.Ledger.Scripts
import PlutusCore.Evaluation.Machine.ExBudget
import UntypedPlutusCore as UPLC

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
    mkFullBM _file flatBS =
        let cbor = toShort $ toStrict $ Serialise.serialise $
                       case unflat @(UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()) flatBS of
                           Left _e -> error "mpla"
                           Right p -> Script p
        in  whnf (\ cborbs ->
                      snd $ evaluateScriptRestricting Quiet (fromJust defaultCostModelParams) (unExRestrictingBudget enormousBudget)
                      cborbs []) cbor
