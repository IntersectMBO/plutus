{-| Force-delay benchmarks.

It has the same setup as the validation benchmark. The scripts are produced
using the code in @PlutusBenchmark.ForceDelay.Script@. -}
module Main where

import Control.Exception (evaluate)
import PlutusBenchmark.Common (toNamedDeBruijnTerm)
import PlutusBenchmark.ForceDelay.Common (benchTermCek, benchWith, mkEvalCtx, unsafeUnflat)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantE))
import PlutusLedgerApi.Common (PlutusLedgerLanguage (PlutusV3))
import UntypedPlutusCore as UPLC

-- Benchmarks only for the CEK execution time of the data/*.flat scripts.
main :: IO ()
main = do
  evalCtx <- evaluate $ mkEvalCtx PlutusV3 DefaultFunSemanticsVariantE
  let mkCekBM file program =
        benchTermCek evalCtx . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
  benchWith mkCekBM
