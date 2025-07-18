{- | Validation benchmarks for the CEK machine. -}
module Main where

import Common (benchTermCek, benchWith, mkEvalCtx)
import Control.Exception (evaluate)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantA))
import PlutusLedgerApi.Common (PlutusLedgerLanguage (PlutusV1))

{-|
 Benchmarks only for the CEK execution time of the data/*.flat validation scripts

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation --benchmark-options crowdfunding`.
-}
main :: IO ()
main = do
  -- The validation benchmarks were all created with PlutusV1, so let's make
  -- sure that the evaluation context matches.
  evalCtx <- evaluate $ mkEvalCtx PlutusV1 DefaultFunSemanticsVariantA
  benchWith $ \(~_) (~_) -> benchTermCek evalCtx
