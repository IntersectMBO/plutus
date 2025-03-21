{- | Validation benchmarks for the CEK machine. -}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Common
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Proxy (Proxy (..))
import PlutusBenchmark.Common (BenchmarkClass (..), toNamedDeBruijnTerm)
import PlutusCore.Default (BuiltinSemanticsVariant (DefaultFunSemanticsVariantA))
import PlutusLedgerApi.Common (PlutusLedgerLanguage (PlutusV1))
import System.Directory (listDirectory)
import System.IO.Unsafe (unsafePerformIO)
import Test.Tasty qualified as T
import Test.Tasty.Ingredients (Ingredient)
import Test.Tasty.Options (OptionDescription (..))
import Test.Tasty.PAPI qualified as PAPI
import UntypedPlutusCore as UPLC

-- | Benchmark instance for tasty-papi benchmarks
-- Orphan instance for now, since the build fails
instance BenchmarkClass PAPI.Benchmarkable where
  whnf = PAPI.whnf

-- env definition is basically copypaste from tasty's source code
  type Benchmark PAPI.Benchmarkable = PAPI.Benchmark
  env res f = T.withResource
    (res >>= evaluate . force)
    (const $ pure ())
    (f . unsafePerformIO)
  bench = PAPI.bench

  type Options PAPI.Benchmarkable = [Ingredient]
  runWithOptions options = T.defaultMainWithIngredients options . T.testGroup "All"

--Benchmarks only for the CEK execution time of the data/*.flat validation scripts

main :: IO ()
main = do
  scriptDirectory <- getScriptDirectory
  files <- listDirectory scriptDirectory
  evalCtx <- evaluate $ mkEvalCtx PlutusV1 DefaultFunSemanticsVariantA
  let customOpts  = [Option (Proxy :: Proxy QuickFlag)]
      ingredients = T.includingOptions customOpts : PAPI.benchIngredients

      mkCekBM file program =
          benchTermCek evalCtx . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
      benchmarks = T.askOption $
        \(MkQuickFlag isQuick) -> T.testGroup "All" $
          mkBMs mkCekBM scriptDirectory (prepareFilePaths isQuick files)
  T.defaultMainWithIngredients ingredients benchmarks
