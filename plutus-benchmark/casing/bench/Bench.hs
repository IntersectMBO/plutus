{-# LANGUAGE BangPatterns #-}

{- | This benchmark cases measures efficiency of builtin case operations. Each branches exclusively
   contain casing operations only.
-}

module Main (main) where

import Criterion.Main

import PlutusBenchmark.Common (benchTermCek, getConfig, mkMostRecentEvalCtx)
import PlutusLedgerApi.Common (EvaluationContext)

import PlutusBenchmark.Casing qualified as Casing

import Control.Exception
import Data.Functor

benchmarks :: EvaluationContext -> [Benchmark]
benchmarks ctx =
    [ bgroup "casing"
      [ mkBMs "pairFstSnd" Casing.pairFstSnd
      , mkBMs "pairCasing" Casing.pairCasing
      , mkBMs "chooseUnit" Casing.chooseUnit
      , mkBMs "unitCasing" Casing.unitCasing
      , mkBMs "headList" Casing.headList
      , mkBMs "headListCasing" Casing.headListCasing
      , mkBMs "bool" Casing.casingBool
      , mkBMs "bool one branch" Casing.casingBoolOneBranch
      , mkBMs "integer" Casing.casingInteger
      , mkBMs "list" Casing.casingList
      , mkBMs "list one branch" Casing.casingListOneBranch
      , mkBMsSmall "regularApply" Casing.regularApply
      , mkBMsSmall "caseApply" Casing.caseApply
      ]
    ]
    where
      mkBMs name f =
        bgroup name $ [2000, 4000..12000] <&> \n ->
          bench (show n) $ benchTermCek ctx (f n)
      mkBMsSmall name f =
        bgroup name $ [3, 10, 30, 100, 500, 1000] <&> \n ->
          bench (show n) $ benchTermCek ctx (f n)

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  config <- getConfig 15.0
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith config $ benchmarks evalCtx
