{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications   #-}

module Benchmarks.Arrays (makeBenchmarks) where

import Prelude

import Common
import PlutusBenchmark.Common (EvaluationContext)

import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.ByteString (ByteString)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import PlutusCore.Builtin (mkTyBuiltin)
import PlutusCore.Core (Type)
import PlutusCore.Default (DefaultFun (IndexArray, LengthOfArray, ListToArray), DefaultUni)
import PlutusCore.Name.Unique (TyName)
import System.Random.Stateful (StdGen, UniformRange (uniformRM), runStateGen_, uniformByteStringM)

--------------------------------------------------------------------------------
-- Benchmarks ------------------------------------------------------------------

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
  [ benchLengthOfArray evalCtx gen
  , benchListToArray   evalCtx gen
  , benchIndexArray    evalCtx gen
  ]

benchLengthOfArray :: EvaluationContext -> StdGen -> Benchmark
benchLengthOfArray evalCtx gen =
  createOneTermBuiltinBench evalCtx LengthOfArray [tyArrayOfBS] listOfArrays
  where
    listOfArrays :: [Vector ByteString] =
      runStateGen_ gen \g -> replicateM 100 do
      arraySize <- uniformRM (1, 100) g
      Vector.replicateM arraySize do
        bsSize <- uniformRM (0, 10_000) g
        uniformByteStringM bsSize g

benchListToArray :: EvaluationContext -> StdGen -> Benchmark
benchListToArray evalCtx gen =
  createOneTermBuiltinBench evalCtx ListToArray [tyListOfBS] listOfLists
 where
  listOfLists :: [[ByteString]] =
    runStateGen_ gen \g -> replicateM 100 do
      listSize <- uniformRM (1, 100) g
      replicateM listSize do
        bsSize <- uniformRM (0, 10_000) g
        uniformByteStringM bsSize g

benchIndexArray :: EvaluationContext -> StdGen -> Benchmark
benchIndexArray evalCtx gen =
  createTwoTermBuiltinBenchElementwise evalCtx
    IndexArray
    [tyArrayOfBS]
    (zip arrays idxs)
 where
  (arrays :: [Vector ByteString], idxs :: [Integer]) =
    unzip $ runStateGen_ gen \g -> replicateM 100 do
      arraySize <- uniformRM (1, 100) g
      vec <- Vector.replicateM arraySize do
        bsSize <- uniformRM (0, 10_000) g
        uniformByteStringM bsSize g
      idx <- uniformRM (0, arraySize - 1) g
      pure (vec, fromIntegral idx)

--------------------------------------------------------------------------------
-- Helpers ---------------------------------------------------------------------

tyArrayOfBS :: Type TyName DefaultUni ()
tyArrayOfBS = mkTyBuiltin @_ @(Vector ByteString) ()

tyListOfBS :: Type TyName DefaultUni ()
tyListOfBS = mkTyBuiltin @_ @[ByteString] ()
