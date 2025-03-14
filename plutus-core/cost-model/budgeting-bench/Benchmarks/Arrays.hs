{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE TypeApplications #-}

module Benchmarks.Arrays (makeBenchmarks) where

import Prelude

import Common (createOneTermBuiltinBench, createTwoTermBuiltinBench)
import Control.Monad (replicateM)
import Criterion.Main (Benchmark)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import PlutusCore.Builtin (mkTyBuiltin)
import PlutusCore.Core (Type)
import PlutusCore.Default (DefaultFun (IndexArray, LengthOfArray, ListToArray), DefaultUni)
import PlutusCore.Name.Unique (TyName)
import System.Random.Stateful (StdGen, UniformRange (uniformRM), runStateGen_)

--------------------------------------------------------------------------------
-- Benchmarks ------------------------------------------------------------------

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ benchLengthOfArray gen
  , benchListToArray gen
  , benchIndexArray gen
  ]

benchLengthOfArray :: StdGen -> Benchmark
benchLengthOfArray gen =
  createOneTermBuiltinBench LengthOfArray [tyArrayOfInteger] listOfArrays
 where
  listOfArrays :: [Vector Integer] =
    runStateGen_ gen \g -> replicateM 100 do
      arraySize <- uniformRM (1, 100) g
      Vector.replicateM arraySize (uniformRM intRange g)

benchListToArray :: StdGen -> Benchmark
benchListToArray gen =
  createOneTermBuiltinBench ListToArray [tyListOfInteger] listOfLists
 where
  listOfLists :: [[Integer]] =
    runStateGen_ gen \g -> replicateM 100 do
      listSize <- uniformRM (1, 100) g
      replicateM listSize (uniformRM intRange g)

benchIndexArray :: StdGen -> Benchmark
benchIndexArray gen =
  createTwoTermBuiltinBench IndexArray [tyArrayOfInteger] arrays idxs
 where
  (arrays :: [Vector Integer], idxs :: [Integer]) =
    unzip $ runStateGen_ gen \g -> replicateM 100 do
      arraySize <- uniformRM (1, 100) g
      vec <- Vector.replicateM arraySize (uniformRM intRange g)
      idx <- uniformRM (0, arraySize - 1) g
      pure (vec, fromIntegral idx)

--------------------------------------------------------------------------------
-- Helpers ---------------------------------------------------------------------

tyListOfInteger :: Type TyName DefaultUni ()
tyListOfInteger = mkTyBuiltin @_ @[Integer] ()

tyArrayOfInteger :: Type TyName DefaultUni ()
tyArrayOfInteger = mkTyBuiltin @_ @(Vector Integer) ()

intRange :: (Integer, Integer)
intRange =
  ( fromIntegral (minBound @Int) - 10
  , fromIntegral (maxBound @Int) + 10
  )
