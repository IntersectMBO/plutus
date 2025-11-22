{-# LANGUAGE LambdaCase #-}

module Benchmarks.Data (makeBenchmarks) where

import Common
import Generators

import PlutusCore hiding (Constr)
import PlutusCore.Data

import Criterion.Main
import System.Random (StdGen)

{-| Benchmarks for builtins operating on Data.  Recall that Data is defined by

      data Data =
           Constr Integer [Data]
         | Map [(Data, Data)]
         | List [Data]
         | I Integer
         | B ByteString -}
isConstr :: Data -> Bool
isConstr = \case Constr {} -> True; _ -> False

isMap :: Data -> Bool
isMap = \case Map {} -> True; _ -> False

isList :: Data -> Bool
isList = \case List {} -> True; _ -> False

isI :: Data -> Bool
isI = \case I {} -> True; _ -> False

isB :: Data -> Bool
isB = \case B {} -> True; _ -> False

---------------- ChooseData ----------------

-- Choose one of five alternatives depending on which constructor you've got.
-- We can't explore a significant fraction of a six-dimensional parameter space;
-- fortunately 'chooseData' is parametric in its last five arguments so we can
-- just give it integers for those.
benchChooseData :: Benchmark
benchChooseData = bgroup (show name) [mkBM d | d <- take 100 dataSample]
  where
    name = ChooseData
    mkBM d =
      benchDefault (showMemoryUsage d) $
        mkApp6
          name
          [integer]
          d
          (111 :: Integer)
          (222 :: Integer)
          (333 :: Integer)
          (444 :: Integer)
          (555 :: Integer)

---------------- Construction ----------------

-- Apply Constr to an integer and a list of Data
benchConstrData :: StdGen -> Benchmark
benchConstrData gen = createTwoTermBuiltinBench ConstrData [] ints lists
  where
    (ints, _) = makeSizedIntegers gen [1 .. 20]
    lists = take 20 . map unList $ filter isList dataSample
    unList = \case List l -> l; _ -> error "Expected List"

benchMapData :: Benchmark
benchMapData = createOneTermBuiltinBench MapData [] pairs
  where
    pairs = take 50 . map unMap $ filter isMap dataSample
    unMap = \case Map l -> l; _ -> error "Expected Map"

--
-- Apply List
benchListData :: Benchmark
benchListData = createOneTermBuiltinBench ListData [] lists
  where
    lists = take 50 . map unList $ filter isList dataSample
    unList = \case List l -> l; _ -> error "Expected List"

-- Apply I
benchIData :: Benchmark
benchIData =
  createOneTermBuiltinBench IData [] ints
  where
    ints = take 50 . map unI $ filter isI dataSample
    unI = \case I n -> n; _ -> error "Expected I"

-- Apply B
benchBData :: Benchmark
benchBData =
  createOneTermBuiltinBench BData [] bss
  where
    bss = take 50 . map unB $ filter isB dataSample
    unB = \case B s -> s; _ -> error "Expected B"

---------------- Elimination ----------------

-- Match against Constr, failing otherwise
benchUnConstrData :: Benchmark
benchUnConstrData = createOneTermBuiltinBench UnConstrData [] constrData
  where
    constrData = take 50 $ filter isConstr dataSample

-- Match against Map, failing otherwise
benchUnMapData :: Benchmark
benchUnMapData = createOneTermBuiltinBench UnMapData [] mapData
  where
    mapData = take 50 $ filter isMap dataSample

-- Match against List, failing otherwise
benchUnListData :: Benchmark
benchUnListData = createOneTermBuiltinBench UnListData [] listData
  where
    listData = take 100 $ filter isList dataSample

-- Match against I, failing otherwise
benchUnIData :: Benchmark
benchUnIData = createOneTermBuiltinBench UnIData [] idata
  where
    idata = take 50 $ filter isI dataSample

-- Match against B, failing otherwise
benchUnBData :: Benchmark
benchUnBData = createOneTermBuiltinBench UnBData [] bdata
  where
    bdata = take 50 $ filter isB dataSample

---------------- Equality ----------------

-- This one is potentially troublesome because our measure of memory size for
-- Data is quite crude and we're using '==' which doesn't pay any attention to
-- the costs of sub-components.
benchEqualsData :: Benchmark
benchEqualsData =
  createTwoTermBuiltinBenchElementwise EqualsData [] $ pairWith copyData dataSampleForEq

-- 400 elements: should take about 35 minutes to benchmark

benchSerialiseData :: Benchmark
benchSerialiseData =
  createOneTermBuiltinBench SerialiseData [] args
  where
    args = dataSampleForEq

-- FIXME: see if we can find a better sample for this. More generally, how
-- does the internal structure of a Data object influence serialisation
-- time?  What causes a Data object to be quick or slow to serialise?

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [ benchChooseData
  , benchConstrData gen
  , benchMapData
  , benchListData
  , benchIData
  , benchBData
  , benchUnConstrData
  , benchUnMapData
  , benchUnListData
  , benchUnIData
  , benchUnBData
  , benchEqualsData
  , benchSerialiseData
  ]
