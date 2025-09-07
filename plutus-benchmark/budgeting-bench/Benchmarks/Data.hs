{-# LANGUAGE LambdaCase #-}

module Benchmarks.Data (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

import PlutusCore hiding (Constr)
import PlutusCore.Data

import Criterion.Main
import System.Random (StdGen)

{- | Benchmarks for builtins operating on Data.  Recall that Data is defined by

      data Data =
           Constr Integer [Data]
         | Map [(Data, Data)]
         | List [Data]
         | I Integer
         | B ByteString
-}


isConstr :: Data -> Bool
isConstr = \case {Constr {} -> True; _ -> False}

isMap :: Data -> Bool
isMap = \case {Map {} -> True; _ -> False}

isList :: Data -> Bool
isList = \case {List {} -> True; _ -> False}

isI :: Data -> Bool
isI = \case {I {} -> True; _ -> False}

isB :: Data -> Bool
isB = \case {B {} -> True; _ -> False}


---------------- ChooseData ----------------

-- Choose one of five alternatives depending on which constructor you've got.
-- We can't explore a significant fraction of a six-dimensional parameter space;
-- fortunately 'chooseData' is parametric in its last five arguments so we can
-- just give it integers for those.
benchChooseData :: EvaluationContext -> Benchmark
benchChooseData evalCtx =
  bgroup (show name) [mkBM d | d <- take 100 dataSample]
  where name = ChooseData
        mkBM d = benchWithCtx evalCtx (showMemoryUsage d) $
                 mkApp6 name [integer] d (111::Integer) (222::Integer)
                 (333::Integer) (444::Integer) (555::Integer)


---------------- Construction ----------------

-- Apply Constr to an integer and a list of Data
benchConstrData :: EvaluationContext -> StdGen -> Benchmark
benchConstrData evalCtx gen =
  createTwoTermBuiltinBench evalCtx ConstrData [] ints lists
  where (ints, _) = makeSizedIntegers gen [1..20]
        lists = take 20 . map unList $ filter isList dataSample
        unList = \case { List l -> l ; _ -> error "Expected List" }

benchMapData :: EvaluationContext -> Benchmark
benchMapData evalCtx =
  createOneTermBuiltinBench evalCtx MapData [] pairs
  where pairs = take 50 . map unMap $ filter isMap dataSample
        unMap = \case { Map l -> l ; _ -> error "Expected Map" }
--
-- Apply List
benchListData :: EvaluationContext -> Benchmark
benchListData evalCtx =
  createOneTermBuiltinBench evalCtx ListData [] lists
  where lists = take 50 . map unList $ filter isList dataSample
        unList = \case { List l -> l ; _ -> error "Expected List" }

-- Apply I
benchIData :: EvaluationContext -> Benchmark
benchIData evalCtx =
  createOneTermBuiltinBench evalCtx IData [] ints
  where ints = take 50 . map unI $ filter isI dataSample
        unI = \case { I n -> n ; _ -> error "Expected I" }

-- Apply B
benchBData :: EvaluationContext -> Benchmark
benchBData evalCtx =
  createOneTermBuiltinBench evalCtx BData [] bss
  where bss =  take 50 . map unB $ filter isB dataSample
        unB = \case { B s -> s ; _ -> error "Expected B" }


---------------- Elimination ----------------

-- Match against Constr, failing otherwise
benchUnConstrData :: EvaluationContext -> Benchmark
benchUnConstrData evalCtx =
  createOneTermBuiltinBench evalCtx UnConstrData [] constrData
  where constrData = take 50 $ filter isConstr dataSample

-- Match against Map, failing otherwise
benchUnMapData :: EvaluationContext -> Benchmark
benchUnMapData evalCtx =
  createOneTermBuiltinBench evalCtx UnMapData [] mapData
  where mapData = take 50 $ filter isMap dataSample

-- Match against List, failing otherwise
benchUnListData :: EvaluationContext -> Benchmark
benchUnListData evalCtx =
  createOneTermBuiltinBench evalCtx UnListData [] listData
  where listData = take 100 $ filter isList dataSample

-- Match against I, failing otherwise
benchUnIData :: EvaluationContext -> Benchmark
benchUnIData evalCtx =
  createOneTermBuiltinBench evalCtx UnIData [] idata
  where idata = take 50 $ filter isI dataSample

-- Match against B, failing otherwise
benchUnBData :: EvaluationContext -> Benchmark
benchUnBData evalCtx =
  createOneTermBuiltinBench evalCtx UnBData [] bdata
  where bdata = take 50 $ filter isB dataSample

---------------- Equality ----------------

-- This one is potentially troublesome because our measure of memory size for
-- Data is quite crude and we're using '==' which doesn't pay any attention to
-- the costs of sub-components.
benchEqualsData :: EvaluationContext -> Benchmark
benchEqualsData evalCtx =
  createTwoTermBuiltinBenchElementwise evalCtx EqualsData [] $ pairWith copyData dataSampleForEq
  -- 400 elements: should take about 35 minutes to benchmark

benchSerialiseData :: EvaluationContext -> Benchmark
benchSerialiseData evalCtx =
  createOneTermBuiltinBench evalCtx SerialiseData [] args
  where args = dataSampleForEq
  -- FIXME: see if we can find a better sample for this. More generally, how
  -- does the internal structure of a Data object influence serialisation
  -- time?  What causes a Data object to be quick or slow to serialise?

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
    [ benchChooseData    evalCtx
    , benchConstrData    evalCtx gen
    , benchMapData       evalCtx
    , benchListData      evalCtx
    , benchIData         evalCtx
    , benchBData         evalCtx
    , benchUnConstrData  evalCtx
    , benchUnMapData     evalCtx
    , benchUnListData    evalCtx
    , benchUnIData       evalCtx
    , benchUnBData       evalCtx
    , benchEqualsData    evalCtx
    , benchSerialiseData evalCtx
    ]
