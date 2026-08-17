{-# LANGUAGE LambdaCase #-}

module Benchmarks.Data (makeBenchmarks) where

import Common
import Generators

import PlutusCore hiding (Constr)
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.ExMemoryUsage (MatchDataCostedPatterns (..))

import Criterion.Main
import Data.ByteString qualified as BS
import Data.List (nub)
import Data.Vector.Strict qualified as Strict
import Data.Word (Word8)
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

---------------- MatchData ----------------

encodeGap :: Int -> [Word8]
encodeGap gap
  | gap < 255 = [fromIntegral gap]
  | otherwise = 255 : encodeGap (gap - 255)

encodePattern :: Int -> [Int] -> BS.ByteString
encodePattern width captureIndices = BS.pack $ concatMap encodeGap gaps
  where
    gaps =
      zipWith
        (\next previous -> next - previous - 1)
        (captureIndices <> [width])
        (-1 : captureIndices)

spreadCaptures :: Int -> Int -> [Int]
spreadCaptures _ 0 = []
spreadCaptures width 1 = [width `div` 2]
spreadCaptures width count =
  [ index * (width - 1) `div` (count - 1)
  | index <- [0 .. count - 1]
  ]

matchDataWidths :: [Int]
matchDataWidths = [0, 1, 2, 4, 8, 16, 32, 64, 128, 254, 255, 256, 512, 1024, 2048, 4096]

matchDataCaptureCounts :: Int -> [Int]
matchDataCaptureCounts width = nub [0, min 1 width, width `div` 4, width `div` 2, width]

matchDataInputs :: [(Strict.Vector (Integer, BS.ByteString), Data)]
matchDataInputs = regularInputs <> tableInputs <> tagInputs <> payloadInputs
  where
    regularInputs =
      [ ( Strict.singleton (0, encodePattern width $ spreadCaptures width captures)
        , Constr 0 $ replicate width $ I 0
        )
      | width <- matchDataWidths
      , captures <- matchDataCaptureCounts width
      ]
    tablePattern = encodePattern 64 $ spreadCaptures 64 8
    tableInputs =
      [ ( Strict.fromList [(tag, tablePattern) | tag <- [0 .. alternatives - 1]]
        , Constr (alternatives - 1) $ replicate 64 $ I 0
        )
      | alternatives <- [1, 2, 4, 8, 16, 32, 64, 128, 256, 512 :: Integer]
      ]
    tagInputs =
      [ (Strict.singleton (tag, tablePattern), Constr tag $ replicate 64 $ I 0)
      | bitSize <- [64, 256, 1024, 4096, 16384, 65536 :: Integer]
      , let tag = 2 ^ bitSize
      ]
    payloadInputs =
      [ (Strict.singleton (0, encodePattern 1 [0]), Constr 0 [payload])
      | payload <-
          [ I $ 2 ^ (65536 :: Integer)
          , B $ BS.replicate (1024 * 1024) 0
          , iterate (\d -> Constr 0 [d]) (I 0) !! 10000
          ]
      ]

-- The benchmark varies width, capture density, pattern-table size, tag size, and nested payload
-- size.  The latter is intentionally independent: MatchData only moves pointers to captured Data
-- fields.
benchMatchData :: Benchmark
benchMatchData =
  createTwoTermBuiltinBenchElementwiseWithWrappers
    (MatchDataCostedPatterns, id)
    MatchData
    -- These benchmark terms are erased without typechecking. The placeholder result type is
    -- operationally irrelevant; its sole purpose here is to emit MatchData's required UPLC force.
    [TySOP () []]
    matchDataInputs

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
  , benchMatchData
  ]
