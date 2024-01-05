-- editorconfig-checker-disable-file

{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-# LANGUAGE TypeOperators #-}

module Benchmarks.Bitwise (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.ByteString qualified as BS
import System.Random (StdGen, randomR)

import Hedgehog qualified as H


import Control.DeepSeq (NFData, force)
import PlutusCore.Evaluation.Machine.ExMemoryUsage

---------------- ByteString builtins ----------------

integerLength :: BS.ByteString -> Integer
integerLength = fromIntegral . BS.length

-- Arguments for single-argument benchmarks: 150 entries.
-- Note that the length is eight times the size.
smallerByteStrings150 :: H.Seed -> [BS.ByteString]
smallerByteStrings150 seed = makeSizedByteStrings seed $ fmap (10*) [1..150]

-- Arguments for two-argument benchmarks: 21 entries.
-- Note that the length is eight times the size.
largerByteStrings21 :: H.Seed -> [BS.ByteString]
largerByteStrings21 seed = makeSizedByteStrings seed $ fmap (250*) [0..20]

largerByteStrings150 :: H.Seed -> [BS.ByteString]
largerByteStrings150 seed = makeSizedByteStrings seed $ fmap (100*) [1..150]

smallerIntegers150 :: StdGen -> [Integer]
smallerIntegers150 gen = fst $ makeSizedIntegers gen $ fmap (10*) [1..150]

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name =
    createTwoTermBuiltinBench name [] (largerByteStrings21 seedA) (largerByteStrings21 seedB)


createTwoTermBuiltinBench'
    :: ( fun ~ DefaultFun, uni ~ DefaultUni
       , uni `HasTermLevel` a, DefaultUni `HasTermLevel` b
       , ExMemoryUsage a, ExMemoryUsage b
       , NFData a, NFData b
       )
    => fun
    -> String
    -> [Type tyname uni ()]
    -> [a]
    -> [b]
    -> Benchmark
createTwoTermBuiltinBench' name suffix tys xs ys =
    bgroup (show name ++ suffix) $ [bgroup (showMemoryUsage x) [mkBM x y | y <- ys] | x <- xs]
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name tys x y

createThreeTermBuiltinBenchElementwise'
    :: ( uni ~ DefaultUni
       , uni `HasTermLevel` a, uni `HasTermLevel` c
       , ExMemoryUsage a, ExMemoryUsage c
       , NFData a, NFData c
       )
    => String
    -> [(a,Int,c)]
    -> Benchmark
createThreeTermBuiltinBenchElementwise' suffix inputs =
    let name = IntegerToByteString
        mkOneBM (x, width, z) =
            let width' = 8 * fromIntegral width  -- Widths are in words: we need to convert those to widths in bytes
            in bgroup (showMemoryUsage x) [
                    bgroup (showMemoryUsage (LiteralByteSize width')) [mkBM x width' z]
                   ]
        mkBM x y z = benchDefault (showMemoryUsage z) $ mkApp3 name [] x y z
    in bgroup (show name  ++ suffix) $ fmap mkOneBM inputs


------------------------- ByteStringToInteger -------------------------


benchByteStringToIntegerFalseSmall :: Benchmark
benchByteStringToIntegerFalseSmall = createTwoTermBuiltinBench' ByteStringToInteger "FalseSmall" [] [False, True] (smallerByteStrings150 seedA)

benchByteStringToIntegerTrueSmall :: Benchmark
benchByteStringToIntegerTrueSmall = createTwoTermBuiltinBench' ByteStringToInteger "TrueSmall" [] [False, True] (smallerByteStrings150 seedA)

benchByteStringToIntegerFalseBig :: Benchmark
benchByteStringToIntegerFalseBig = createTwoTermBuiltinBench' ByteStringToInteger "FalseBig" [] [False, True] (smallerByteStrings150 seedA)

benchByteStringToIntegerTrueBig :: Benchmark
benchByteStringToIntegerTrueBig = createTwoTermBuiltinBench' ByteStringToInteger "TrueBig" [] [False, True] (smallerByteStrings150 seedA)

------------------------- IntegerToByteString -------------------------

-- Width = 1-150 ExMemory (8 times that in bytes)
-- input = random integer 'width'-bytes integer
benchIntegerToByteStringBoundedFalseSmall :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseSmall gen =
    let widths = [1..150]  -- width in words
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseSmall" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueSmall :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueSmall gen =
    let widths = [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueSmall" $ zip3 (repeat True) widths inputs

benchIntegerToByteStringBoundedFalseBig :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseBig gen =
    let widths = fmap (10*) [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseBig" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueBig :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueBig gen =
    let widths = fmap (10*) [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueBig" $ zip3 (repeat True) widths inputs


benchIntegerToByteStringUnboundedFalseSmall :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedFalseSmall gen =
    let widths = [1..150]  -- width in words
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedFalseSmall" $ zip3 (repeat False) (repeat 0) inputs

benchIntegerToByteStringUnboundedTrueSmall :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedTrueSmall gen =
    let widths = [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedTrueSmall" $ zip3 (repeat True) (repeat 0) inputs

benchIntegerToByteStringUnboundedFalseBig :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedFalseBig gen =
    let widths = fmap (10*) [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedFalseBig" $ zip3 (repeat False) (repeat 0) inputs

benchIntegerToByteStringUnboundedTrueBig :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedTrueBig gen =
    let widths = fmap (10*) [1..150]
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedTrueBig" $ zip3 (repeat True) (repeat 0) inputs


benchIntegerToByteStringTrue0 :: StdGen -> Benchmark
benchIntegerToByteStringTrue0 gen =
    bgroup name $ fmap mkBM (smallerIntegers150 gen)
        where mkBM b = benchDefault (showMemoryUsage b) $
                       mkApp3 IntegerToByteString [] True (0::Integer) b
              name = "IntegerToByteStringTrue0"

benchIntegerToByteStringFalse0 :: StdGen -> Benchmark
benchIntegerToByteStringFalse0 gen =
    bgroup name $ fmap mkBM (smallerIntegers150 gen)
        where mkBM b = benchDefault (showMemoryUsage b) $
                       mkApp3 IntegerToByteString [] False (0::Integer) b
              name = "IntegerToByteStringFalse0"

mkBmW :: String -> Bool -> [Integer] -> [Integer] -> Benchmark
mkBmW name flag xs ys =
    bgroup name $ zipWith (\x y -> bgroup (show x) [mkBM x y]) xs ys
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp3 IntegerToByteString [] flag x y

mkBmW2 :: String -> Bool -> Benchmark
mkBmW2 name flag =
    let widths = fmap (80*) [1..150]
        inputs = fmap (\n -> 256^n - 1) widths
    in mkBmW name flag widths inputs

benchIntegerToByteStringWTrue :: Benchmark
benchIntegerToByteStringWTrue =
    mkBmW2 "IntegerToByteStringWTrue" True

benchIntegerToByteStringWFalse :: Benchmark
benchIntegerToByteStringWFalse =
    mkBmW2 "IntegerToByteStringWFalse" False

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    [ benchByteStringToIntegerFalseSmall
    , benchByteStringToIntegerTrueSmall
    , benchByteStringToIntegerFalseBig
    , benchByteStringToIntegerTrueBig
    , benchIntegerToByteStringBoundedFalseSmall   gen
    , benchIntegerToByteStringBoundedTrueSmall    gen
    , benchIntegerToByteStringBoundedFalseBig     gen
    , benchIntegerToByteStringBoundedTrueBig      gen
    , benchIntegerToByteStringUnboundedFalseSmall gen
    , benchIntegerToByteStringUnboundedTrueSmall  gen
    , benchIntegerToByteStringUnboundedFalseBig   gen
    , benchIntegerToByteStringUnboundedTrueBig    gen
    ]
