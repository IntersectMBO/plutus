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
smallerByteStrings150 seed = makeSizedByteStrings seed [1..150]

-- Arguments for two-argument benchmarks: 21 entries.
-- Note that the length is eight times the size.
largerByteStrings21 :: H.Seed -> [BS.ByteString]
largerByteStrings21 seed = makeSizedByteStrings seed $ fmap (250*) [0..20]

largerByteStrings150 :: H.Seed -> [BS.ByteString]
largerByteStrings150 seed = makeSizedByteStrings seed $ fmap (10*) [1..150]

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
benchByteStringToIntegerFalseSmall = createTwoTermBuiltinBench' ByteStringToInteger "FalseSmall" [] [False] (smallerByteStrings150 seedA)

benchByteStringToIntegerTrueSmall :: Benchmark
benchByteStringToIntegerTrueSmall =  createTwoTermBuiltinBench' ByteStringToInteger "TrueSmall" [] [True] (smallerByteStrings150 seedA)

benchByteStringToIntegerFalseBig :: Benchmark
benchByteStringToIntegerFalseBig =   createTwoTermBuiltinBench' ByteStringToInteger "FalseBig" [] [False] (largerByteStrings150 seedA)

benchByteStringToIntegerTrueBig :: Benchmark
benchByteStringToIntegerTrueBig =    createTwoTermBuiltinBench' ByteStringToInteger "TrueBig" [] [True] (largerByteStrings150 seedA)

------------------------- IntegerToByteString -------------------------

smallWidths :: [Int]
smallWidths = [1..150]

bigWidths :: [Int]
bigWidths = fmap (10*) [1..150]

-- Make an integer 0xFF...FF of size n.
allFF :: Int -> Integer
allFF n = 256^(8*n) - 1

-- Fixed width, small inputs.
-- Width = 1-150 ExMemory (8 times that in bytes)
-- input = random integer 'width'-bytes integer
benchIntegerToByteStringBoundedFalseSmall :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseSmall gen =
    let widths = smallWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseSmall" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueSmall :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueSmall gen =
    let widths = smallWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueSmall" $ zip3 (repeat True) widths inputs

benchIntegerToByteStringBoundedFalseSmallFF :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseSmallFF _gen =
    let widths = smallWidths
        inputs = fmap allFF widths
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseSmallFF" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueSmallFF :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueSmallFF _gen =
    let widths = smallWidths
        inputs = fmap allFF widths
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueSmallFF" $ zip3 (repeat True) widths inputs

-- Fixed width, big inputs.
benchIntegerToByteStringBoundedFalseBig :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseBig gen =
    let widths = bigWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseBig" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueBig :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueBig gen =
    let widths = bigWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueBig" $ zip3 (repeat True) widths inputs

-- Very small inputs but big widths.
benchIntegerToByteStringBoundedFalseBig2 :: StdGen -> Benchmark
benchIntegerToByteStringBoundedFalseBig2 _gen =
    let widths = bigWidths
        inputs = take (length widths) $ repeat (189 :: Integer)
    in createThreeTermBuiltinBenchElementwise' "BoundedFalseBig2" $ zip3 (repeat False) widths inputs

benchIntegerToByteStringBoundedTrueBig2 :: StdGen -> Benchmark
benchIntegerToByteStringBoundedTrueBig2 _gen =
    let widths = bigWidths
        inputs = take (length widths) $ repeat (189 :: Integer)
    in createThreeTermBuiltinBenchElementwise' "BoundedTrueBig2" $ zip3 (repeat True) widths inputs

-- Flexible width, small inputs
benchIntegerToByteStringUnboundedFalseSmall :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedFalseSmall gen =
    let widths = smallWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedFalseSmall" $ zip3 (repeat False) (repeat 0) inputs

benchIntegerToByteStringUnboundedTrueSmall :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedTrueSmall gen =
    let widths = smallWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedTrueSmall" $ zip3 (repeat True) (repeat 0) inputs

-- Flexible width, small inputs
benchIntegerToByteStringUnboundedFalseSmallFF :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedFalseSmallFF _gen =
    let widths = smallWidths
        inputs = fmap allFF widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedFalseSmallFF" $ zip3 (repeat False) (repeat 0) inputs

benchIntegerToByteStringUnboundedTrueSmallFF :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedTrueSmallFF _gen =
    let widths = smallWidths
        inputs = fmap allFF widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedTrueSmallFF" $ zip3 (repeat True) (repeat 0) inputs

-- Flexible width, big inputs
benchIntegerToByteStringUnboundedFalseBig :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedFalseBig gen =
    let widths = bigWidths
        (inputs, _) = makeSizedIntegers gen widths
    in createThreeTermBuiltinBenchElementwise' "UnboundedFalseBig" $ zip3 (repeat False) (repeat 0) inputs

benchIntegerToByteStringUnboundedTrueBig :: StdGen -> Benchmark
benchIntegerToByteStringUnboundedTrueBig gen =
    let widths = bigWidths
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
{-    , benchIntegerToByteStringBoundedFalseSmall   gen
    , benchIntegerToByteStringBoundedTrueSmall    gen
    , benchIntegerToByteStringBoundedFalseSmallFF gen
    , benchIntegerToByteStringBoundedTrueSmallFF  gen
    , benchIntegerToByteStringBoundedFalseBig     gen
    , benchIntegerToByteStringBoundedTrueBig      gen
    , benchIntegerToByteStringBoundedFalseBig2    gen
    , benchIntegerToByteStringBoundedTrueBig2     gen
    , benchIntegerToByteStringUnboundedFalseSmall gen
    , benchIntegerToByteStringUnboundedTrueSmall  gen
    , benchIntegerToByteStringUnboundedFalseSmallFF gen
    , benchIntegerToByteStringUnboundedTrueSmallFF  gen
    , benchIntegerToByteStringUnboundedFalseBig   gen
    , benchIntegerToByteStringUnboundedTrueBig    gen
-}
    ]
