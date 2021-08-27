module Benchmarks.Lists (makeBenchmarks) where

import           Benchmarks.Common
import           PlutusCore

import           Criterion.Main
import           Data.ByteString   (ByteString)
import qualified Hedgehog          as H
import           System.Random     (StdGen)



{- Some functions for generating lists of sizes integers/bytestrings The time
   behaviour of the list functions should be independent of the size of the
   arguments (and in fact constant), but we benchmark them with both integer
   and bytestring lists for confirmation. -}

makeListOfSizedIntegers :: StdGen -> Int -> Int -> ([Integer], StdGen)
makeListOfSizedIntegers gen count size = makeSizedIntegers gen (take count $ repeat size)

makeListOfIntegerLists :: StdGen -> [(Int, Int)] -> [[Integer]]
makeListOfIntegerLists  _ [] = []
makeListOfIntegerLists  gen ((count, size):rest) =
    let (l, gen') = makeListOfSizedIntegers gen count size
    in l:(makeListOfIntegerLists gen' rest)

makeListOfSizedBytestrings :: H.Seed -> Int -> Int -> [ByteString]
makeListOfSizedBytestrings seed count size = makeSizedByteStrings seed (take count $ repeat size)

makeListOfByteStringLists :: H.Seed -> [(Int, Int)] -> [[ByteString]]
makeListOfByteStringLists  _ [] = []
makeListOfByteStringLists seed ((count, size):rest) =
    let l = makeListOfSizedBytestrings seed count size
    in l:(makeListOfByteStringLists seed rest)
-- Don't like reusing the seed here.

intLists :: StdGen -> [[Integer]]
intLists gen = makeListOfIntegerLists gen [(count,size) | count <- [0..7], size <- [1..7]]

nonEmptyIntLists :: StdGen -> [[Integer]]
nonEmptyIntLists gen = makeListOfIntegerLists gen [(count,size) | count <- [1..7], size <- [1..7]]

byteStringLists :: H.Seed -> [[ByteString]]
byteStringLists seed = makeListOfByteStringLists seed [(count,size) | count <- [0..7], size <- [0, 500..3000]]

nonEmptyByteStringLists :: H.Seed -> [[ByteString]]
nonEmptyByteStringLists seed = makeListOfByteStringLists seed [(count,size) | count <- [1..7], size <- [0, 500..3000]]


-- nullList tests if a list is empty
benchNullList :: StdGen -> Benchmark
benchNullList gen =
    bgroup (show name) $ fmap (mkBM integer) (intLists gen)
                      ++ fmap (mkBM bytestring) (byteStringLists seedA)
        where mkBM ty x = benchDefault (showMemoryUsage x) $ mkApp1 name [ty] x
              name = NullList

benchNonEmptyList :: StdGen -> DefaultFun -> Benchmark
benchNonEmptyList gen name =
    bgroup (show name) $ fmap (mkBM integer) (nonEmptyIntLists gen)
                      ++ fmap (mkBM bytestring) (nonEmptyByteStringLists seedA)
        where mkBM ty x = benchDefault (showMemoryUsage x) $ mkApp1 name [ty] x


benchMkCons :: StdGen -> Benchmark
benchMkCons gen =
    let name = ConsByteString
        intInputs = intLists gen
        (intsToCons, _) = makeSizedIntegers gen $ take (length intInputs) (cycle [1,2,4,10,15])
        bsInputs = byteStringLists seedA
        bssToCons = makeSizedByteStrings seedA $ take (length bsInputs) (cycle [5,80,500, 1000, 5000])
    in  bgroup (show name) $ fmap (mkBM name integer) (zip intsToCons intInputs)
                           ++ fmap (mkBM name bytestring) (zip bssToCons bsInputs)
          where mkBM name ty (x,xs) = benchDefault (showMemoryUsage x) $ mkApp2 name [ty] x xs


-- chooseList l a b = case l of [] -> a | _ -> b
-- This is presumably constant time, but we should check.  Let's look at a
-- subset of the sample lists and give each one several choices of bytestring
-- results of different sizes.
benchChooseList :: StdGen -> Benchmark
benchChooseList gen =
    let name = ChooseList
        resultSizes = [100, 500, 1500, 3000, 5000]
        results1 = makeSizedByteStrings seedA resultSizes
        results2 = makeSizedByteStrings seedB resultSizes
        intInputs = take 10 $ intLists gen
        bsInputs  = take 10 $ byteStringLists seedA
        mkBMs ty inputs = [ bgroup (showMemoryUsage x)
                           [ bgroup (showMemoryUsage r1)
                            [ benchDefault (showMemoryUsage r2) $ mkApp3 name [ty] x r1 r2
                            | r2 <- results2 ]
                           | r1 <- results1 ]
                          | x <- inputs ]
    in bgroup (show name) (mkBMs integer intInputs ++ mkBMs bytestring bsInputs)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ benchNullList gen,
                       benchNonEmptyList gen HeadList,
                       benchNonEmptyList gen TailList,
                       benchMkCons gen,
                       benchChooseList gen
                     ]
