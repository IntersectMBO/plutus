{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Benchmarks.Lists (makeBenchmarks) where

import Common
import Generators

import PlutusCore
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn, mkIterInstNoAnn)

import Control.DeepSeq (force)
import Criterion.Main
import Data.ByteString (ByteString)
import Debug.Trace (trace)
import Hedgehog qualified as H
import PlutusCore.Evaluation.Machine.ExMemoryUsage (IntegerCostedLiterally (..),
                                                    ListCostedByLength (..))
import PlutusCore.Pretty qualified as PP
import System.Random (StdGen, randomR)

{- Some functions for generating lists of sizes integers/bytestrings The time
   behaviour of the list functions should be independent of the sizes and types
   of the arguments (and in fact constant), but we benchmark them with both
   integer and bytestring lists for confirmation. -}

makeListOfSizedIntegers :: StdGen -> Int -> Int -> ([Integer], StdGen)
makeListOfSizedIntegers gen count size =
    makeSizedIntegers gen (take count $ repeat size)

makeListOfIntegerLists :: StdGen -> [(Int, Int)] -> [[Integer]]
makeListOfIntegerLists  _ [] = []
makeListOfIntegerLists  gen ((count, size):rest) =
    let (l, gen') = makeListOfSizedIntegers gen count size
    in l:(makeListOfIntegerLists gen' rest)

makeListOfSizedBytestrings :: H.Seed -> Int -> Int -> [ByteString]
makeListOfSizedBytestrings seed count size =
    makeSizedByteStrings seed (take count $ repeat size)

makeListOfByteStringLists :: H.Seed -> [(Int, Int)] -> [[ByteString]]
makeListOfByteStringLists  _ [] = []
makeListOfByteStringLists seed ((count, size):rest) =
    let l = makeListOfSizedBytestrings seed count size
    in l:makeListOfByteStringLists seed rest
-- Don't like reusing the seed here.

intLists :: StdGen -> [[Integer]]
intLists gen = makeListOfIntegerLists gen [(count,size) | count <- [0..7], size <- [1..7]]

-- Make a list of n integers whose value is less than or equal to m
intMaxList :: Integer -> Integer -> StdGen -> [Integer]
intMaxList 0 _ _ = []
intMaxList n m gen = (v : (intMaxList (n-1) m g2))
  where (v , g2) = randomR ((0::Integer),m) gen

nonEmptyIntLists :: StdGen -> [[Integer]]
nonEmptyIntLists gen = makeListOfIntegerLists gen [(count,size) | count <- [1..7], size <- [1..7]]

byteStringLists :: H.Seed -> [[ByteString]]
byteStringLists seed =
    makeListOfByteStringLists seed [(count,size) | count <- [0..7], size <- [0, 500..3000]]

nonEmptyByteStringLists :: H.Seed -> [[ByteString]]
nonEmptyByteStringLists seed =
    makeListOfByteStringLists seed [(count,size) | count <- [1..7], size <- [0, 500..3000]]

-- chooseList l a b = case l of [] -> a | _ -> b
-- We expect this to be constant time, but check anyway.  We look at a subset of
-- the sample lists and give each one several choices of bytestring results of
-- different sizes.
benchChooseList :: StdGen -> Benchmark
benchChooseList gen =
    let name = ChooseList
        resultSizes = [100, 500, 1500, 3000, 5000]
        results1 = makeSizedByteStrings seedA resultSizes
        results2 = makeSizedByteStrings seedB resultSizes
        intInputs = take 10 $ intLists gen
        bsInputs  = take 10 $ byteStringLists seedA
        mkBMs tys inputs = [ bgroup (showMemoryUsage x)
                             [ bgroup (showMemoryUsage r1)
                               [ benchDefault (showMemoryUsage r2) $ mkApp3 name tys x r1 r2
                               | r2 <- results2 ]
                             | r1 <- results1 ]
                           | x <- inputs ]
    in bgroup (show name) (mkBMs [integer,bytestring] intInputs
                            ++ mkBMs [bytestring,bytestring] bsInputs)

benchMkCons :: StdGen -> Benchmark
benchMkCons gen =
    let name = MkCons
        intInputs = intLists gen
        (intsToCons, _) = makeSizedIntegers gen $ take (length intInputs) (cycle [1,2,4,10,15])
        bsInputs = byteStringLists seedA
        bssToCons =
            makeSizedByteStrings seedA $ take (length bsInputs) (cycle [5,80,500, 1000, 5000])
        mkBM ty (x,xs) = benchDefault (showMemoryUsage x) $ mkApp2 name [ty] x xs
    in  bgroup (show name) $ fmap (mkBM integer) (zip intsToCons intInputs)
                           ++ fmap (mkBM bytestring) (zip bssToCons bsInputs)

-- For headList and tailList
benchNonEmptyList :: StdGen -> DefaultFun -> Benchmark
benchNonEmptyList gen name =
    bgroup (show name) $ fmap (mkBM integer) (nonEmptyIntLists gen)
                      ++ fmap (mkBM bytestring) (nonEmptyByteStringLists seedA)
                          where mkBM ty x = benchDefault (showMemoryUsage x) $ mkApp1 name [ty] x

-- nullList tests if a list is empty
benchNullList :: StdGen -> Benchmark
benchNullList gen =
    bgroup (show name) $ fmap (mkBM integer) (intLists gen)
                      ++ fmap (mkBM bytestring) (byteStringLists seedA)
        where mkBM ty x = benchDefault (showMemoryUsage x) $ mkApp1 name [ty] x
              name = NullList

-- dropList n ls
-- We expect this to be linear with the value of n.
benchDropList :: StdGen -> Benchmark
benchDropList gen =
    let name = DropList
        resultSizes = [100, 500, 1500, 3000, 5000]
        -- Produce lists of sz items, each of sz length
        stringlists = makeListOfByteStringLists seedA [ (sz , sz) | sz <- resultSizes ]
        intInputs = [ intMaxList 10 (toInteger sz) gen | sz <- resultSizes ]
        inputs = concat [[(n , rs) | n <- ns] | (ns, rs) <- zip intInputs stringlists]
    in createTwoTermBuiltinBenchElementwiseWithWrappers
           (IntegerCostedLiterally, id) name [bytestring] inputs

benchCaseList :: StdGen -> Benchmark
benchCaseList gen =
    let name = CaseList
        y = Name "y" (Unique 1)
        ys = Name "ys" (Unique 2)
        -- lam y (con unit ())
        mkCase1 ty = LamAbs () y ty (mkConstant () ())
        -- lam y (lam ys (con unit ()))
        mkCase2 ty = LamAbs () y ty (LamAbs () ys (list ty) (mkConstant () ()))
        -- Two different types of inputs, just to make sure there's no difference
        intInputs = take 100 $ intLists gen          -- Make these bigger
        bsInputs  = take 100 $ byteStringLists seedA -- Make these bigger
        mkApp3' !fun !tys term1 term2 (force -> !l) =
          eraseTerm $ mkIterAppNoAnn instantiated [term1, term2, mkConstant () l]
          where instantiated = mkIterInstNoAnn (builtin () fun) tys

        mkBMs ty inputs =
          let case1 = mkCase1 ty
              case2 = mkCase2 ty
          in [ bgroup "1"
               [ bgroup "1"
                 [ benchDefault
                   (showMemoryUsage $ ListCostedByLength l)
                   (mkApp3' name [ty, unit] case1 case2 l)
                 ]
               ]
             | l <- inputs ]
        test :: PlainTerm DefaultUni DefaultFun
        test = mkApp3' name [integer, unit]
               (mkCase1 integer)
               (mkCase2 integer)
               [1,2,3,4,5,6,7,8,9::Integer]
    in trace (show $ PP.prettyPlcClassic test) $
       bgroup (show name) (mkBMs integer intInputs ++ mkBMs bytestring bsInputs)

  -- benchmark caseList (con unit ()) (lam x (lam y (con unit ()))) l

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ benchChooseList gen
                     , benchMkCons gen
                     , benchNonEmptyList gen HeadList
                     , benchNonEmptyList gen TailList
                     , benchNullList gen
                     , benchDropList gen
                     , benchCaseList gen
                     ]
