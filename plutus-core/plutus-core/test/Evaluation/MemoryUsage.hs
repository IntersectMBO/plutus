{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.MemoryUsage (test_memoryUsage) where

import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Unroll (dropN)

import Control.Monad (forM_)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

test_memoryUsage :: TestTree
test_memoryUsage =
  testGroup
    "memory usage"
    [ testGroup
        "dropN"
        [ testCase "zero drops do not inspect the list" $
            case dropN @0 (undefined :: [Int]) of
              Just _ -> pure ()
              Nothing -> assertFailure "Zero drops must succeed"
        , testCase "short, exact and longer lists" $ do
            dropN @3 ([] :: [Int]) @?= Nothing
            dropN @3 [1 :: Int] @?= Nothing
            dropN @3 [1 :: Int, 2] @?= Nothing
            dropN @3 [1 :: Int, 2, 3] @?= Just []
            dropN @3 [1 :: Int, 2, 3, 4] @?= Just [4]
        , testCase "all shortfalls in a batch" $
            forM_ [0 .. 201] $ \n ->
              dropN @100 [1 .. n :: Int]
                @?= if n < 100 then Nothing else Just [101 .. n]
        , testCase "dropped elements and remaining spine stay lazy" $
            case dropN @3 (replicate 3 undefined ++ undefined :: [Int]) of
              Just _ -> pure ()
              Nothing -> assertFailure "Three drops must succeed"
        ]
    , testGroup
        "list batches"
        [ testCase "cost chunks at and between batch boundaries" $
            forM_ [0 .. 301] $ \n ->
              listCosts (memoryUsage (replicate n undefined :: [Int]))
                @?= replicate (n `div` 100) 100 ++ [fromIntegral (n `mod` 100)]
        , testCase "the first batch does not force the remaining spine" $
            case memoryUsage (replicate 100 undefined ++ undefined :: [Int]) of
              CostRose cost _ -> cost @?= 100
        , testCase "infinite lists produce costs incrementally" $
            take 3 (listCosts (memoryUsage (repeat undefined :: [Int]))) @?= [100, 100, 100]
        ]
    ]
  where
    listCosts (CostRose cost children) = cost : concatMap listCosts children
