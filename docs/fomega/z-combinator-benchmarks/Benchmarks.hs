module Main where

import Criterion.Main.Options
import Criterion.Main
import Criterion.Types

fix' :: ((a -> b) -> a -> b) -> a -> b
fix' f x = (f $! fix' f) $! x

newtype Rec a = In { out :: Rec a -> a }

z :: ((a -> b) -> a -> b) -> a -> b
z = \f -> let a = \r -> f (\x -> out r r $! x) in a (In a)

countdownBy
  :: (((Int -> Bool) -> Int -> Bool) -> Int -> Bool)
  -> Int -> Bool
countdownBy recurse = recurse $ \r x -> x == 0 || r (x - 1)

natSumUpToBy
  :: (((Int -> Int -> Int) -> Int -> Int -> Int) -> Int -> Int -> Int)
  -> Int -> Int
natSumUpToBy recurse = recurse (\r a x -> if x == 0 then 0 else r (a + x) (x - 1)) 0

leakingNatSumUpToBy
  :: (((Int -> Int) -> Int -> Int) -> Int -> Int)
  -> Int -> Int
leakingNatSumUpToBy recurse = recurse $ \r x -> if x == 0 then 0 else x + r (x - 1)

----------------
-- Benchmarks --
----------------

countdownBy_fix'_z :: Benchmark
countdownBy_fix'_z = bgroup "countdownBy" $ [10^5, 10^6, 10^7] >>= \n ->
  [ bench ("fix'/" ++ show n) $ whnf (countdownBy fix') n
  , bench ("z/"    ++ show n) $ whnf (countdownBy z   ) n
  ]

natSumUpToBy_fix'_z :: Benchmark
natSumUpToBy_fix'_z = bgroup "natSumUpToBy" $ [10^5, 10^6, 10^7] >>= \n ->
  [ bench ("fix'/" ++ show n) $ whnf (natSumUpToBy fix') n
  , bench ("z/"    ++ show n) $ whnf (natSumUpToBy z   ) n
  ]

leakingNatSumUpToBy_fix'_z :: Benchmark
leakingNatSumUpToBy_fix'_z = bgroup "leakingNatSumUpToBy" $ [10^5, 10^6, 10^7] >>= \n ->
  [ bench ("fix'/" ++ show n) $ whnf (leakingNatSumUpToBy fix') n
  , bench ("z/"    ++ show n) $ whnf (leakingNatSumUpToBy z   ) n
  ]

main :: IO ()
main = defaultMain
  [ countdownBy_fix'_z
  , natSumUpToBy_fix'_z
  , leakingNatSumUpToBy_fix'_z
  ]
