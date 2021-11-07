{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes      #-}
module Main where

import Criterion.Main
import Criterion.Main.Options
import Criterion.Types

fix' :: ((a -> b) -> a -> b) -> a -> b
fix' f x = (f $! fix' f) $! x

newtype Fix f = Fix (f (Fix f))

newtype SelfF a r = SelfF
  { unSelfF :: r -> a
  }

type Self a = Fix (SelfF a)

pattern Self f = Fix (SelfF f)

unfold :: Self a -> Self a -> a
unfold (Self f) = f

-- unroll (self {τ} (x.e)) ↦ [self {τ} (x.e) / x] e
unroll :: Self a -> a
unroll s = unfold s s

-- fix {τ} (x. e) = unroll (self {τ} (y. [unroll y / x] e))
bz1 :: ((a -> b) -> a -> b) -> a -> b
bz1 = \f -> unroll . Self $ \s -> f (\x -> unroll s $! x)

-- fix {τ} (x. e) = unroll (self {τ} (y. [unroll y / x] e))
bz2 :: ((a -> b) -> a -> b) -> a -> b
bz2 = \f -> unroll . Self $ \s x -> (f $! unroll s) $! x

z1 :: ((a -> b) -> a -> b) -> a -> b
z1 = \f -> let a = \r -> f (\x -> unroll r $! x) in a (Self a)

z2 :: ((a -> b) -> a -> b) -> a -> b
z2 = \f -> let a = \r x -> (f $! unroll r) $! x in a (Self a)

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

bench_fixed_points
  :: String
  -> ((forall a b. ((a -> b) -> a -> b) -> a -> b) -> Int -> c)
  -> Benchmark
bench_fixed_points name fun = bgroup name $ [10^5, 10^6, 10^7] >>= \n ->
  [ bench ("fix'/" ++ show n) $ whnf (fun fix') n
  , bench ("bz1/"  ++ show n) $ whnf (fun bz1 ) n
  , bench ("bz2/"  ++ show n) $ whnf (fun bz2 ) n
  , bench ("z1/"   ++ show n) $ whnf (fun z1  ) n
  , bench ("z2/"   ++ show n) $ whnf (fun z2  ) n
  ]

bench_countdownBy :: Benchmark
bench_countdownBy = bench_fixed_points "countdownBy" countdownBy

bench_natSumUpToBy :: Benchmark
bench_natSumUpToBy = bench_fixed_points "natSumUpToBy" natSumUpToBy

bench_leakingNatSumUpToBy :: Benchmark
bench_leakingNatSumUpToBy = bench_fixed_points "leakingNatSumUpToBy" leakingNatSumUpToBy

main :: IO ()
main = defaultMain
  [ bench_countdownBy
  , bench_natSumUpToBy
  , bench_leakingNatSumUpToBy
  ]
