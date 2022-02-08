{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module Main where

import Criterion.Main
import Data.Semigroup
import System.Random

import Data.DeBruijnEnv
import Data.DeBruijnEnv qualified as DBE
import Data.RAList qualified as R
import Data.RandomAccessList.SkewBinary qualified as B
import Data.Word

main :: IO ()
main = defaultMain
    -- NOTE: there is a faster/better way to create a map using fromAscList
    -- but we want to bench cons-ing because that is what we are using in our machine.
    [ bgroup "create" $ flip fmap [100, 250] $ \sz ->
            bgroup (show sz) [ bench "bral" $ whnf (ext @(B.RAList ())) sz
                             , bench "ral" $ whnf (ext @(R.RAList ())) sz
                             , bench "rmap" $ whnf (ext @(DBE.RelativizedMap ())) sz
                             ]

    , bgroup "query/front" $ flip fmap [100, 250] $ \sz ->
            bgroup (show sz) [ bench "bral" $ whnf (queryFront sz) (ext @(B.RAList ()) sz)
                             , bench "ral" $ whnf (queryFront sz) (ext @(R.RAList ()) sz)
                             , bench "rmap" $ whnf (queryFront sz) (ext @(DBE.RelativizedMap ()) sz)
                             ]

    , bgroup "query/back" $ flip fmap [100, 250] $ \sz ->
            bgroup (show sz) [ bench "bral" $ whnf (queryBack sz) (ext @(B.RAList ()) sz)
                             , bench "ral" $ whnf (queryBack sz) (ext @(R.RAList ()) sz)
                             , bench "rmap" $ whnf (queryBack sz) (ext @(DBE.RelativizedMap ()) sz)
                             ]

    , bgroup "query/rand" $ flip fmap [100, 250] $ \sz ->
            bgroup (show sz) [ bench "bral" $ whnf (uncurry queryRand) (randWords sz, ext @(B.RAList ()) sz)
                             , bench "ral" $ whnf (uncurry queryRand) (randWords sz, ext @(R.RAList ()) sz)
                             , bench "rmap" $ whnf (uncurry queryRand) (randWords sz, ext @(DBE.RelativizedMap ()) sz)
                             ]

    , bgroup "create/front100/cons100/back100/cons100/rand" $ flip fmap [100, 250] $ \sz ->
            let qsize = 100
            in bgroup (show sz) [ bench "bral" $ whnf (uncurry $ mix qsize qsize qsize qsize) (randWords sz, ext @(B.RAList ()) sz)
                                , bench "ral" $ whnf (uncurry $ mix qsize qsize qsize qsize) (randWords sz, ext @(B.RAList ()) sz)
                                , bench "rmap" $ whnf (uncurry $ mix qsize qsize qsize qsize) (randWords sz, ext @(DBE.RelativizedMap ()) sz)
                                ]

    ]
  where
        ext :: (DeBruijnEnv e, Element e ~ ()) => Word64 -> e
        ext = extend empty

        randWords :: Word64 -> [Word64]
        randWords sz = take (fromIntegral sz) $ randomRs (1, sz-1) g

        -- note: fixed rand-seed to make benchmarks deterministic
        g = mkStdGen 59950

applyN :: Integral b => (a -> a) -> a -> b -> a
applyN f start n = appEndo (stimes n $ Endo f) start

extend :: (DeBruijnEnv e, Element e ~ ()) => e -> Word64 -> e
extend = applyN $ cons ()

queryFront :: (DeBruijnEnv e, Element e ~ ()) => Word64 -> e -> Element e
queryFront 0 _ = ()
queryFront !i d = index d i' `seq` queryFront i' d
  where i' = i-1

queryBack :: (DeBruijnEnv e, Element e ~ ()) => Word64 -> e -> Element e
queryBack size = go 0
 where
   go !i d | i == size = ()
           | otherwise = index d i `seq` go (i+1) d

queryRand :: (DeBruijnEnv e, Element e ~ ()) => [Word64] -> e -> Element e
queryRand [] _     = ()
queryRand (i:is) d = index d i `seq` queryRand is d

mix :: (DeBruijnEnv e, Element e ~ ()) => Word64 -> Word64 -> Word64 -> Word64 -> [Word64] -> e -> Element e
mix front cons1 back cons2 rand d =
    queryFront front d
    `seq`
    let d1 = extend d cons1
    in queryBack back d1
    `seq`
    let d2 = extend d1 cons2
    in queryRand rand d2
