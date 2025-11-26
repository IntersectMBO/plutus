{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Criterion.Main
import Data.Semigroup
import System.Random

import Data.Maybe (fromJust)
import Data.Proxy
import Data.RAList qualified as R
import Data.RandomAccessList.Class
import Data.RandomAccessList.RelativizedMap qualified as RM
import Data.RandomAccessList.SkewBinary qualified as B
import Data.RandomAccessList.SkewBinarySlab qualified as BS
import Data.Vector.NonEmpty qualified as NEV
import Data.Word

ralWorkloads :: forall e. (RandomAccessList e, Element e ~ ()) => Proxy e -> [Benchmark]
ralWorkloads _ =
  [ bgroup "cons" $ workloads (consN @e)
  , bgroup "consSlab" $ workloads (consNSlab @e)
  ]
  where
    workloads :: (Word64 -> e -> e) -> [Benchmark]
    workloads creator =
      [ bgroup "create" $ flip fmap [100, 250] $ \sz ->
          bench (show sz) $ whnf (creator sz) empty
      , bgroup "query-front" $ flip fmap [100, 250] $ \sz ->
          bench (show sz) $ whnf (query [0 .. 100]) (creator sz empty)
      , bgroup "query-back" $ flip fmap [100, 250] $ \sz ->
          bench (show sz) $ whnf (query [sz - 100 .. sz]) (creator sz empty)
      , bgroup "query-rand" $ flip fmap [100, 250] $ \sz ->
          let ws = randWords sz
           in bench (show sz) $ whnf (query ws) (creator sz empty)
      , bgroup "create/front100/cons100/back100/cons100/rand" $ flip fmap [100, 250] $ \sz ->
          let qsize = 100
              ws = randWords sz
           in bench (show sz) $ whnf (mix sz qsize qsize qsize qsize ws) (creator sz empty)
      ]

    randWords :: Word64 -> [Word64]
    randWords sz = take (fromIntegral sz) $ randomRs (1, sz - 1) g

    -- note: fixed rand-seed to make benchmarks deterministic
    g = mkStdGen 59950

applyN :: Integral b => b -> (a -> a) -> a -> a
applyN n f = appEndo (stimes n $ Endo f)

-- | Conses on 'n' elements individually.
consN :: (RandomAccessList e, Element e ~ ()) => Word64 -> e -> e
consN n = applyN n (cons ())

-- | Conses on 'n' elements in slabs of size 10.
consNSlab :: (RandomAccessList e, Element e ~ ()) => Word64 -> e -> e
consNSlab n = consNSlabM (n `div` 10) 10

-- | Conses on 'n' slabs of size 'm'
consNSlabM :: (RandomAccessList e, Element e ~ ()) => Word64 -> Word64 -> e -> e
consNSlabM slabNo slabSize = applyN slabNo (consSlab slab)
  where
    slab = fromJust $ NEV.replicate (fromIntegral slabSize) ()
{-# INLINE consNSlabM #-}

-- | Accesses the given indices.
query :: (RandomAccessList e, Element e ~ ()) => [Word64] -> e -> Element e
query [] _ = ()
query (i : is) d = indexZero d i `seq` query is d

-- | A mixed worload.
mix
  :: (RandomAccessList e, Element e ~ ())
  => Word64 -> Word64 -> Word64 -> Word64 -> Word64 -> [Word64] -> e -> Element e
mix sz front cons1 back cons2 rand d =
  query [0 .. front] d `seq`
    let d1 = consN cons1 d
     in query [(sz - back) .. sz] d1 `seq`
          let d2 = consN cons2 d1
           in query rand d2

main :: IO ()
main =
  defaultMain
    [ bgroup "SkewBinary" (ralWorkloads (Proxy :: Proxy (B.RAList ())))
    , bgroup "SkewBinarySlab" (ralWorkloads (Proxy :: Proxy (BS.RAList ())))
    , bgroup "RelativizedMap" (ralWorkloads (Proxy :: Proxy (RM.RelativizedMap ())))
    , bgroup "RAL" (ralWorkloads (Proxy :: Proxy (R.RAList ())))
    ]
