{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
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

ralWorkloads :: forall e . (RandomAccessList e, Element e ~ ()) => Proxy e -> [Benchmark]
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
                        bench (show sz) $ whnf (queryUpTo 100) (creator sz empty)
            , bgroup "query-back" $ flip fmap [100, 250] $ \sz ->
                        bench (show sz) $ whnf (queryFrom (sz - 100)) (creator sz empty)
            , bgroup "query-rand" $ flip fmap [100, 250] $ \sz ->
                    let ws = randWords sz
                    in bench (show sz) $ whnf (queryListed ws) (creator sz empty)
            , bgroup "create/front100/cons100/back100/cons100/rand" $ flip fmap [100, 250] $ \sz ->
                    let qsize = 100
                        ws = randWords sz
                    in bench (show sz) $ whnf (mix sz qsize qsize qsize qsize ws) (creator sz empty)
            ]

        randWords :: Word64 -> [Word64]
        randWords sz = take (fromIntegral sz) $ randomRs (1, sz-1) g

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

{-# INLINE consNSlabM #-}
-- | Conses on 'n' slabs of size 'm'
consNSlabM :: (RandomAccessList e, Element e ~ ()) => Word64 -> Word64 -> e -> e
consNSlabM slabNo slabSize = applyN slabNo (consSlab slab)
   where slab = fromJust $ NEV.replicate (fromIntegral slabSize) ()

-- | Accesses all indices from i down to 0.
queryUpTo :: (RandomAccessList e) => Word64 -> e -> ()
queryUpTo 0 _ = ()
queryUpTo !i d = indexZero d i' `seq` queryUpTo i' d
    where i' = i-1

-- | Accesses all indices from i up to the maximum.
queryFrom :: (RandomAccessList e) => Word64 -> e -> ()
queryFrom = go
    where go !i d = case indexZero d i of
            Just _  -> go (i+1) d
            Nothing -> ()

-- | Accesses the given indices.
queryListed :: (RandomAccessList e, Element e ~ ()) => [Word64] -> e -> Element e
queryListed [] _     = ()
queryListed (i:is) d = indexZero d i `seq` queryListed is d

-- | A mixed worload.
mix :: (RandomAccessList e, Element e ~ ()) => Word64 -> Word64 -> Word64 -> Word64 -> Word64 -> [Word64] -> e -> Element e
mix sz front cons1 back cons2 rand d =
    queryUpTo front d
    `seq`
    let d1 = consN cons1 d
    in queryFrom (sz - back) d1
    `seq`
    let d2 = consN cons2 d1
    in queryListed rand d2

main :: IO ()
main = defaultMain
    [ bgroup "SkewBinary" (ralWorkloads (Proxy :: Proxy (B.RAList ())))
    , bgroup "SkewBinarySlab" (ralWorkloads (Proxy :: Proxy (BS.RAList ())))
    , bgroup "RelativizedMap" (ralWorkloads (Proxy :: Proxy (RM.RelativizedMap ())))
    , bgroup "RAL" (ralWorkloads (Proxy :: Proxy (R.RAList ())))
    ]
