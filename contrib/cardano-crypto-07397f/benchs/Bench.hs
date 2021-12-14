{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import           Gauge
import           Gauge.Main

import           Crypto.Random
import           Cardano.Crypto.Wallet
import           Data.ByteArray (Bytes)
import qualified Data.ByteArray as B

hardIdx, softIdx :: DerivationIndex
hardIdx = 0x80000001
softIdx = 0x00000001

derivePass :: Bytes
derivePass = B.pack [10..30]

noDerivePass :: Bytes
noDerivePass = B.empty

doDeriveBench dscheme pass parent =
    [ bench "derive-hard" $ nf (\p -> deriveXPrv dscheme pass p hardIdx) parent
    , bench "derive-soft" $ nf (\p -> deriveXPrv dscheme pass p softIdx) parent
    ]

main = do
    seed <- getRandomBytes 32 :: IO Bytes
    let !parentPass   = generate seed derivePass
        !parentNoPass = generate seed noDerivePass

    defaultMain
        [ bgroup "derivation-v1-nopass" $ doDeriveBench DerivationScheme1 noDerivePass parentNoPass
        , bgroup "derivation-v2-nopass" $ doDeriveBench DerivationScheme2 noDerivePass parentNoPass
        , bgroup "derivation-v1-pass" $ doDeriveBench DerivationScheme1 derivePass parentPass
        , bgroup "derivation-v2-pass" $ doDeriveBench DerivationScheme2 derivePass parentPass
        ]
