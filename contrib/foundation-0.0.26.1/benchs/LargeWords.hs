{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module LargeWords where

import Foundation
import Basement.From
import Basement.Types.Word128 (Word128)
import Basement.Types.Word256 (Word256)
import qualified Basement.Types.Word128 as Word128
import qualified Basement.Types.Word256 as Word256
import BenchUtil.Common

largeNumber64 :: Natural
largeNumber64 = 0xffffffffffffffff

largeNumber128 :: Natural
largeNumber128 = 0xfffffffffffffffffffffffffffffff

largeNumber256 :: Natural
largeNumber256 = 0xffffffffffffffffffffffffffffffffffffffffffffffff

benchLargeWords =
    [ bgroup "Addition"
        [ bgroup "Word128"
            [ bench "Word128" $ whnf (+ 1240) (Word128.fromNatural largeNumber128)
            , bench "Natural" $ whnf (+ 1240) largeNumber128
            ]
        , bgroup "Word256"
            [ bench "Word256" $ whnf (+ 200) (Word256.fromNatural largeNumber256)
            , bench "Natural" $ whnf (+ 200) largeNumber256
            ]
        ]
    , bgroup "Multiplication"
        [ bgroup "Word128"
            [ bench "Word128" $ whnf (* 1240) (Word128.fromNatural largeNumber128)
            , bench "Natural" $ whnf (* 1240) largeNumber128
            ]
        , bgroup "Word256"
            [ bench "Word256" $ whnf (* 200) (Word256.fromNatural largeNumber256)
            , bench "Natural" $ whnf (* 200) largeNumber256
            ]
        ]
    ]
