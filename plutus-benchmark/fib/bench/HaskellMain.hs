module Main (main) where

import Control.Exception (evaluate)
import Criterion.Main
import Plinth
import PlutusBenchmark.Common

main :: IO ()
main =
  defaultMain
    [ bgroup
        "fib"
        [ bench "15" $ whnf fib 15
        , bench "20" $ whnf fib 20
        , bench "25" $ whnf fib 25
        , bench "29" $ whnf fib 29
        , bench "31" $ whnf fib 31
        , bench "33" $ whnf fib 33
        ]
    ]
