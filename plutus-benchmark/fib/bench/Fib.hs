module Main (main) where

import Control.Exception (evaluate)
import Criterion.Main
import Plinth
import PlutusBenchmark.Common

main :: IO ()
main = defaultMain [
  bgroup "fib" [
               bench "25"  $ whnf fib 25
               , bench "29"  $ whnf fib 29
               , bench "31" $ whnf fib 31
            --    , bench "15"  $ whnf fib 15
               , bench "20"  $ whnf fib 20
               ]
  ]

-- main :: IO ()
-- main = do
--     evalCtx <- evaluate mkMostRecentEvalCtx
--     let b25 = benchProgramCek evalCtx fib25
--         b29 = benchProgramCek evalCtx fib29
--         b31 = benchProgramCek evalCtx fib31
--         b35 = benchProgramCek evalCtx fib35
--         b20 = benchProgramCek evalCtx fib20
--     defaultMain [
--         bgroup "fib" [ bench "25" b25
--                     , bench "29"  $ b29
--                     , bench "31" $ b31
--                     , bench "35" $ b35
--                     , bench "20" b20
--                 ]
--         ]
