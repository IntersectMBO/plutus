module Main (main) where

import           Criterion.Main

benchAdd :: Integer -> Benchmark
benchAdd = benchOp (+)

benchMul :: Integer -> Benchmark
benchMul = benchOp (*)

-- FIXME: this doesn't do anything
benchOp :: (Integer -> Integer -> Integer) -> Integer -> Benchmark
benchOp op n = bench (show n) $ nf (`op` n) n

main :: IO ()
main =
    defaultMain [ bgroup "Integer Addition" $
                      benchAdd <$> [ 10000
                                   , 10000000000000000000000
                                   ]
                , bgroup "Integer Multiplication" $
                      benchMul <$> [ 1000
                                   , 10000000000000000000000
                                   ]
                ]
