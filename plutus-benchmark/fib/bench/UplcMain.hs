module Main (main) where

import Control.Exception (evaluate)
import Criterion.Main
import Plinth
import PlutusBenchmark.Common
import PlutusCore.Pretty
import PlutusTx.Code

main :: IO ()
main = do
  putStrLn "===============FIB UPLC==============="
  putStrLn . render . prettyReadableSimple $ getPlcNoAnn fibCompiled
  putStrLn "===============END FIB UPLC==============="
  evalCtx <- evaluate mkMostRecentEvalCtx
  let benchFib :: Integer -> Benchmarkable
      benchFib = benchProgramCek evalCtx . fibK
  defaultMain
    [ bgroup
        "fib"
        [ bench "15" (benchFib 15)
        , bench "20" (benchFib 20)
        , bench "25" (benchFib 25)
        , bench "29" (benchFib 29)
        , bench "31" (benchFib 31)
        , bench "33" (benchFib 33)
        ]
    ]
