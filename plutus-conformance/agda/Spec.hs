{- | Conformance tests for the Agda implementation. -}

module Main (main) where

import MAlonzo.Code.Main (runUAgda)
import PlutusConformance.Common (agdaEvalUplcProg, runUplcEvalTests)

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg

