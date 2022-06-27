{- | Conformance tests for the Haskell implementation. -}

module Main (main) where

import PlutusConformance.Common

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalUplcProg

