{- | Conformance tests for the Haskell implementation. -}

module Main (main) where

import PlutusConformance.Common

failingTests :: [FilePath]
failingTests = []

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalUplcProg (\dir -> elem dir failingTests)
