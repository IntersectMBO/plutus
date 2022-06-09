{- | Conformance tests of Untyped Plutus Core program evaluation. -}

module Main (main) where

import Common (evalUplcProg, runTests)
import Prelude hiding (readFile)

main :: IO ()
main = runTests evalUplcProg

