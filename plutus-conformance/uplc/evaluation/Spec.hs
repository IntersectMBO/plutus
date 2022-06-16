{- | Conformance tests of Untyped Plutus Core program evaluation. -}

module Main (main) where

import PlutusConformance.Common (evalUplcProg, runUplcEvalTests)
import Prelude hiding (readFile)

main :: IO ()
main = runUplcEvalTests evalUplcProg

