{- | Conformance tests for the Agda implementation. -}

module Main (main) where

import MAlonzo.Code.Main (runUAgda)
import PlutusConformance.Common

-- | Our `evaluator` for the Agda UPLC tests is the CEK machine.
agdaEvalUplcProg :: UplcProg -> Maybe UplcProg
agdaEvalUplcProg p =
    case runUAgda (mkTerm p) of
        Left _  -> Nothing
        Right p -> Just p

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg

