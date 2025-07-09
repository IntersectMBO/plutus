module Main (main) where

import CardanoLoans.Test (validatorCodeFullyApplied)
import Data.Text qualified as Text
import PlutusTx.Test (displayEvalResult, evaluateCompiledCode)

main :: IO ()
main = do
  putStrLn ""
  putStrLn $
    Text.unpack $
      displayEvalResult $
        evaluateCompiledCode validatorCodeFullyApplied
