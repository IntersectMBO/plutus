module Main (main) where

import Data.Text qualified as Text
import LinearVesting.TestOptimized (validatorOptimizedCodeFullyApplied)
import PlutusTx.Test (displayEvalResult, evaluateCompiledCode)

main :: IO ()
main = do
  putStrLn ""
  putStrLn $
    Text.unpack $
      displayEvalResult $
        evaluateCompiledCode validatorOptimizedCodeFullyApplied
