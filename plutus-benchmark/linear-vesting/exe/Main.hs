module Main (main) where

import Data.Text qualified as Text
import LinearVesting (validatorCodeFullyApplied)
import PlutusTx.Test (displayEvalResult, evaluateCompiledCode)

main :: IO ()
main = do
  putStrLn ""
  putStrLn $
    Text.unpack $
      displayEvalResult $
        evaluateCompiledCode validatorCodeFullyApplied
