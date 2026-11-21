module Main (main) where

import Data.Char (isSpace)
import System.Process (readProcess)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

main :: IO ()
main =
  defaultMain $
    testGroup
      "docusaurus examples"
      [ testCase "example-builtin-value: keeping the state token passes, losing it fails" $ do
          output <- readProcess "example-builtin-value" [] ""
          evaluationResults output @?= ["True", "False"]
      ]

-- | The result printed under each successful evaluation by 'PlutusTx.Eval.displayEvalResult'.
evaluationResults :: String -> [String]
evaluationResults = go . lines
  where
    go (header : result : rest)
      | header == "Evaluation was SUCCESSFUL, result is:" = dropWhile isSpace result : go rest
    go (_ : rest) = go rest
    go [] = []
