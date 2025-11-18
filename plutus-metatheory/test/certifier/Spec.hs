module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Test.Tasty

import Test.Certifier.AST (astTests)
import Test.Certifier.AST.ForceDelay (forceDelayASTTests)
import Test.Certifier.Optimizer (optimizerTests)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup
      "Certification"
      [ optimizerTests
      , astTests
      , forceDelayASTTests
      ]
