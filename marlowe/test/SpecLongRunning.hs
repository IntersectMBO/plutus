{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.PAB.Workflow
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Marlowe"
    [ testGroup "PAB Workflow"
      [ Spec.PAB.Workflow.tests
      ]
    ]
