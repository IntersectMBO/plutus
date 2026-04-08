module Main where

import Test.Certifier.Report qualified as Report

import Test.Tasty

main :: IO ()
main = do
  reportTests <- Report.tests
  defaultMain $
    testGroup
      "Certifier Report"
      [reportTests]
