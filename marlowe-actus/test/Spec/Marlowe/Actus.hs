module Spec.Marlowe.Actus
    ( tests
    )
where

import           Spec.Marlowe.Util
import           System.Environment
import           Test.Tasty
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Actus"
    [
      testCase "PAM static ACTUS" pamStaticFromFile
    ]

excludedTestCases :: [String]
excludedTestCases =
  [
    "pam25" -- dates include hours, minutes, seconds
  ]


pathToTests :: IO String
pathToTests = do
  getEnv "ACTUS_TEST_DATA_DIR"

pamStaticFromFile :: IO ()
pamStaticFromFile = do
  testPath <- pathToTests
  assertTestResultsFromFile excludedTestCases (testPath ++ "actus-tests-pam.json")
