{-# LANGUAGE RecordWildCards #-}

module Main(main) where

import           Data.Aeson                  as Aeson (decode)
import           Data.ByteString.Lazy.UTF8   as BLU (fromString)
import           Data.Map                    hiding (filter)
import           Spec.Marlowe.ACTUS
import           Spec.Marlowe.ACTUS.Examples
import           System.Environment
import           Test.Tasty
import           Test.Tasty.HUnit

main :: IO ()
main = do
  p <- getEnv "ACTUS_TEST_DATA_DIR"

  pamTests <- testCasesFromFile ["pam25"] $ p ++ "actus-tests-pam.json" -- pam25: dates include hours, minutes, second
  lamTests <- testCasesFromFile ["lam18"] $ p ++ "actus-tests-lam.json" -- lam18: dates include hours, minutes, second
-- NAM, ANN temporarily commented - waiting for
-- https://github.com/actusfrf/actus-tests/pull/1
  namTests <- testCasesFromFile []        $ p ++ "actus-tests-nam.json"
  annTests <- testCasesFromFile [
      "ann09" -- ann09: currently unsupported, see also actus-core AnnuityTest.java
    , "ann19" -- ann19: dates include hours, minutes, second
    , "ann26" -- ann26: dates include hours, minutes, second
    ] $ p ++ "actus-tests-ann.json"

  defaultMain $ testGroup "ACTUS test-framework"
    [
      Spec.Marlowe.ACTUS.tests "PAM" pamTests
    , Spec.Marlowe.ACTUS.tests "LAM" lamTests
    , Spec.Marlowe.ACTUS.tests "NAM" namTests
    , Spec.Marlowe.ACTUS.tests "ANN" annTests
    , Spec.Marlowe.ACTUS.Examples.tests
    ]

testCasesFromFile :: [String] -> FilePath -> IO [TestCase]
testCasesFromFile excludedTestCases fileName = do
  tcs <- readFile fileName
  case let tc = fromString tcs in decode tc :: Maybe (Map String TestCase) of
    (Just decodedTests) -> return
                              $ filter (\TestCase{..} -> notElem identifier excludedTestCases)
                              $ fmap snd (toList decodedTests)
    Nothing             -> assertFailure ("Cannot parse test specification from file: " ++ fileName) >> return []
