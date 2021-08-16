{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main(main) where

import           Data.Aeson                as Aeson (decode)
import           Data.ByteString.Lazy.UTF8 as BLU (fromString)
import           Data.Map                  hiding (filter)
import           Spec.Marlowe.Actus
import           System.Environment
import           Test.Tasty

main :: IO ()
main = do
  p <- getEnv "ACTUS_TEST_DATA_DIR"

  pamTests <- testCasesFromFile ["pam25"] $ p ++ "actus-tests-pam.json" -- pam25: dates include hours, minutes, second
  -- lamTests <- testCasesFromFile []        $ p ++ "actus-tests-lam.json"
  -- namTests <- testCasesFromFile []        $ p ++ "actus-tests-nam.json"

  defaultMain $ testGroup "ACTUS Contracts"
    [
      Spec.Marlowe.Actus.tests "PAM" pamTests
 -- , Spec.Marlowe.Actus.tests "LAM" lamTests
 -- , Spec.Marlowe.Actus.tests "NAM" namTests
    ]

testCasesFromFile :: [String] -> FilePath -> IO [TestCase]
testCasesFromFile excludedTestCases fileName = do
  tcs <- readFile fileName
  let Just decodedTests = let tc = fromString tcs in decode tc :: Maybe (Map String TestCase)
  return
    $ filter (\TestCase{..} -> notElem identifier excludedTestCases)
    $ fmap snd (toList decodedTests)
