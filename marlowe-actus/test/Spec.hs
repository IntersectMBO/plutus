{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import           Spec.Marlowe.ACTUS.Examples
import           Spec.Marlowe.ACTUS.TestFramework
import           System.Environment
import           Test.Tasty

main :: IO ()
main = do
  p <- getEnv "ACTUS_TEST_DATA_DIR"

  pamTests <- testCasesFromFile ["pam25"] $ p ++ "actus-tests-pam.json" -- pam25: dates include hours, minutes, second
  lamTests <- testCasesFromFile ["lam18"] $ p ++ "actus-tests-lam.json" -- lam18: dates include hours, minutes, second
  -- NAM, ANN temporarily commented - waiting for
  -- https://github.com/actusfrf/actus-tests/pull/1
  namTests <- testCasesFromFile [] $ p ++ "actus-tests-nam.json"
  annTests <-
    testCasesFromFile
      [ "ann09", -- ann09: currently unsupported, see also actus-core AnnuityTest.java
        "ann19", -- ann19: dates include hours, minutes, second
        "ann26" -- ann26: dates include hours, minutes, second
      ]
      $ p ++ "actus-tests-ann.json"

  defaultMain $
    testGroup
      "ACTUS test-framework"
      [ Spec.Marlowe.ACTUS.TestFramework.tests "PAM" pamTests,
        Spec.Marlowe.ACTUS.TestFramework.tests "LAM" lamTests,
        Spec.Marlowe.ACTUS.TestFramework.tests "NAM" namTests,
        Spec.Marlowe.ACTUS.TestFramework.tests "ANN" annTests,
        Spec.Marlowe.ACTUS.Examples.tests
      ]
