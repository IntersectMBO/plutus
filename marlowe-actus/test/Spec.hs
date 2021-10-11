{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import           Spec.Marlowe.ACTUS.Examples
import           Spec.Marlowe.ACTUS.QCTests
import           Spec.Marlowe.ACTUS.TestFramework
import           System.Environment
import           Test.Tasty

main :: IO ()
main = do
  p <- getEnv "ACTUS_TEST_DATA_DIR"

  pamTests <- testCasesFromFile [] $ p ++ "actus-tests-pam.json"
  lamTests <- testCasesFromFile [] $ p ++ "actus-tests-lam.json"
  namTests <- testCasesFromFile [] $ p ++ "actus-tests-nam.json"
  annTests <-
    testCasesFromFile
      [ "ann09" -- ann09: currently unsupported, see also actus-core AnnuityTest.java
      ]
      $ p ++ "actus-tests-ann.json"
  stkTests <- testCasesFromFile [] $ p ++ "actus-tests-stk.json"
  optnsTests <- testCasesFromFile [] $ p ++ "actus-tests-optns.json"
  -- futurTests <- testCasesFromFile [] $ p ++ "actus-tests-futur.json"

  defaultMain $
    testGroup
      "ACTUS test cases"
      [ testGroup
          "ACTUS test-framework"
          [ Spec.Marlowe.ACTUS.TestFramework.tests "PAM" pamTests
          , Spec.Marlowe.ACTUS.TestFramework.tests "LAM" lamTests
          , Spec.Marlowe.ACTUS.TestFramework.tests "NAM" namTests
          , Spec.Marlowe.ACTUS.TestFramework.tests "ANN" annTests
          , Spec.Marlowe.ACTUS.TestFramework.tests "STK" stkTests
          , Spec.Marlowe.ACTUS.TestFramework.tests "OPTNS" optnsTests
          -- , Spec.Marlowe.ACTUS.TestFramework.tests "FUTUR" futurTests
          ],
        testGroup
          "ACTUS examples"
          [ Spec.Marlowe.ACTUS.Examples.tests
          ],
        testGroup
          "QuickCheck"
          [ Spec.Marlowe.ACTUS.QCTests.tests
          ]
      ]
