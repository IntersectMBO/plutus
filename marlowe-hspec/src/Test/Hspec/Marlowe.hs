module Test.Hspec.Marlowe where

import           Data.Bifunctor                        (first)
import           Language.Marlowe                      (Contract)
import           Language.Marlowe.Analysis.FSSemantics (warningsTrace)
import           Test.Hspec.Expectations               (Expectation, shouldBe)
import           Test.HUnit                            (assertFailure)

-- | Check that a Contract cannot lead to any warning states
--
-- This uses symbolic execution to inspect possible execution
-- paths. Be warned, this can take a lot of time and memory!
assertNoWarnings :: Contract -> Expectation
assertNoWarnings contract = do
    evRes <- warningsTrace contract
    case evRes of
        Left e -> assertFailure (show e)
        Right Nothing -> pure ()
        Right (Just counterExample) -> assertFailure $ "Found an input that would result in a warning:\n" <> show counterExample
