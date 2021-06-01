module Marlowe.Holes.TimeoutTest where

import Prelude
import Data.Maybe (Maybe(..))
import Marlowe.Gen (genContract, GenerationOptions(..))
import Marlowe.GenWithHoles (GenWithHoles, contractQuickCheck)
import Marlowe.Holes (fromTerm)
import Marlowe.Semantics (timeouts)
import Marlowe.Semantics as S
import Test.QuickCheck (Result, (===))
import Test.Unit (TestSuite, suite, test)

all :: TestSuite
all =
  suite "Marlowe.Holes.Timeout" do
    test "Term and Semantic contract has the same timeouts" $ contractQuickCheck (GenerationOptions { withHoles: false, withExtendedConstructs: false }) sameTimeouts

sameTimeouts :: GenWithHoles Result
sameTimeouts = do
  termContract <- genContract
  let
    (mSContract :: Maybe S.Contract) = fromTerm termContract

    termTimeouts = timeouts termContract

    mSemanticTimeouts = timeouts <$> mSContract
  pure (Just termTimeouts === mSemanticTimeouts)
