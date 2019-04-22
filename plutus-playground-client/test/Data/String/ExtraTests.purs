module Data.String.ExtraTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Random (RANDOM)
import Data.String as String
import Data.String.Extra (abbreviate)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)

all :: forall eff. TestSuite (random :: RANDOM | eff)
all =
  suite "Data.String.Extra" do
    abbreviateTests

abbreviateTests :: forall eff. TestSuite (random :: RANDOM | eff)
abbreviateTests = do
  suite "abbreviate" do
    test "Always limits the string length" do
      quickCheck \str -> String.length (abbreviate str) <= 10
    test "Never affects the start of the string" do
      quickCheck \str ->
        String.take 5 str ==
        String.take 5 (abbreviate str)
