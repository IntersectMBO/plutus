module MainFrameTests
  ( all
  ) where

import Prelude
import Test.Unit (TestSuite, suite)

all :: TestSuite
all =
  suite "MainFrame" do
    evalTests

evalTests :: TestSuite
evalTests =
  suite "handleAction" do
    pure unit
