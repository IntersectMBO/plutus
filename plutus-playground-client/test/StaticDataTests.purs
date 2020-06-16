module StaticDataTests
  ( all
  ) where

import Control.Monad.Except (runExcept)
import Prelude (($))
import StaticData (mkContractDemos)
import Test.Unit (TestSuite, suite, test)
import TestUtils (assertRight)

all :: TestSuite
all =
  suite "StaticData" do
    simulationDecodingTests

simulationDecodingTests :: TestSuite
simulationDecodingTests =
  suite "Simulation Decoding" do
    test "contractDemos" $ assertRight $ runExcept mkContractDemos
