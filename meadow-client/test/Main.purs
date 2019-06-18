module Test.Main where

import Prelude
import BridgeTests as BridgeTests
import Effect (Effect)
import Marlowe.ParserTests as ParserTests
import Marlowe.ContractTests as ContractTests
import Test.Unit.Main (runTest)

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    BridgeTests.all
    ParserTests.all
    ContractTests.all
