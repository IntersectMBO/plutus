module Test.Main where

import Prelude
import BridgeTests as BridgeTests
import Effect (Effect)
import Marlowe.BlocklyTests as BlocklyTests
import Marlowe.ContractTests as ContractTests
import Marlowe.LintTests as LintTests
import Marlowe.ParserTests as ParserTests
import Marlowe.DeinstantiatorTests as DeinstantiatorTests
import Test.Unit.Main (runTest)

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    BridgeTests.all
    ParserTests.all
    ContractTests.all
    BlocklyTests.all
    LintTests.all
    DeinstantiatorTests.all
