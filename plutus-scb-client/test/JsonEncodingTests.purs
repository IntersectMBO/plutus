module JsonEncodingTests
  ( all
  ) where

import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (FullReport)
import Test.Unit (TestSuite, suite, test)
import TestUtils (assertDecodesTo)
import Type.Proxy (Proxy(..))

all :: TestSuite
all =
  suite "JsonEncoding" do
    jsonHandlingTests

jsonHandlingTests :: TestSuite
jsonHandlingTests = do
  suite "Json handling" do
    test "Decode a full report response." do
      assertDecodesTo
        (Proxy :: Proxy (FullReport ContractExe))
        "generated/full_report_response.json"
