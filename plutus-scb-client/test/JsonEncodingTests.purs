module JsonEncodingTests
  ( all
  ) where

import Prelude
import Plutus.SCB.Effects.ContractTest (TestContracts)
import Plutus.SCB.Webserver.Types (FullReport, ContractSignatureResponse)
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
        (Proxy :: Proxy (FullReport TestContracts))
        "generated/full_report_response.json"
    test "Decode a contract schema response." do
      assertDecodesTo
        (Proxy :: Proxy (ContractSignatureResponse TestContracts))
        "generated/contract_schema_response.json"
