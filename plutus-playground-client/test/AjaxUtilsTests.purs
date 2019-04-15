module AjaxUtilsTests
       ( all
       ) where

import Prelude

import AjaxUtils (decodeJson, encodeJson)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Core as Argonaut
import Data.Either (Either(..))
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Data.Tuple (Tuple(..))
import Language.Haskell.Interpreter (CompilationError, InterpreterError, InterpreterResult)
import Ledger.Extra (LedgerMap(..))
import Ledger.Value.TH (CurrencySymbol(..), TokenName(..), Value(..))
import Node.FS (FS)
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency, TokenId)
import Test.Unit (TestSuite, suite, test)
import TestUtils (assertDecodesTo, assertEncodesTo, equalGShow)
import Type.Proxy (Proxy(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "AjaxUtils" do
    jsonHandling

jsonHandling :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
jsonHandling = do
    suite "Json handling" do
      test "Decode a List." do
        assertDecodesTo
          (Proxy :: Proxy (List TokenId))
          "test/token_ids.json"
      test ("Decode an empty NonEmptyList.") do
        equalGShow
          (Left "List is empty, expecting non-empty")
          (decodeJson (Argonaut.fromArray []) :: Either String (NonEmptyList TokenId))
      test ("Decode a populated NonEmptyList.") do
        assertDecodesTo
          (Proxy :: Proxy (NonEmptyList TokenId))
          "test/token_ids.json"
      test "Decode a KnownCurrency." do
        assertDecodesTo
          (Proxy :: Proxy KnownCurrency)
          "test/known_currency.json"
      test "Decode a CompilationResult." do
        assertDecodesTo
          (Proxy :: Proxy (Either InterpreterError (InterpreterResult CompilationResult)))
          "test/compilation_response1.json"
      test "Decode an EvaluationResult." do
        assertDecodesTo
          (Proxy :: Proxy EvaluationResult)
          "test/evaluation_response1.json"
      test "Decode a CompilationError." do
        assertDecodesTo
          (Proxy :: Proxy (Array CompilationError))
          "test/evaluation_error1.json"
      test "Decode/Encode a Value" do
        let aValue = Value { getValue: LedgerMap [ Tuple (CurrencySymbol { unCurrencySymbol: "0"}) (LedgerMap [ Tuple (TokenName { unTokenName: "ADA" }) 10 ])
                                                 , Tuple (CurrencySymbol { unCurrencySymbol: "1"}) (LedgerMap [ Tuple (TokenName { unTokenName: "USD" }) 20 ])
                                                 ]}
        equalGShow (Right aValue)
          (decodeJson (encodeJson aValue))
      test "Encode a Value." do
        let aValue = Value { getValue: LedgerMap [ Tuple (CurrencySymbol { unCurrencySymbol: "0" }) (LedgerMap [ Tuple (TokenName { unTokenName: "ADA" }) 100 ])
                                                 , Tuple (CurrencySymbol { unCurrencySymbol: "1" }) (LedgerMap [ Tuple (TokenName { unTokenName: "USD" }) 40 ])
                                                 , Tuple (CurrencySymbol { unCurrencySymbol: "2" }) (LedgerMap [ Tuple (TokenName { unTokenName: "EUR" }) 40 ])
                                                 ]}
        assertEncodesTo
          aValue
          "test/value1.json"
