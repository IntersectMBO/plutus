module AjaxUtilsTests
       ( all
       ) where

import Prelude

import AjaxUtils (decodeJson, encodeJson)
import AjaxUtils as AjaxUtils
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Core as Argonaut
import Data.Either (Either(..))
import Data.Generic (class Generic, gShow)
import Data.List (List)
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.Types (NonEmptyList)
import Data.NonEmpty ((:|))
import Data.Tuple (Tuple(..))
import Language.Haskell.Interpreter (CompilationError, InterpreterError, InterpreterResult)
import Ledger.Extra (LedgerMap(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Node.FS (FS)
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency(..))
import Test.QuickCheck (arbitrary, withHelp)
import Test.QuickCheck.Gen (Gen, chooseInt, vectorOf)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (assertDecodesTo, assertEncodesTo, equalGShow)
import Type.Proxy (Proxy(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "AjaxUtils" do
    jsonHandlingTests

jsonHandlingTests :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
jsonHandlingTests = do
    suite "Json handling" do
      test "Decode a List." do
        assertDecodesTo
          (Proxy :: Proxy (List TokenName))
          "test/token_names.json"
      test ("Decode an empty NonEmptyList.") do
        equalGShow
          (Left "List is empty, expecting non-empty")
          (decodeJson (Argonaut.fromArray []) :: Either String (NonEmptyList TokenName))
      test ("Decode a populated NonEmptyList.") do
        assertDecodesTo
          (Proxy :: Proxy (NonEmptyList TokenName))
          "test/token_names.json"
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
      test "Encode Ada." do
        let aValue = Value { getValue: LedgerMap [ Tuple (CurrencySymbol { unCurrencySymbol: ""}) (LedgerMap [ Tuple (TokenName { unTokenName: "" }) 50 ])]}
        assertEncodesTo
          aValue
          "test/value_ada.json"
      suite "Roundtrips" do
        testRoundTrip "CurrencySymbol" arbitraryCurrencySymbol
        testRoundTrip "TokenName" arbitraryTokenName
        testRoundTrip "Value" arbitraryValue
        testRoundTrip "KnownCurrency" arbitraryKnownCurrency

testRoundTrip ::
  forall eff a.
  Eq a =>
  Generic a =>
  String ->
  Gen a ->
  TestSuite (random :: RANDOM | eff)
testRoundTrip title gen = do
  test title do
    quickCheck do
      value <- gen
      let expect = Right value
      let actual = AjaxUtils.decodeJson (AjaxUtils.encodeJson value)
      pure $ withHelp (expect == actual) $ "Expected: " <> gShow expect <> "Got: " <> gShow actual

arbitraryCurrencySymbol :: Gen CurrencySymbol
arbitraryCurrencySymbol = do
  str <- arbitrary
  pure $ CurrencySymbol { unCurrencySymbol: str }

arbitraryTokenName :: Gen TokenName
arbitraryTokenName = do
  str <- arbitrary
  pure $ TokenName { unTokenName: str }

arbitraryLedgerMap :: forall k v. Gen k -> Gen v -> Gen (LedgerMap k v)
arbitraryLedgerMap genK genV = do
  n <- chooseInt 0 5
  xs <- vectorOf n (Tuple <$> genK <*> genV)
  pure $ LedgerMap xs

arbitraryValue :: Gen Value
arbitraryValue = do
  ledgerMap <- arbitraryLedgerMap arbitraryCurrencySymbol (arbitraryLedgerMap arbitraryTokenName arbitrary)
  pure $ Value { getValue: ledgerMap }

arbitraryKnownCurrency :: Gen KnownCurrency
arbitraryKnownCurrency = do
  hash <- arbitrary
  friendlyName <- arbitrary
  knownTokens <- arbitraryNonEmptyList arbitraryTokenName
  pure $ KnownCurrency { hash, friendlyName, knownTokens }

arbitraryNonEmptyList :: forall a. Gen a -> Gen (NonEmptyList a)
arbitraryNonEmptyList genX = do
  n <- chooseInt 0 5
  x <- genX
  xs <- List.fromFoldable <$> vectorOf n genX
  pure $ NonEmptyList $ x :| xs
