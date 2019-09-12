module AjaxUtilsTests
  ( all
  ) where

import Prelude

import Auth (AuthStatus)
import Control.Monad.Except (runExcept)
import Cursor (Cursor)
import Cursor as Cursor
import Data.Either (Either(..))
import Data.RawJson (JsonEither(..), JsonNonEmptyList(..), JsonTuple(..))
import Data.Tuple (Tuple(..))
import Foreign (MultipleErrors)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Language.Haskell.Interpreter (CompilationError, InterpreterError, InterpreterResult)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency(..), PlaygroundError)
import Test.QuickCheck (arbitrary, withHelp)
import Test.QuickCheck.Gen (Gen, chooseInt, vectorOf)
import Test.Unit (TestSuite, failure, success, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (arbitraryEither, arbitraryNonEmptyList, assertDecodesTo, assertEncodesTo)
import Type.Proxy (Proxy(..))

all :: TestSuite
all =
  suite "AjaxUtils" do
    jsonHandlingTests

jsonHandlingTests :: TestSuite
jsonHandlingTests = do
  suite "Json handling" do
    test "Decode a List." do
      assertDecodesTo
        (Proxy :: Proxy (Array TokenName))
        "test/token_names.json"
    test ("Decode an empty NonEmptyList should fail.") do
      case (runExcept (decode (encode ([] :: Array TokenName))) :: Either MultipleErrors (JsonNonEmptyList TokenName)) of
        Left _ -> success
        Right value -> failure $ "A empty list shouldn't decode into a NonEmptyList. Expected failure, got: " <> show value
    test ("Decode a populated NonEmptyList.") do
      assertDecodesTo
        (Proxy :: Proxy (JsonNonEmptyList TokenName))
        "test/token_names.json"
    test "Decode a KnownCurrency." do
      assertDecodesTo
        (Proxy :: Proxy KnownCurrency)
        "test/known_currency.json"
    test "Decode a compilation response." do
      assertDecodesTo
        (Proxy :: Proxy (JsonEither InterpreterError (InterpreterResult CompilationResult)))
        "test/compilation_response1.json"
    test "Decode an EvaluationResult." do
      assertDecodesTo
        (Proxy :: Proxy (JsonEither PlaygroundError EvaluationResult))
        "test/evaluation_response1.json"
    test "Decode an AuthStatus." do
      assertDecodesTo
        (Proxy :: Proxy AuthStatus)
        "test/authstatus.json"
    test "Decode a CompilationError." do
      assertDecodesTo
        (Proxy :: Proxy (Array CompilationError))
        "test/evaluation_error1.json"
    test "Decode/Encode a Value" do
      let
        aValue =
          Value
            { getValue:
              AssocMap.fromTuples
                [ Tuple (CurrencySymbol { unCurrencySymbol: "0" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "ADA" }) 10 ])
                , Tuple (CurrencySymbol { unCurrencySymbol: "1" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "USD" }) 20 ])
                ]
            }
      equal
        (Right aValue)
        (runExcept (decode (encode aValue)))
    test "Encode a Value." do
      let
        aValue =
          Value
            { getValue:
              AssocMap.fromTuples
                [ Tuple (CurrencySymbol { unCurrencySymbol: "0" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "ADA" }) 100 ])
                , Tuple (CurrencySymbol { unCurrencySymbol: "1" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "USD" }) 40 ])
                , Tuple (CurrencySymbol { unCurrencySymbol: "2" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "EUR" }) 40 ])
                ]
            }
      assertEncodesTo
        aValue
        "test/value1.json"
    test "Encode Ada." do
      let
        aValue = Value { getValue: AssocMap.fromTuples [ Tuple (CurrencySymbol { unCurrencySymbol: "" }) (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "" }) 50 ]) ] }
      assertEncodesTo
        aValue
        "test/value_ada.json"
    suite "Roundtrips" do
      testRoundTrip "CurrencySymbol" arbitraryCurrencySymbol
      testRoundTrip "TokenName" arbitraryTokenName
      testRoundTrip "Value" arbitraryValue
      testRoundTrip "KnownCurrency" arbitraryKnownCurrency
      testRoundTrip "JsonEither" ((JsonEither <$> arbitraryEither arbitrary arbitrary) :: Gen (JsonEither String Int))
      testRoundTrip "JsonTuple" ((JsonTuple <$> (Tuple <$> arbitrary <*> arbitrary)) :: Gen (JsonTuple String Int))
      testRoundTrip "JsonNonEmptyList" ((JsonNonEmptyList <$> arbitrary) :: Gen (JsonNonEmptyList String))
      testRoundTrip "Cursor" ((Cursor.fromArray <$> arbitrary) :: Gen (Cursor String))

testRoundTrip ::
  forall a.
  Eq a =>
  Decode a =>
  Encode a =>
  Show a =>
  String ->
  Gen a ->
  TestSuite
testRoundTrip title gen = do
  test title do
    quickCheck do
      value <- gen
      let
        expect = Right value
      let
        actual = runExcept $ decode $ encode value
      pure $ withHelp (expect == actual) $ "Expected: " <> show expect <> "Got: " <> show actual

arbitraryCurrencySymbol :: Gen CurrencySymbol
arbitraryCurrencySymbol = do
  str <- arbitrary
  pure $ CurrencySymbol { unCurrencySymbol: str }

arbitraryTokenName :: Gen TokenName
arbitraryTokenName = do
  str <- arbitrary
  pure $ TokenName { unTokenName: str }

arbitraryAssocMap :: forall k v. Gen k -> Gen v -> Gen (AssocMap.Map k v)
arbitraryAssocMap genK genV = do
  n <- chooseInt 0 5
  xs <- vectorOf n (JsonTuple <$> (Tuple <$> genK <*> genV))
  pure $ AssocMap.Map xs

arbitraryValue :: Gen Value
arbitraryValue = do
  assocMap <- arbitraryAssocMap arbitraryCurrencySymbol (arbitraryAssocMap arbitraryTokenName arbitrary)
  pure $ Value { getValue: assocMap }

arbitraryKnownCurrency :: Gen KnownCurrency
arbitraryKnownCurrency = do
  hash <- arbitrary
  friendlyName <- arbitrary
  knownTokens <- JsonNonEmptyList <$> arbitraryNonEmptyList arbitraryTokenName
  pure $ KnownCurrency { hash, friendlyName, knownTokens }
