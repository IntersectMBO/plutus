module Schema.TypesTests
  ( all
  ) where

import Data.Functor.Foldable (Fix(..))
import Data.Json.JsonNonEmptyList (JsonNonEmptyList(..))
import Data.Json.JsonTuple (JsonTuple(..))
import Data.List (List(..))
import Data.List.NonEmpty (NonEmptyList(..))
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff)
import Foreign (Foreign)
import Foreign.Class (encode)
import Foreign.Generic (encodeJSON)
import Foreign.Object as FO
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (ContractCall(..), EndpointName(..), FunctionSchema(..), KnownCurrency(..))
import Prelude
import Schema (FormSchema(..), FormArgumentF(..))
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.Assert (equal)
import TestUtils (equalGenericShow)
import Types
import Schema.Types
import Validation (ValidationError(..), validate, withPath)
import Wallet.Emulator.Wallet (Wallet(..))

all :: TestSuite
all =
  suite "Schema.Types" do
    validateTests
    toArgumentTests
    formArgumentToJsonTests
    mkInitialValueTests

validateTests :: TestSuite
validateTests = do
  test "No validation errors" do
    isValid $ AddBlocks { blocks: 1 }
    isValid $ makeTestAction [ Fix $ FormIntF (Just 5) ]
    isValid $ makeTestAction [ Fix $ FormStringF (Just "TEST") ]
    isValid $ makeTestAction [ Fix $ FormTupleF (Fix $ FormIntF (Just 5)) (Fix $ FormIntF (Just 6)) ]
    isValid $ makeTestAction [ Fix $ FormArrayF FormSchemaInt [] ]
    isValid $ makeTestAction [ Fix $ FormObjectF [] ]
  --
  test "Validation errors" do
    equal [ withPath [ "0" ] Unsupported ] $ validate (makeTestAction [ Fix $ FormUnsupportedF "Test case." ])
    equal [ withPath [ "0" ] Required ] $ validate (makeTestAction [ Fix $ FormIntF Nothing ])
    equal [ withPath [ "0" ] Required ] $ validate (makeTestAction [ Fix $ FormStringF Nothing ])
    equal
      [ withPath [ "0", "_1" ] Required
      , withPath [ "0", "_2" ] Unsupported
      ]
      (validate (makeTestAction [ Fix $ FormTupleF (Fix $ FormIntF Nothing) (Fix $ FormUnsupportedF "Test.") ]))
    equal [ withPath [ "0", "_1" ] Required ] $ validate (makeTestAction [ Fix $ FormTupleF (Fix $ FormIntF Nothing) (Fix $ FormIntF (Just 5)) ])
    equal [ withPath [ "0", "_2" ] Required ] $ validate (makeTestAction [ Fix $ FormTupleF (Fix $ FormIntF (Just 5)) (Fix $ FormIntF Nothing) ])
    equal [ withPath [ "0", "2" ] Required ]
      $ validate
          ( makeTestAction
              [ Fix
                  $ FormArrayF FormSchemaInt
                      [ Fix $ FormIntF (Just 5)
                      , Fix $ FormIntF (Just 6)
                      , Fix $ FormIntF Nothing
                      , Fix $ FormIntF (Just 7)
                      ]
              ]
          )
    equal
      [ withPath [ "0", "name" ] Required
      , withPath [ "1", "test" ] Required
      ]
      ( validate
          ( makeTestAction
              [ Fix
                  $ FormObjectF
                      [ JsonTuple $ Tuple "name" (Fix $ FormStringF Nothing)
                      , JsonTuple $ Tuple "test" (Fix $ FormIntF (Just 5))
                      ]
              , Fix
                  $ FormObjectF
                      [ JsonTuple $ Tuple "name" (Fix $ FormStringF (Just "burt"))
                      , JsonTuple $ Tuple "test" (Fix $ FormIntF Nothing)
                      ]
              ]
          )
      )

toArgumentTests :: TestSuite
toArgumentTests = do
  suite "toArgument" do
    let
      initialValue :: Value
      initialValue =
        Value
          { getValue:
            AssocMap.fromTuples
              [ ( Tuple (CurrencySymbol { unCurrencySymbol: "12345" })
                    (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "ADA" }) 100 ])
                )
              ]
          }
    test "FormIntF" do
      equal
        (toArgument initialValue FormSchemaInt)
        (Fix (FormIntF Nothing))
    test "Value" do
      equal
        (toArgument initialValue FormSchemaValue)
        (Fix (FormValueF initialValue))

makeTestAction :: Array FormArgument -> SimulatorAction
makeTestAction arguments =
  CallEndpoint
    { caller:
      Wallet { getWallet: 1 }
    , argumentValues:
      FunctionSchema
        { endpointName: EndpointName "test"
        , arguments
        }
    }

isValid :: SimulatorAction -> Aff Unit
isValid = validate >>> equal []

formArgumentToJsonTests :: TestSuite
formArgumentToJsonTests = do
  suite "FormArgument to JSON" do
    test "Ints" do
      equalJson
        Nothing
        (formArgumentToJson (Fix $ FormIntF Nothing))
      equalJson
        (Just (encodeJSON 5))
        (formArgumentToJson (Fix $ FormIntF (Just 5)))
    test "Strings" do
      equalJson
        Nothing
        (formArgumentToJson (Fix $ FormStringF Nothing))
      equalJson
        (Just (encodeJSON "Test"))
        (formArgumentToJson (Fix $ FormStringF (Just "Test")))
    test "Tuples" do
      equalJson
        Nothing
        (formArgumentToJson (Fix $ FormTupleF (Fix $ FormIntF Nothing) (Fix $ FormStringF Nothing)))
      equalJson
        Nothing
        (formArgumentToJson (Fix $ FormTupleF (Fix $ FormIntF Nothing) (Fix $ FormStringF (Just "Test"))))
      equalJson
        Nothing
        (formArgumentToJson (Fix $ FormTupleF (Fix $ FormIntF (Just 5)) (Fix $ FormStringF Nothing)))
      equalJson
        (Just (encodeJSON [ encode 5.0, encode "Test" ]))
        (formArgumentToJson (Fix $ FormTupleF (Fix $ FormIntF (Just 5)) (Fix $ FormStringF (Just "Test"))))
    test "Arrays" do
      equalJson
        (Just (encodeJSON [ 1.0, 2.0, 3.0 ]))
        ( formArgumentToJson
            ( Fix
                $ FormArrayF FormSchemaInt
                    [ Fix $ FormIntF (Just 1)
                    , Fix $ FormIntF (Just 2)
                    , Fix $ FormIntF (Just 3)
                    ]
            )
        )
    test "Values" do
      equalJson
        ( Just
            ( encodeJSON
                ( FO.singleton "getValue"
                    [ [ encode $ FO.singleton "unCurrencySymbol" ""
                      , encode
                          [ [ encode $ FO.singleton "unTokenName" ""
                            , encode 4
                            ]
                          ]
                      ]
                    ]
                )
            )
        )
        ( formArgumentToJson
            ( Fix
                $ FormValueF
                    (Value { getValue: AssocMap.fromTuples [ CurrencySymbol { unCurrencySymbol: "" } /\ AssocMap.fromTuples [ TokenName { unTokenName: "" } /\ 4 ] ] })
            )
        )
    test "Objects" do
      equalJson
        ( Just
            ( encodeJSON
                ( FO.fromFoldable
                    [ "name" /\ encode "Tester"
                    , "arg" /\ encode 20.0
                    ]
                )
            )
        )
        ( formArgumentToJson
            ( Fix
                $ FormObjectF
                    [ JsonTuple $ "name" /\ (Fix $ FormStringF (Just "Tester"))
                    , JsonTuple $ "arg" /\ (Fix $ FormIntF (Just 20))
                    ]
            )
        )

mkInitialValueTests :: TestSuite
mkInitialValueTests =
  suite "mkInitialValue" do
    test "balance" do
      equalGenericShow
        ( Value
            { getValue:
              AssocMap.fromTuples
                [ ada /\ AssocMap.fromTuples [ adaToken /\ 10 ]
                , currencies
                    /\ AssocMap.fromTuples
                        [ usdToken /\ 10
                        , eurToken /\ 10
                        ]
                ]
            }
        )
        ( mkInitialValue
            [ KnownCurrency { hash: "", friendlyName: "Ada", knownTokens: (JsonNonEmptyList (pure (TokenName { unTokenName: "" }))) }
            , KnownCurrency { hash: "Currency", friendlyName: "Currencies", knownTokens: JsonNonEmptyList (NonEmptyList ((TokenName { unTokenName: "USDToken" }) :| (Cons (TokenName { unTokenName: "EURToken" }) Nil))) }
            ]
            10
        )

ada :: CurrencySymbol
ada = CurrencySymbol { unCurrencySymbol: "" }

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency" }

adaToken :: TokenName
adaToken = TokenName { unTokenName: "" }

usdToken :: TokenName
usdToken = TokenName { unTokenName: "USDToken" }

eurToken :: TokenName
eurToken = TokenName { unTokenName: "EURToken" }

equalJson :: Maybe String -> Maybe Foreign -> Test
equalJson expected actual = equal expected (encodeJSON <$> actual)
