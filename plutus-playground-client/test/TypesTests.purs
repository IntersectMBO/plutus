module TypesTests
  ( all
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff)
import Foreign (Foreign)
import Foreign.Class (encode)
import Foreign.Generic (encodeJSON)
import Foreign.Object as FO
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (Fn(Fn), FunctionSchema(FunctionSchema), SimulatorWallet(SimulatorWallet))
import Schema (FormSchema(..))
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.Assert (equal)
import Types (Action(Action, Wait), FormArgument(..), formArgumentToJson, toArgument)
import Validation (class Validation, ValidationError(..), validate, withPath)
import Wallet.Emulator.Types (Wallet(..))

all :: TestSuite
all =
  suite "Types" do
    validateTests
    toArgumentTests
    formArgumentToJsonTests

validateTests :: TestSuite
validateTests = do
  test "No validation errors" do
    isValid $ Wait { blocks: 1 }
    isValid $ makeTestAction [ FormInt (Just 5) ]
    isValid $ makeTestAction [ FormString (Just "TEST") ]
    isValid $ makeTestAction [ FormTuple (JsonTuple (Tuple (FormInt (Just 5)) (FormInt (Just 6)))) ]
    isValid $ makeTestAction [ FormArray FormSchemaInt [] ]
    isValid $ makeTestAction [ FormObject [] ]
  --
  test "Validation errors" do
    equal [ withPath [ "0" ] Unsupported ] $ validate (makeTestAction [ FormUnsupported { description: "Test case." } ])
    equal [ withPath [ "0" ] Required ] $ validate (makeTestAction [ FormInt Nothing ])
    equal [ withPath [ "0" ] Required ] $ validate (makeTestAction [ FormString Nothing ])
    equal
      [ withPath [ "0", "_1" ] Required
      , withPath [ "0", "_2" ] Unsupported
      ]
      (validate (makeTestAction [ FormTuple (JsonTuple (Tuple (FormInt Nothing) (FormUnsupported { description: "Test." }))) ]))
    equal [ withPath [ "0", "_1" ] Required ] $ validate (makeTestAction [ FormTuple (JsonTuple (Tuple (FormInt Nothing) (FormInt (Just 5)))) ])
    equal [ withPath [ "0", "_2" ] Required ] $ validate (makeTestAction [ FormTuple (JsonTuple (Tuple (FormInt (Just 5)) (FormInt Nothing))) ])
    equal [ withPath [ "0", "2" ] Required ]
      $ validate
          ( makeTestAction
              [ FormArray FormSchemaInt
                  [ FormInt (Just 5)
                  , FormInt (Just 6)
                  , FormInt Nothing
                  , FormInt (Just 7)
                  ]
              ]
          )
    equal
      [ withPath [ "0", "name" ] Required
      , withPath [ "1", "test" ] Required
      ]
      ( validate
          ( makeTestAction
              [ FormObject
                  [ JsonTuple $ Tuple "name" (FormString Nothing)
                  , JsonTuple $ Tuple "test" (FormInt (Just 5))
                  ]
              , FormObject
                  [ JsonTuple $ Tuple "name" (FormString (Just "burt"))
                  , JsonTuple $ Tuple "test" (FormInt Nothing)
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
    test "FormInt" do
      equal
        (toArgument initialValue FormSchemaInt)
        (FormInt Nothing)
    test "Value" do
      equal
        (toArgument initialValue FormSchemaValue)
        (FormValue initialValue)

makeTestAction :: Array FormArgument -> Action
makeTestAction arguments =
  Action
    { simulatorWallet:
      SimulatorWallet
        { simulatorWalletWallet: Wallet { getWallet: 1 }
        , simulatorWalletBalance:
          Value
            { getValue:
              AssocMap.fromTuples
                [ ( Tuple (CurrencySymbol { unCurrencySymbol: "12345" })
                      (AssocMap.fromTuples [ Tuple (TokenName { unTokenName: "ADA" }) 100 ])
                  )
                ]
            }
        }
    , functionSchema:
      FunctionSchema
        { functionName: Fn "test"
        , argumentSchema: arguments
        }
    }

isValid :: forall a. Validation a => a -> Aff Unit
isValid = validate >>> equal []

formArgumentToJsonTests :: TestSuite
formArgumentToJsonTests = do
  suite "FormArgument to JSON" do
    test "Ints" do
      equalJson
        Nothing
        (formArgumentToJson (FormInt Nothing))
      equalJson
        (Just (encodeJSON 5))
        (formArgumentToJson (FormInt (Just 5)))
    test "Strings" do
      equalJson
        Nothing
        (formArgumentToJson (FormString Nothing))
      equalJson
        (Just (encodeJSON "Test"))
        (formArgumentToJson (FormString (Just "Test")))
    test "Tuples" do
      equalJson
        Nothing
        (formArgumentToJson (FormTuple (JsonTuple (FormInt Nothing /\ FormString Nothing))))
      equalJson
        Nothing
        (formArgumentToJson (FormTuple (JsonTuple (FormInt Nothing /\ FormString (Just "Test")))))
      equalJson
        Nothing
        (formArgumentToJson (FormTuple (JsonTuple (FormInt (Just 5) /\ FormString Nothing))))
      equalJson
        (Just (encodeJSON [ encode 5.0, encode "Test" ]))
        (formArgumentToJson (FormTuple (JsonTuple (FormInt (Just 5) /\ FormString (Just "Test")))))
    test "Arrays" do
      equalJson
        (Just (encodeJSON [ 1.0, 2.0, 3.0 ]))
        ( formArgumentToJson
            ( FormArray FormSchemaInt
                [ FormInt (Just 1)
                , FormInt (Just 2)
                , FormInt (Just 3)
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
            ( FormValue
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
            ( FormObject
                [ JsonTuple $ "name" /\ FormString (Just "Tester")
                , JsonTuple $ "arg" /\ FormInt (Just 20)
                ]
            )
        )

equalJson :: Maybe String -> Maybe Foreign -> Test
equalJson expected actual = equal expected (encodeJSON <$> actual)
