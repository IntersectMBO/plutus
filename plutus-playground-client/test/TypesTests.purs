module TypesTests
       ( all
       ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.RawJson (JsonTuple(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff)
import Foreign (Foreign)
import Foreign.Class (encode)
import Foreign.Generic (encodeJSON)
import Foreign.Object as FO
import Ledger.Extra (LedgerMap(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.API (Fn(Fn), FunctionSchema(FunctionSchema), SimulatorWallet(SimulatorWallet))
import Schema (SimpleArgumentSchema(..))
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.Assert (equal)
import Types (Action(Action, Wait), SimpleArgument(..), simpleArgumentToJson)
import Validation (class Validation, ValidationError(..), validate, withPath)
import Wallet.Emulator.Types (Wallet(..))

all :: TestSuite
all =
  suite "Types" do
    validateTests
    simpleArgumentToJsonTests

validateTests :: TestSuite
validateTests = do
  test "No validation errors" do
    isValid $ Wait {blocks: 1}
    isValid $ makeTestAction [ SimpleInt (Just 5) ]
    isValid $ makeTestAction [ SimpleString (Just "TEST") ]
    isValid $ makeTestAction [ SimpleTuple (JsonTuple (Tuple (SimpleInt (Just 5)) (SimpleInt (Just 6)))) ]
    isValid $ makeTestAction [ SimpleArray SimpleIntSchema [] ]
    isValid $ makeTestAction [ SimpleObject (SimpleObjectSchema []) [] ]
    --
  test "Validation errors" do
    equal [ withPath ["0"] Unsupported ] $ validate (makeTestAction [ Unknowable { context: "TEST", description: "Test case."} ])
    equal [ withPath ["0"] Required ] $ validate (makeTestAction [ SimpleInt Nothing ])
    equal [ withPath ["0"] Required ] $ validate (makeTestAction [ SimpleString Nothing ])
    equal
      [ withPath ["0", "_1"] Required
      , withPath ["0", "_2"] Unsupported
      ]
      (validate (makeTestAction [ SimpleTuple (JsonTuple (Tuple (SimpleInt Nothing) (Unknowable { context: "TEST", description: "Test." }))) ]))
    equal [ withPath ["0", "_1"] Required ] $ validate (makeTestAction [ SimpleTuple (JsonTuple (Tuple (SimpleInt Nothing) (SimpleInt (Just 5)))) ])
    equal [ withPath ["0", "_2"] Required ] $ validate (makeTestAction [ SimpleTuple (JsonTuple (Tuple (SimpleInt (Just 5)) (SimpleInt Nothing))) ])
    equal [ withPath ["0", "2"] Required ]
      $ validate (makeTestAction [ SimpleArray SimpleIntSchema [ SimpleInt (Just 5)
                                                               , SimpleInt (Just 6)
                                                               , SimpleInt Nothing
                                                               , SimpleInt (Just 7)
                                                               ]
                                 ])
    equal
      [ withPath ["0", "name"] Required
      , withPath ["1", "test"] Required
      ]
      (let objectSchema = SimpleObjectSchema [ JsonTuple $ Tuple "name" SimpleStringSchema
                                             , JsonTuple $ Tuple "test" SimpleIntSchema
                                             ]
       in validate (makeTestAction [ SimpleObject objectSchema  [ JsonTuple $ Tuple "name" (SimpleString Nothing)
                                                                , JsonTuple $ Tuple "test" (SimpleInt (Just 5))
                                                                ]
                                   , SimpleObject objectSchema  [ JsonTuple $ Tuple "name" (SimpleString (Just "burt"))
                                                                , JsonTuple $ Tuple "test" (SimpleInt Nothing)
                                                                ]
                                   ])
      )

makeTestAction :: Array SimpleArgument -> Action
makeTestAction arguments =
  Action
    { simulatorWallet: SimulatorWallet { simulatorWalletWallet: Wallet { getWallet: 1 }
                                       , simulatorWalletBalance: Value { getValue: LedgerMap [ Tuple (CurrencySymbol { unCurrencySymbol: "12345" } )
                                                                                                     (LedgerMap [ Tuple (TokenName { unTokenName: "ADA" }) 100 ]) ] }
                                       }
    , functionSchema: FunctionSchema
                        { functionName: Fn "test"
                        , argumentSchema: arguments
                        }
    }

isValid :: forall a. Validation a => a -> Aff Unit
isValid = validate >>> equal []

simpleArgumentToJsonTests :: TestSuite
simpleArgumentToJsonTests = do
  suite "SimpleArgument to JSON" do
    test "Ints" $ do
      equalJson
        Nothing
        (simpleArgumentToJson (SimpleInt Nothing))
      equalJson
        (Just (encodeJSON 5))
        (simpleArgumentToJson (SimpleInt (Just 5)))
    test "Strings" $ do
      equalJson
        Nothing
        (simpleArgumentToJson (SimpleString Nothing))
      equalJson
        (Just (encodeJSON "Test"))
        (simpleArgumentToJson (SimpleString (Just "Test")))
    test "Tuples" $ do
      equalJson
        Nothing
        (simpleArgumentToJson (SimpleTuple (JsonTuple (SimpleInt Nothing /\ SimpleString Nothing))))
      equalJson
        Nothing
        (simpleArgumentToJson (SimpleTuple (JsonTuple (SimpleInt Nothing /\ SimpleString (Just "Test")))))
      equalJson
        Nothing
        (simpleArgumentToJson (SimpleTuple (JsonTuple (SimpleInt (Just 5) /\ SimpleString Nothing))))
      equalJson
        (Just (encodeJSON [ encode 5.0, encode "Test" ]))
        (simpleArgumentToJson (SimpleTuple (JsonTuple (SimpleInt (Just 5) /\ SimpleString (Just "Test")))))
    test "Arrays" $ do
      equalJson
        (Just (encodeJSON [ 1.0, 2.0, 3.0 ]))
        (simpleArgumentToJson (SimpleArray SimpleIntSchema [ SimpleInt (Just 1)
                                                           , SimpleInt (Just 2)
                                                           , SimpleInt (Just 3)
                                                           ]))
    test "Values" $ do
      let valueSchema = ValueSchema [
            JsonTuple (
               "getValue"
               /\
               SimpleObjectSchema [
                 JsonTuple (
                    "unMap"
                    /\
                    SimpleArraySchema (
                      SimpleTupleSchema (
                         JsonTuple (
                            SimpleHexSchema
                            /\
                            SimpleObjectSchema [
                              JsonTuple (
                                 "unMap"
                                 /\
                                 SimpleArraySchema (
                                   SimpleTupleSchema (
                                      JsonTuple (
                                         SimpleStringSchema
                                         /\
                                         SimpleIntSchema
                                         )
                                      )
                                   )
                                 )
                              ]
                            )
                         )
                      )
                    )
                 ]
               )
            ]
      equalJson
        (Just (encodeJSON (FO.singleton "getValue" [
                              [ encode (FO.singleton "unCurrencySymbol" "5fff")
                              , encode [
                                   [ encode (FO.singleton "unTokenName" "")
                                   , encode 4
                                   ]
                                   ]
                              ]
                              ])))
        (simpleArgumentToJson
          (ValueArgument
             valueSchema
             (Value { getValue: (LedgerMap [CurrencySymbol { unCurrencySymbol: "5fff" } /\ LedgerMap [TokenName { unTokenName: "" } /\ 4]]) })))

    test "Objects" $ do
      let objectSchema = SimpleObjectSchema [ JsonTuple $ Tuple "name" SimpleStringSchema
                                            , JsonTuple $ Tuple "test" SimpleIntSchema
                                            ]
      equalJson
        (Just (encodeJSON (FO.fromFoldable [ "name" /\ encode "Tester"
                                           , "arg" /\ encode 20.0
                                           ])))
        (simpleArgumentToJson (SimpleObject objectSchema [ JsonTuple $ "name" /\ SimpleString (Just "Tester")
                                                         , JsonTuple $ "arg" /\ SimpleInt (Just 20)
                                                         ]))

equalJson :: Maybe String -> Maybe Foreign -> Test
equalJson expected actual =
  equal expected (encodeJSON <$> actual)
