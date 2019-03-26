module TypesTests
       ( all
       ) where

import Prelude

import Control.Monad.Aff (Aff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Core (fromArray, fromNumber, fromObject, fromString)
import Data.Maybe (Maybe(..))
import Data.StrMap as StrMap
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Ledger.Value.TH (CurrencySymbol(..), Value(..))
import Playground.API (Fn(Fn), FunctionSchema(FunctionSchema), SimpleArgumentSchema(..), SimulatorWallet(SimulatorWallet))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Types (Action(Action, Wait), SimpleArgument(SimpleInt, SimpleString, SimpleObject, SimpleArray, SimpleTuple, Unknowable), simpleArgumentToJson)
import Validation (class Validation, ValidationError(..), validate, withPath)
import Wallet.Emulator.Types (Wallet(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
all =
  suite "Types" do
    validateTests
    simpleArgumentToJsonTests

validateTests :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
validateTests = do
  test "No validation errors" do
    isValid $ Wait {blocks: 1}
    isValid $ makeTestAction [ SimpleInt (Just 5) ]
    isValid $ makeTestAction [ SimpleString (Just "TEST") ]
    isValid $ makeTestAction [ SimpleTuple (Tuple (SimpleInt (Just 5)) (SimpleInt (Just 6))) ]
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
      (validate (makeTestAction [ SimpleTuple (Tuple (SimpleInt Nothing) (Unknowable { context: "TEST", description: "Test." })) ]))
    equal [ withPath ["0", "_1"] Required ] $ validate (makeTestAction [ SimpleTuple (Tuple (SimpleInt Nothing) (SimpleInt (Just 5))) ])
    equal [ withPath ["0", "_2"] Required ] $ validate (makeTestAction [ SimpleTuple (Tuple (SimpleInt (Just 5)) (SimpleInt Nothing)) ])
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
      (let objectSchema = SimpleObjectSchema [ Tuple "name" SimpleStringSchema
                                             , Tuple "test" SimpleIntSchema
                                             ]
       in validate (makeTestAction [ SimpleObject objectSchema  [ Tuple "name" (SimpleString Nothing)
                                                                , Tuple "test" (SimpleInt (Just 5))
                                                                ]
                                   , SimpleObject objectSchema  [ Tuple "name" (SimpleString (Just "burt"))
                                                                , Tuple "test" (SimpleInt Nothing)
                                                                ]
                                   ])
      )

makeTestAction :: Array SimpleArgument -> Action
makeTestAction arguments =
  Action
    { simulatorWallet: SimulatorWallet { simulatorWalletWallet: Wallet { getWallet: 1 }
                                       , simulatorWalletBalance: Value { getValue: [ Tuple (CurrencySymbol 12345) 10 ] }
                                       }
    , functionSchema: FunctionSchema
                        { functionName: Fn "test"
                        , argumentSchema: arguments
                        }
    }

isValid :: forall m a. Validation a => a -> Aff m Unit
isValid = validate >>> equal []

simpleArgumentToJsonTests :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
simpleArgumentToJsonTests = do
  suite "SimpleArgument to JSON" do
    test "Ints" $ do
      equal
        Nothing
        (simpleArgumentToJson (SimpleInt Nothing))
      equal
        (Just (fromNumber 5.0))
        (simpleArgumentToJson (SimpleInt (Just 5)))
    test "Strings" $ do
      equal
        Nothing
        (simpleArgumentToJson (SimpleString Nothing))
      equal
        (Just (fromString "Test"))
        (simpleArgumentToJson (SimpleString (Just "Test")))
    test "Tuples" $ do
      equal
        Nothing
        (simpleArgumentToJson (SimpleTuple (SimpleInt Nothing /\ SimpleString Nothing)))
      equal
        Nothing
        (simpleArgumentToJson (SimpleTuple (SimpleInt Nothing /\ SimpleString (Just "Test"))))
      equal
        Nothing
        (simpleArgumentToJson (SimpleTuple (SimpleInt (Just 5) /\ SimpleString Nothing)))
      equal
        (Just (fromArray [ fromNumber 5.0, fromString "Test" ]))
        (simpleArgumentToJson (SimpleTuple (SimpleInt (Just 5) /\ SimpleString (Just "Test"))))
    test "Arrays" $ do
      equal
        (Just (fromArray (fromNumber <$> [ 1.0, 2.0, 3.0 ])))
        (simpleArgumentToJson (SimpleArray SimpleIntSchema [ SimpleInt (Just 1)
                                                           , SimpleInt (Just 2)
                                                           , SimpleInt (Just 3)
                                                           ]))
    test "Objects" $ do
      let objectSchema = SimpleObjectSchema [ Tuple "name" SimpleStringSchema
                                            , Tuple "test" SimpleIntSchema
                                            ]
      equal
        (Just (fromObject (StrMap.fromFoldable [ "name" /\ fromString "Tester"
                                               , "arg" /\ fromNumber 20.0
                                               ])))
        (simpleArgumentToJson (SimpleObject objectSchema [ "name" /\ SimpleString (Just "Tester")
                                                         , "arg" /\ SimpleInt (Just 20)
                                                         ]))
