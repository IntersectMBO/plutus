module TypesTests
       ( all
       ) where

import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Ledger.Ada.TH (Ada(..))
import Playground.API (Fn(Fn), FunctionSchema(FunctionSchema), SimpleArgumentSchema(..), SimulatorWallet(SimulatorWallet))
import Prelude (discard, unit, ($))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Types (Action(..), SimpleArgument(..))
import Validation (ValidationError(..), validate)
import Wallet.Emulator.Types (Wallet(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
all =
  suite "Types" do
    validateTests

validateTests :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
validateTests = do
  test "No validation errors" do
    equal [] $ validate unit (Wait {blocks: 1})
    equal [] $ validate unit (makeTestAction [ SimpleInt (Just 5) ])
    equal [] $ validate unit (makeTestAction [ SimpleString (Just "TEST") ])
    equal [] $ validate unit (makeTestAction [ SimpleTuple (Tuple (SimpleInt (Just 5)) (SimpleInt (Just 6))) ])
    equal [] $ validate unit (makeTestAction [ SimpleArray SimpleIntSchema [] ])
    equal [] $ validate unit (makeTestAction [ SimpleObject (SimpleObjectSchema []) [] ])
    --
  test "Validation errors" do
    equal [ Unsupported "0" ] $ validate unit (makeTestAction [ Unknowable { context: "TEST", description: "Test case."} ])
    equal [ Required "0" ] $ validate unit (makeTestAction [ SimpleInt Nothing ])
    equal [ Required "0" ] $ validate unit (makeTestAction [ SimpleString Nothing ])
    equal [ Required "0._1" ] $ validate unit (makeTestAction [ SimpleTuple (Tuple (SimpleInt Nothing) (SimpleInt (Just 5))) ])
    equal [ Required "0._2" ] $ validate unit (makeTestAction [ SimpleTuple (Tuple (SimpleInt (Just 5)) (SimpleInt Nothing)) ])
    equal [ Required "0.2" ] $ validate unit (makeTestAction [ SimpleArray SimpleIntSchema [ SimpleInt (Just 5)
                                                                                           , SimpleInt (Just 6)
                                                                                           , SimpleInt Nothing
                                                                                           , SimpleInt (Just 7)
                                                                                           ]
                                                             ])
    equal
      [ Required "0.name"
      , Required "1.test"
      ]
      (let objectSchema = SimpleObjectSchema [ Tuple "name" SimpleStringSchema
                                             , Tuple "test" SimpleIntSchema
                                             ]
       in validate unit (makeTestAction [ SimpleObject objectSchema  [ Tuple "name" (SimpleString Nothing)
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
                                       , simulatorWalletBalance: Ada { getAda: 10 }
                                       }
    , functionSchema: FunctionSchema
                        { functionName: Fn "test"
                        , argumentSchema: arguments
                        }
    }
