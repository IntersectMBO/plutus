module TypesTests
       ( all
       ) where

import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Playground.API (Fn(..), FunctionSchema(..))
import Prelude (discard, unit, ($))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Types (Action(..), MockWallet(..), SimpleArgument(..), ValidationError(..), validate)
import Wallet.Emulator.Types (Wallet(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
all =
  suite "Types" do
    validateTests

validateTests :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
validateTests = do
  test "Validation errors" do
    equal [] $ validate unit (Wait {blocks: 1})
    equal [] $ validate unit (makeTestAction [ SimpleInt (Just 5) ])
    equal [] $ validate unit (makeTestAction [ SimpleString (Just "TEST") ])
    equal [] $ validate unit (makeTestAction [ SimpleObject [] ])
    --
    equal [ Unsupported "0" ] $ validate unit (makeTestAction [ Unknowable ])
    equal [ Required "0" ] $ validate unit (makeTestAction [ SimpleInt Nothing ])
    equal [ Required "0" ] $ validate unit (makeTestAction [ SimpleString Nothing ])
    equal
      [ Required "0.name"
      , Required "1.test"
      ]
      (validate unit (makeTestAction [ SimpleObject [ Tuple "name" (SimpleString Nothing)
                                                    , Tuple "test" (SimpleInt (Just 5))
                                                    ]
                                     , SimpleObject [ Tuple "name" (SimpleString (Just "test"))
                                                    , Tuple "test" (SimpleInt Nothing)
                                                    ]
                                     ]))

makeTestAction :: Array SimpleArgument -> Action
makeTestAction arguments =
  Action
    { mockWallet: MockWallet { wallet: Wallet { getWallet: 1 }, balance: 10 }
    , functionSchema: FunctionSchema
                        { functionName: Fn "test"
                        , argumentSchema: arguments
                        }
    }
