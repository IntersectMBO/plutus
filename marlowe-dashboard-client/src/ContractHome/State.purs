module ContractHome.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Contract.Lenses (_executionState)
import Contract.State (mkInitialState) as Contract
import Contract.Types (State) as Contract
import ContractHome.Lenses (_selectedContract, _status)
import ContractHome.Types (ContractStatus(..), State, Action(..))
import Data.Array (catMaybes)
import Data.BigInteger (fromInt)
import Data.Foldable (foldl)
import Data.Lens (assign, over)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Halogen (HalogenM)
import Marlowe.Execution (nextState)
import Marlowe.Extended (TemplateContent(..), fillTemplate, toCore)
import Marlowe.Market.Contract1 as Contract1
import Marlowe.Market.Contract3 as Contract3
import Marlowe.Semantics (Input(..), Party(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..))

-- FIXME: debug purposes only, delete later
filledContract1 :: Maybe Contract.State
filledContract1 =
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Buyer's deposit timeout" /\ fromInt 10
              , "Buyer's dispute timeout" /\ fromInt 12
              , "Seller's response timeout" /\ fromInt 15
              , "Timeout for arbitrage" /\ fromInt 17
              ]
        , valueContent:
            Map.fromFoldable
              [ "Price" /\ fromInt 1500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "Arbiter") /\ Just "Alice user"
        , (Role "Buyer") /\ Just "Bob user"
        , (Role "Seller") /\ Nothing
        ]

    mContract = toCore $ fillTemplate templateContent Contract1.extendedContract
  in
    mContract <#> \contract -> Contract.mkInitialState zero contract Contract1.metaData participants (Just $ Role "Arbiter")

filledContract2 :: Maybe Contract.State
filledContract2 = do
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "aliceTimeout" /\ fromInt 10
              , "arbitrageTimeout" /\ fromInt 12
              , "bobTimeout" /\ fromInt 15
              , "depositSlot" /\ fromInt 17
              ]
        , valueContent:
            Map.fromFoldable
              [ "amount" /\ fromInt 1500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "alice") /\ Just "Alice user"
        , (Role "bob") /\ Just "Bob user"
        , (Role "carol") /\ Nothing
        ]

    transactions =
      [ TransactionInput
          { interval:
              (SlotInterval (Slot $ fromInt 40000) (Slot $ fromInt 40060))
          , inputs:
              List.singleton
                $ IDeposit (Role "alice") (Role "alice") (Token "" "") (fromInt 1500)
          }
      ]

    nextState' :: Contract.State -> TransactionInput -> Contract.State
    nextState' state txInput = over _executionState (flip nextState $ txInput) state
  contract <- toCore $ fillTemplate templateContent Contract3.extendedContract
  initialState <- pure $ Contract.mkInitialState zero contract Contract3.metaData participants (Just $ Role "alice")
  pure $ foldl nextState' initialState transactions

defaultState :: State
defaultState =
  { status: Running
  , contracts: catMaybes [ filledContract1, filledContract2 ]
  -- , contracts: mempty
  , selectedContract: Nothing
  }

handleAction ::
  forall m slots msg.
  Action -> HalogenM State Action slots msg m Unit
handleAction ToggleTemplateLibraryCard = pure unit -- handled in Play

handleAction (SelectView view) = assign _status view

handleAction (OpenContract contract) = assign _selectedContract $ Just contract
