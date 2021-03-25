module ContractHome.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Contract.Lenses (_executionState)
import Contract.State (mkInitialState) as Contract
import Contract.Types (State) as Contract
import ContractHome.Lenses (_selectedContractIndex, _status)
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
        [ (Role "Arbiter") /\ Just "Alice"
        , (Role "Buyer") /\ Just "Bob"
        , (Role "Seller") /\ Nothing
        ]

    mContract = toCore $ fillTemplate templateContent Contract1.extendedContract
  in
    mContract <#> \contract -> Contract.mkInitialState "dummy contract 1" zero contract Contract1.metaData participants (Just $ Role "Buyer")

filledContract2 :: Maybe Contract.State
filledContract2 = do
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Initial exchange deadline" /\ fromInt 10
              , "Maturity exchange deadline" /\ fromInt 12
              ]
        , valueContent:
            Map.fromFoldable
              [ "Discounted price" /\ fromInt 1000
              , "Notional" /\ fromInt 1500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "Investor") /\ Just "Alice"
        , (Role "Issuer") /\ Just "Bob"
        ]

    transactions =
      [ TransactionInput
          { interval:
              (SlotInterval (Slot $ fromInt 0) (Slot $ fromInt 0))
          , inputs:
              List.singleton
                $ IDeposit (Role "Investor") (Role "Investor") (Token "" "") (fromInt 1000)
          }
      ]

    nextState' :: Contract.State -> TransactionInput -> Contract.State
    nextState' state txInput = over _executionState (flip nextState $ txInput) state
  contract <- toCore $ fillTemplate templateContent Contract3.extendedContract
  initialState <- pure $ Contract.mkInitialState "dummy contract 2" zero contract Contract3.metaData participants (Just $ Role "alice")
  pure $ foldl nextState' initialState transactions

defaultState :: State
defaultState =
  { status: Running
  , contracts: catMaybes [ filledContract1, filledContract2 ]
  -- , contracts: mempty
  , selectedContractIndex: Nothing
  }

handleAction ::
  forall m slots msg.
  Action -> HalogenM State Action slots msg m Unit
handleAction ToggleTemplateLibraryCard = pure unit -- handled in Play

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix
