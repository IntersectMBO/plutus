module ContractHome.State
  ( defaultState
  , handleAction
  , partitionContracts
  -- FIXME: Remove this, only for developing
  , loadExistingContracts
  ) where

import Prelude
import Contract.State (applyTimeout, applyTx, isContractClosed)
import Contract.State (mkInitialState) as Contract
import Contract.Types (ContractId)
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _selectedContractIndex, _status)
import ContractHome.Types (Action(..), ContractStatus(..), State, PartitionedContracts)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.BigInteger (fromInt)
import Data.Foldable (foldl)
import Data.Lens (assign, filtered, over, traversed)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
import Halogen (HalogenM, modify_)
import Marlowe.Extended (TemplateContent(..), fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Semantics (Input(..), Party(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..))
import Marlowe.Slot (currentSlot)

-- FIXME: debug purposes only, delete later
filledContract1 :: Slot -> Maybe Contract.State
filledContract1 (Slot currentSlot) =
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Buyer's deposit timeout" /\ (currentSlot + fromInt 60)
              , "Buyer's dispute timeout" /\ (currentSlot + fromInt 120)
              , "Seller's response timeout" /\ (currentSlot + fromInt 180)
              , "Timeout for arbitrage" /\ (currentSlot + fromInt 340)
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

    mContract = toCore $ fillTemplate templateContent Escrow.extendedContract
  in
    mContract <#> \contract -> Contract.mkInitialState "dummy contract 1" zero Escrow.metaData participants (Just $ Role "Buyer") contract

filledContract2 :: Slot -> Maybe Contract.State
filledContract2 (Slot currentSlot) = do
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Collateral deposit by seller timeout" /\ (currentSlot + fromInt 60)
              , "Deposit of collateral by buyer timeout" /\ (currentSlot + fromInt 80)
              , "Deposit of price by buyer timeout" /\ (currentSlot + fromInt 100)
              , "Dispute by buyer timeout" /\ (currentSlot + fromInt 120)
              , "Seller's response timeout" /\ (currentSlot + fromInt 140)
              ]
        , valueContent:
            Map.fromFoldable
              [ "Collateral amount" /\ fromInt 1000
              , "Price" /\ fromInt 500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "Buyer") /\ Just "Alice"
        , (Role "Seller") /\ Just "Bob"
        ]

    transactions =
      [ TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Seller") (Role "Seller") (Token "" "") (fromInt 1000)
          }
      ]

    nextState' :: Contract.State -> TransactionInput -> Contract.State
    nextState' state txInput = applyTx (Slot currentSlot) txInput state
  contract <- toCore $ fillTemplate templateContent EscrowWithCollateral.extendedContract
  initialState <- pure $ Contract.mkInitialState "dummy contract 2" zero EscrowWithCollateral.metaData participants (Just $ Role "Buyer") contract
  pure $ foldl nextState' initialState transactions

filledContract3 :: Slot -> Maybe Contract.State
filledContract3 (Slot currentSlot) = do
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Initial exchange deadline" /\ (currentSlot + fromInt 60)
              , "Maturity exchange deadline" /\ (currentSlot + fromInt 80)
              ]
        , valueContent:
            Map.fromFoldable
              [ "Discounted price" /\ fromInt 1000
              , "Notional" /\ fromInt 1500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "Guarantor") /\ Just "Alice"
        , (Role "Investor") /\ Just "Bob"
        ]
  contract <- toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) ZeroCouponBond.extendedContract
  pure $ Contract.mkInitialState "dummy contract 3" zero ZeroCouponBond.metaData participants (Just $ Role "Guarantor") contract

loadExistingContracts :: Effect (Map ContractId Contract.State)
loadExistingContracts = do
  slot <- currentSlot
  pure
    $ catMaybes [ filledContract1 slot, filledContract2 slot, filledContract3 slot ]
    # map (\contract -> contract.contractId /\ contract)
    # Map.fromFoldable

partitionContracts :: Map ContractId Contract.State -> PartitionedContracts
partitionContracts contracts =
  Map.toUnfoldableUnordered contracts
    # map snd
    # Array.partition isContractClosed
    # \{ no, yes } -> { completed: yes, running: no }

defaultState :: State
defaultState =
  { status: Running
  , contracts: mempty
  , selectedContractIndex: Nothing
  }

handleAction ::
  forall m slots msg.
  Action -> HalogenM State Action slots msg m Unit
handleAction ToggleTemplateLibraryCard = pure unit -- handled in Play

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix

handleAction (AdvanceTimedOutContracts currentSlot) =
  modify_
    $ over
        (_contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout == Just currentSlot))
        (applyTimeout currentSlot)
