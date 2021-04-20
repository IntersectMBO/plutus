module ContractHome.State
  ( dummyState
  , mkInitialState
  , handleAction
  , partitionContracts
  -- FIXME: Remove this, only for developing
  , dummyContracts
  ) where

import Prelude
import Contract.State (applyTimeout, applyTx, isContractClosed)
import Contract.State (mkInitialState) as Contract
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
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\))
import Data.UUID (emptyUUID)
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
import Halogen (HalogenM, modify_)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (TemplateContent(..), fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Semantics (Input(..), Party(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..))
import Types (ContractInstanceId(..))
import WalletData.Validation (parseContractInstanceId)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: Map ContractInstanceId Contract.State -> State
mkInitialState contracts =
  { status: Running
  , contracts
  , selectedContractIndex: Nothing
  }

handleAction ::
  forall m.
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction OpenTemplateLibraryCard = pure unit -- handled in Play.State

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix

-- FIXME: probably get rid of this action and take care of this in MainFrame.handleQuery
handleAction (AdvanceTimedOutContracts currentSlot) =
  modify_
    $ over
        (_contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout == Just currentSlot))
        (applyTimeout currentSlot)

partitionContracts :: Map ContractInstanceId Contract.State -> PartitionedContracts
partitionContracts contracts =
  Map.toUnfoldableUnordered contracts
    # map snd
    # Array.partition isContractClosed
    # \{ no, yes } -> { completed: yes, running: no }

-- FIXME: Remove this, only for developing
dummyContracts :: Slot -> (Map ContractInstanceId Contract.State)
dummyContracts slot =
  catMaybes [ filledContract1 slot, filledContract2 slot, filledContract3 slot ]
    -- FIXME: only to have multiple contracts, remove.
    
    -- # (bindFlipped $ Array.replicate 10)
    
    -- # Array.mapWithIndex (\ix contract -> (show ix) /\ contract)
    
    # map (\contract -> contract.contractInstanceId /\ contract)
    # Map.fromFoldable

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

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "09e83958-824d-4a9d-9fd3-2f57a4f211a1"
  in
    mContract <#> \contract -> Contract.mkInitialState contractInstanceId zero Escrow.metaData participants (Just $ Role "Buyer") contract

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

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "59f292a0-3cd8-431c-8384-ea67583c1489"

    nextState' :: Contract.State -> TransactionInput -> Contract.State
    nextState' state txInput = applyTx (Slot currentSlot) txInput state
  contract <- toCore $ fillTemplate templateContent EscrowWithCollateral.extendedContract
  initialState <- pure $ Contract.mkInitialState contractInstanceId zero EscrowWithCollateral.metaData participants (Just $ Role "Buyer") contract
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

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "8242d217-6f7c-4a70-9b18-233a82d089aa"
  contract <- toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) ZeroCouponBond.extendedContract
  pure $ Contract.mkInitialState contractInstanceId zero ZeroCouponBond.metaData participants (Just $ Role "Guarantor") contract
