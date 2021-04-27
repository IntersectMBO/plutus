module ContractHome.State
  ( dummyState
  , mkInitialState
  , handleAction
  , partitionContracts
  , dummyContracts
  ) where

import Prelude
import Contract.State (isContractClosed)
import Contract.State (mkInitialState) as Contract
import Contract.Types (State) as Contract
import ContractHome.Lenses (_selectedContractIndex, _status)
import ContractHome.Types (Action(..), ContractStatus(..), State, PartitionedContracts)
import Data.Array (catMaybes, partition)
import Data.BigInteger (fromInt)
import Data.Lens (assign)
import Data.List (singleton) as List
import Data.Map (Map, mapMaybeWithKey)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple, snd)
import Data.Tuple.Nested ((/\), tuple3)
import Data.UUID (emptyUUID)
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (ContractInstanceId(..), MarloweData, MarloweParams, History(..))
import Marlowe.Extended (TemplateContent(..), fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Semantics (ChoiceId(..), Contract, Input(..), Party(..), Slot(..), SlotInterval(..), TransactionInput(..), Token(..))
import Marlowe.Semantics (State(..)) as Semantic
import Plutus.V1.Ledger.Value (CurrencySymbol(..))
import WalletData.Validation (parseContractInstanceId)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState zero mempty

mkInitialState :: Slot -> Map ContractInstanceId History -> State
mkInitialState currentSlot contracts =
  { status: Running
  , contracts: mapMaybeWithKey (Contract.mkInitialState currentSlot) contracts
  , selectedContractIndex: Nothing
  }

handleAction ::
  forall m.
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction OpenTemplateLibraryCard = pure unit -- handled in Play.State

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix

partitionContracts :: Map ContractInstanceId Contract.State -> PartitionedContracts
partitionContracts contracts =
  Map.toUnfoldableUnordered contracts
    # map snd
    # partition isContractClosed
    # \{ no, yes } -> { completed: yes, running: no }

-- FIXME: Remove this, only for developing
dummyContracts :: Slot -> (Map ContractInstanceId History)
dummyContracts slot =
  catMaybes [ filledContract1 slot, filledContract2 slot, filledContract3 slot ]
    # Map.fromFoldable

filledContract1 :: Slot -> Maybe (Tuple ContractInstanceId History)
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

    mContract = toCore $ fillTemplate templateContent Escrow.extendedContract

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "09e83958-824d-4a9d-9fd3-2f57a4f211a1"
  in
    mContract <#> \contract -> contractInstanceId /\ History (tuple3 dummyMarloweParams (marloweData (Slot currentSlot) contract) mempty)

filledContract2 :: Slot -> Maybe (Tuple ContractInstanceId History)
filledContract2 (Slot currentSlot) =
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

    transactionInputs =
      [ TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Seller") (Role "Seller") (Token "" "") (fromInt 1000)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Buyer") (Role "Buyer") (Token "" "") (fromInt 1000)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Seller") (Role "Buyer") (Token "" "") (fromInt 500)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IChoice (ChoiceId "Report problem" (Role "Buyer")) (fromInt 1)
          }
      ]

    mContract = toCore $ fillTemplate templateContent EscrowWithCollateral.extendedContract

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "59f292a0-3cd8-431c-8384-ea67583c1489"
  in
    mContract <#> \contract -> contractInstanceId /\ History (tuple3 dummyMarloweParams (marloweData (Slot currentSlot) contract) transactionInputs)

filledContract3 :: Slot -> Maybe (Tuple ContractInstanceId History)
filledContract3 (Slot currentSlot) =
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

    mContract = toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) ZeroCouponBond.extendedContract

    contractInstanceId = fromMaybe (ContractInstanceId emptyUUID) $ parseContractInstanceId "8242d217-6f7c-4a70-9b18-233a82d089aa"
  in
    mContract <#> \contract -> contractInstanceId /\ History (tuple3 dummyMarloweParams (marloweData (Slot currentSlot) contract) mempty)

dummyMarloweParams :: MarloweParams
dummyMarloweParams =
  { rolePayoutValidatorHash: ""
  , rolesCurrency: CurrencySymbol { unCurrencySymbol: "" }
  }

marloweData :: Slot -> Contract -> MarloweData
marloweData currentSlot contract =
  { marloweContract: contract
  , marloweState:
      Semantic.State
        { accounts: mempty
        , choices: mempty
        , boundValues: mempty
        , minSlot: currentSlot
        }
  }
