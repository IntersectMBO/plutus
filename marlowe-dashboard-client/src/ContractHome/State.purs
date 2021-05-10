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
import Marlowe.Extended (TemplateContent(..), fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.PAB (PlutusAppId(..), MarloweData, MarloweParams, History(..))
import Marlowe.Semantics (ChoiceId(..), Contract, Input(..), Party(..), Slot(..), SlotInterval(..), TransactionInput(..), Token(..))
import Marlowe.Semantics (emptyState) as Semantic
import Plutus.V1.Ledger.Value (CurrencySymbol(..))
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletDetails)
import WalletData.Validation (parsePlutusAppId)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState defaultWalletDetails zero mempty

mkInitialState :: WalletDetails -> Slot -> Map PlutusAppId History -> State
mkInitialState walletDetails currentSlot contracts =
  { status: Running
  , contracts: mapMaybeWithKey (Contract.mkInitialState walletDetails currentSlot) contracts
  , selectedContractIndex: Nothing
  }

handleAction ::
  forall m.
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction OpenTemplateLibraryCard = pure unit -- handled in Play.State

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix

partitionContracts :: Map PlutusAppId Contract.State -> PartitionedContracts
partitionContracts contracts =
  Map.toUnfoldableUnordered contracts
    # map snd
    # partition isContractClosed
    # \{ no, yes } -> { completed: yes, running: no }

-- FIXME: Remove this, only for developing
dummyContracts :: Slot -> (Map PlutusAppId History)
dummyContracts slot =
  catMaybes [ filledContract1 slot, filledContract2 slot, filledContract3 slot ]
    # Map.fromFoldable

filledContract1 :: Slot -> Maybe (Tuple PlutusAppId History)
filledContract1 (Slot currentSlot) =
  let
    templateContent =
      TemplateContent
        { slotContent: mempty
        , valueContent:
            Map.fromFoldable
              [ "Price" /\ fromInt 1500000000
              ]
        }

    mContract = toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) Escrow.fixedTimeoutContract

    contractInstanceId = fromMaybe (PlutusAppId emptyUUID) $ parsePlutusAppId "09e83958-824d-4a9d-9fd3-2f57a4f211a1"
  in
    mContract <#> \contract -> contractInstanceId /\ History (tuple3 dummyMarloweParams (marloweData (Slot currentSlot) contract) mempty)

filledContract2 :: Slot -> Maybe (Tuple PlutusAppId History)
filledContract2 (Slot currentSlot) =
  let
    templateContent =
      TemplateContent
        { slotContent: mempty
        , valueContent:
            Map.fromFoldable
              [ "Collateral amount" /\ fromInt 1000000000
              , "Price" /\ fromInt 500000000
              ]
        }

    transactionInputs =
      [ TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Seller") (Role "Seller") (Token "" "") (fromInt 1000000000)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Buyer") (Role "Buyer") (Token "" "") (fromInt 1000000000)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IDeposit (Role "Seller") (Role "Buyer") (Token "" "") (fromInt 500000000)
          }
      , TransactionInput
          { interval:
              (SlotInterval (Slot currentSlot) (Slot currentSlot))
          , inputs:
              List.singleton
                $ IChoice (ChoiceId "Report problem" (Role "Buyer")) (fromInt 1)
          }
      ]

    mContract = toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) EscrowWithCollateral.fixedTimeoutContract

    contractInstanceId = fromMaybe (PlutusAppId emptyUUID) $ parsePlutusAppId "59f292a0-3cd8-431c-8384-ea67583c1489"
  in
    mContract <#> \contract -> contractInstanceId /\ History (tuple3 dummyMarloweParams (marloweData (Slot currentSlot) contract) transactionInputs)

filledContract3 :: Slot -> Maybe (Tuple PlutusAppId History)
filledContract3 (Slot currentSlot) =
  let
    templateContent =
      TemplateContent
        { slotContent: mempty
        , valueContent:
            Map.fromFoldable
              [ "Discounted price" /\ fromInt 1000000000
              , "Notional" /\ fromInt 1500000000
              ]
        }

    mContract = toCore $ fillTemplate templateContent $ resolveRelativeTimes (Slot currentSlot) ZeroCouponBond.fixedTimeoutContract

    contractInstanceId = fromMaybe (PlutusAppId emptyUUID) $ parsePlutusAppId "8242d217-6f7c-4a70-9b18-233a82d089aa"
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
  , marloweState: Semantic.emptyState currentSlot
  }
