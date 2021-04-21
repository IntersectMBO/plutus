module Play.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.Toast (class Toast)
import Capability.Wallet (class ManageWallet)
import Contract.Lenses (_selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction) as Contract
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (handleAction, mkInitialState) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Array (init, snoc)
import Data.Foldable (for_)
import Data.Lens (assign, filtered, modifying, over, set, use)
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (lastOf)
import Data.Lens.Traversal (traversed)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes(..))
import Data.UUID (emptyUUID)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import MainFrame.Lenses (_screen)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (ContractInstanceId(..))
import Marlowe.Semantics (Slot(..))
import Play.Lenses (_cards, _contractsState, _currentSlot, _menuOpen, _selectedContract, _templateState)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Template.Lenses (_template)
import Template.State (dummyState, handleAction, mkInitialState) as Template
import Template.Types (Action(..), State) as Template
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState defaultWalletDetails mempty (Slot zero) (Minutes zero)
  where
  defaultWalletDetails =
    { walletNickname: mempty
    , contractInstanceId: ContractInstanceId emptyUUID
    , wallet: Wallet zero
    , pubKey: ""
    , pubKeyHash: PubKeyHash ""
    , assets: mempty
    }

-- We initialise the play state using the locally determined currentSlot, but subsequently
-- it will be updated through the websocket to the PAB's currentSlot. The two should always
-- be in sync (if they go out of sync, a toast warning is displayed).
mkInitialState :: WalletDetails -> Map ContractInstanceId Contract.State -> Slot -> Minutes -> State
mkInitialState walletDetails contracts currentSlot timezoneOffset =
  { walletDetails: walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , cards: mempty
  , currentSlot
  , timezoneOffset
  , templateState: Template.dummyState
  , contractsState: ContractHome.mkInitialState contracts
  }

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  Toast m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction PutdownWallet = pure unit -- handled in MainFrame.State (see note [State] in MainFrame.State)

handleAction (SetNewWalletNickname walletNickname) = pure unit -- handled in MainFrame.State (see note [State] in MainFrame.State)

handleAction (SetNewWalletContractId contractId) = pure unit -- handled in MainFrame.State (see note [State] in MainFrame.State)

handleAction (AddNewWallet mTokenName) = pure unit -- handled in MainFrame.State (see note [State] in MainFrame.State)

handleAction ToggleMenu = modifying _menuOpen not

handleAction (SetScreen screen) =
  modify_
    $ set _menuOpen false
    <<< set _cards mempty
    <<< set _screen screen

handleAction (OpenCard card) = modifying _cards $ flip snoc card

handleAction CloseCard = do
  cards <- use _cards
  for_ (init cards) \remainingCards ->
    assign _cards remainingCards

handleAction (SetCurrentSlot slot) = do
  selectedStep <- peruse $ _selectedContract <<< _selectedStep
  modify_
    $ over
        (_contractsState <<< _contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout == Just slot))
        (applyTimeout slot)
    <<< set _currentSlot slot
  selectedStep' <- peruse $ _selectedContract <<< _selectedStep
  when (selectedStep /= selectedStep')
    $ for_ selectedStep'
    $ \step -> toContract $ Contract.handleAction $ Contract.MoveToStep step

handleAction (TemplateAction templateAction) = case templateAction of
  Template.SetTemplate template -> do
    mCurrentTemplate <- peruse (_templateState <<< _template)
    when (mCurrentTemplate /= Just template) $ assign _templateState $ Template.mkInitialState template
    handleAction $ SetScreen TemplateScreen
  Template.OpenTemplateLibraryCard -> handleAction $ OpenCard TemplateLibraryCard
  Template.OpenCreateWalletCard tokenName -> handleAction $ OpenCard $ CreateWalletCard $ Just tokenName
  Template.OpenSetupConfirmationCard -> handleAction $ OpenCard ContractSetupConfirmationCard
  Template.CloseSetupConfirmationCard -> do
    cards <- use _cards
    case lastOf traversed cards of
      Just ContractSetupConfirmationCard -> handleAction CloseCard
      _ -> pure unit
  _ -> toTemplate $ Template.handleAction templateAction

handleAction (ContractHomeAction contractHomeAction) = case contractHomeAction of
  ContractHome.OpenTemplateLibraryCard -> handleAction $ OpenCard TemplateLibraryCard
  a@(ContractHome.OpenContract _) -> do
    toContractHome $ ContractHome.handleAction a
    handleAction $ OpenCard ContractCard
    toContract $ Contract.handleAction Contract.CarouselOpened
  _ -> toContractHome $ ContractHome.handleAction contractHomeAction

handleAction (ContractAction contractAction) = case contractAction of
  Contract.AskConfirmation action -> handleAction $ OpenCard $ ContractActionConfirmationCard action
  Contract.ConfirmAction action -> do
    void $ toContract $ Contract.handleAction $ Contract.ConfirmAction action
    handleAction CloseCard -- TODO: guard against closing the wrong card
  Contract.CancelConfirmation -> handleAction CloseCard -- TODO: guard against closing the wrong card
  _ -> toContract $ Contract.handleAction contractAction

------------------------------------------------------------
toTemplate ::
  forall m msg slots.
  Functor m =>
  HalogenM Template.State Template.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toTemplate = mapSubmodule _templateState TemplateAction

toContractHome ::
  forall m msg slots.
  Functor m =>
  HalogenM ContractHome.State ContractHome.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContractHome = mapSubmodule _contractsState ContractHomeAction

-- see note [dummyState] in MainFrame.State
toContract ::
  forall m msg slots.
  Functor m =>
  HalogenM Contract.State Contract.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toContract = mapMaybeSubmodule _selectedContract ContractAction Contract.dummyState
