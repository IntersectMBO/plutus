module Play.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createContract, lookupWalletInfo)
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction, mkInitialState) as Contract
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (handleAction, mkInitialState) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Array (init, snoc)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, filtered, modifying, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Traversal (traversed)
import Data.Map (Map, insert, lookup, mapMaybe)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes(..))
import Data.Tuple.Nested (tuple3)
import Data.UUID (genUUID)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import LocalStorage (setItem)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (PlutusAppId(..), History(..))
import Marlowe.Semantics (Slot(..))
import Marlowe.Semantics (State(..)) as Semantic
import Network.RemoteData (RemoteData(..), fromEither)
import Play.Lenses (_allContracts, _cards, _contractsState, _menuOpen, _newWalletCompanionAppIdString, _newWalletInfo, _newWalletNickname, _screen, _selectedContract, _templateState, _walletDetails, _walletLibrary)
import Play.Types (Action(..), Card(..), Inputs, Screen(..), State)
import Plutus.V1.Ledger.Value (CurrencySymbol(..))
import StaticData (walletLibraryLocalStorageKey)
import Template.Lenses (_extendedContract, _roleWallets, _template, _templateContent)
import Template.State (dummyState, handleAction, mkInitialState) as Template
import Template.State (instantiateExtendedContract)
import Template.Types (Action(..), State) as Template
import Toast.Types (ajaxErrorToast, errorToast, successToast)
import WalletData.Lenses (_pubKeyHash, _walletInfo)
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (parsePlutusAppId)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty defaultWalletDetails mempty (Slot zero) (Minutes zero)

mkInitialState :: WalletLibrary -> WalletDetails -> Map PlutusAppId History -> Slot -> Minutes -> State
mkInitialState walletLibrary walletDetails contracts currentSlot timezoneOffset =
  { walletLibrary
  , walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , cards: mempty
  , newWalletNickname: mempty
  , newWalletCompanionAppIdString: mempty
  , newWalletInfo: NotAsked
  , timezoneOffset
  , templateState: Template.dummyState
  , contractsState: ContractHome.mkInitialState walletDetails currentSlot contracts
  }

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageContract m =>
  ManageMarlowe m =>
  Toast m =>
  Inputs -> Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction _ PutdownWallet = do
  walletLibrary <- use _walletLibrary
  walletDetails <- use _walletDetails
  runningContracts <- use _allContracts
  callMainFrameAction $ MainFrame.EnterPickupState walletLibrary walletDetails runningContracts

handleAction _ (SetNewWalletNickname walletNickname) = assign _newWalletNickname walletNickname

handleAction _ (SetNewWalletCompanionAppIdString companionAppIdString) = do
  modify_
    $ set _newWalletCompanionAppIdString companionAppIdString
    <<< set _newWalletInfo NotAsked
  -- if this is a valid contract ID ...
  for_ (parsePlutusAppId companionAppIdString) \companionAppId -> do
    assign _newWalletInfo Loading
    -- .. lookup wallet info
    ajaxWalletInfo <- lookupWalletInfo companionAppId
    assign _newWalletInfo $ fromEither ajaxWalletInfo

handleAction inputs (SaveNewWallet mTokenName) = do
  oldWalletLibrary <- use _walletLibrary
  newWalletNickname <- use _newWalletNickname
  newWalletCompanionAppIdString <- use _newWalletCompanionAppIdString
  newWalletInfo <- use _newWalletInfo
  let
    newWalletCompanionAppId = parsePlutusAppId newWalletCompanionAppIdString
  case newWalletInfo, newWalletCompanionAppId of
    Success walletInfo, Just companionAppId -> do
      handleAction inputs CloseCard
      let
        walletDetails =
          { walletNickname: newWalletNickname
          , companionAppId
          , walletInfo
          , assets: mempty
          }
      modify_
        $ over _walletLibrary (insert newWalletNickname walletDetails)
        <<< set _newWalletNickname mempty
        <<< set _newWalletCompanionAppIdString mempty
        <<< set _newWalletInfo NotAsked
      newWalletLibrary <- use _walletLibrary
      liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWalletLibrary
    -- TODO: show error feedback to the user (just to be safe - but this should never happen, because
    -- the button to save a new wallet should be disabled in this case)
    _, _ -> pure unit

handleAction _ ToggleMenu = modifying _menuOpen not

handleAction _ (SetScreen screen) =
  modify_
    $ set _menuOpen false
    <<< set _cards mempty
    <<< set _screen screen

handleAction _ (OpenCard card) =
  modify_
    $ over _cards (flip snoc card)
    <<< set _menuOpen false

handleAction _ CloseCard = do
  cards <- use _cards
  for_ (init cards) \remainingCards ->
    assign _cards remainingCards

handleAction { currentSlot } AdvanceTimedoutSteps = do
  walletDetails <- use _walletDetails
  selectedStep <- peruse $ _selectedContract <<< _selectedStep
  modify_
    $ over
        (_contractsState <<< _contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout == Just currentSlot))
        (applyTimeout currentSlot)
  selectedStep' <- peruse $ _selectedContract <<< _selectedStep
  when (selectedStep /= selectedStep')
    $ for_ selectedStep'
    $ \step ->
        let
          contractInputs = { currentSlot, walletDetails }
        in
          toContract $ Contract.handleAction contractInputs $ Contract.MoveToStep step

-- TODO: we have to handle quite a lot of submodule actions here (mainly just because of the cards),
-- so there's probably a better way of structuring this - perhaps making cards work more like toasts
handleAction inputs@{ currentSlot } (TemplateAction templateAction) = case templateAction of
  Template.SetTemplate template -> do
    mCurrentTemplate <- peruse (_templateState <<< _template)
    when (mCurrentTemplate /= Just template) $ assign _templateState $ Template.mkInitialState template
    handleAction inputs $ SetScreen TemplateScreen
  Template.OpenTemplateLibraryCard -> handleAction inputs $ OpenCard TemplateLibraryCard
  Template.OpenCreateWalletCard tokenName -> handleAction inputs $ OpenCard $ SaveWalletCard $ Just tokenName
  Template.OpenSetupConfirmationCard -> handleAction inputs $ OpenCard ContractSetupConfirmationCard
  Template.CloseSetupConfirmationCard -> handleAction inputs CloseCard -- TODO: guard against closing the wrong card
  Template.StartContract -> do
    extendedContract <- use (_templateState <<< _template <<< _extendedContract)
    templateContent <- use (_templateState <<< _templateContent)
    case instantiateExtendedContract currentSlot extendedContract templateContent of
      Nothing -> addToast $ errorToast "Failed to instantiate contract." $ Just "Something went wrong when trying to instantiate a contract from this template using the parameters you specified."
      Just contract -> do
        -- the user enters wallet nicknames for roles; here we convert these into pubKeyHashes
        walletDetails <- use _walletDetails
        walletLibrary <- use _walletLibrary
        roleWallets <- use (_templateState <<< _roleWallets)
        let
          roles = mapMaybe (\walletNickname -> view (_walletInfo <<< _pubKeyHash) <$> lookup walletNickname walletLibrary) roleWallets
        ajaxCreateContract <- createContract walletDetails roles contract
        case ajaxCreateContract of
          -- TODO: make this error message more informative
          Left ajaxError -> addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
          _ -> do
            -- FIXME: If the user gives themselves a role in this contract, their WalletCompanion contract
            -- should notice, and that will trigger all the other necessary updates. But if they don't, we
            -- should create a WalletFollower contract manually here.
            handleAction inputs $ SetScreen ContractsScreen
            addToast $ successToast "Contract started."
            -- FIXME: until we get contracts running properly in the PAB, we just fake the contract here locally
            uuid <- liftEffect genUUID
            let
              contractInstanceId = PlutusAppId uuid

              marloweParams = { rolePayoutValidatorHash: mempty, rolesCurrency: CurrencySymbol { unCurrencySymbol: "" } }

              marloweState = Semantic.State { accounts: mempty, choices: mempty, boundValues: mempty, minSlot: zero }

              marloweData = { marloweContract: contract, marloweState }

              history = History $ tuple3 marloweParams marloweData mempty

              mContractState = Contract.mkInitialState walletDetails currentSlot contractInstanceId history
            for_ mContractState \contractState -> do
              modifying _allContracts $ insert contractInstanceId contractState
              handleAction inputs $ ContractHomeAction $ ContractHome.OpenContract contractInstanceId
  _ -> toTemplate $ Template.handleAction templateAction

handleAction inputs (ContractHomeAction contractHomeAction) = case contractHomeAction of
  ContractHome.OpenTemplateLibraryCard -> handleAction inputs $ OpenCard TemplateLibraryCard
  a@(ContractHome.OpenContract _) -> do
    walletDetails <- use _walletDetails
    toContractHome $ ContractHome.handleAction a
    handleAction inputs $ OpenCard ContractCard
  _ -> toContractHome $ ContractHome.handleAction contractHomeAction

handleAction inputs@{ currentSlot } (ContractAction contractAction) = do
  walletDetails <- use _walletDetails
  let
    contractInputs = { currentSlot, walletDetails }
  case contractAction of
    Contract.AskConfirmation action -> handleAction inputs $ OpenCard $ ContractActionConfirmationCard action
    Contract.ConfirmAction action -> do
      void $ toContract $ Contract.handleAction contractInputs contractAction
      handleAction inputs CloseCard -- TODO: guard against closing the wrong card
    Contract.CancelConfirmation -> handleAction inputs CloseCard -- TODO: guard against closing the wrong card
    _ -> toContract $ Contract.handleAction contractInputs contractAction

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
