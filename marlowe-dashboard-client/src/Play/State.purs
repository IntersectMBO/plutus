module Play.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.LocalStorage (class ManageLocalStorage, getCurrentWalletDetails, getWalletLibrary)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe.Dummy (class ManageMarlowe, createContract, followContract, getFollowerApps, lookupWalletInfo, subscribeToPlutusApp)
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_marloweParams, _selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction, mkInitialState, updateState) as Contract
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (handleAction, mkInitialState) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Data.Array (difference, init, snoc)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, filtered, modifying, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Traversal (traversed)
import Data.List (toUnfoldable) as List
import Data.Map (Map, insert, keys, lookup, mapMaybe, toUnfoldable, values)
import Data.Maybe (Maybe(..))
import Data.Set (toUnfoldable) as Set
import Data.Time.Duration (Minutes(..))
import Data.Traversable (for)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (emptyUUID)
import Debug.Trace (spy)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import InputField.Lenses (_value)
import InputField.State (handleAction, initialState) as InputField
import InputField.Types (Action(..), State) as InputField
import LocalStorage (setItem)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (ContractHistory(..), PlutusAppId(..))
import Marlowe.Semantics (Slot(..))
import Network.RemoteData (RemoteData(..), fromEither)
import Play.Lenses (_allContracts, _cards, _contractsState, _menuOpen, _remoteWalletInfo, _screen, _selectedContract, _templateState, _walletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput)
import Play.Types (Action(..), Card(..), Input, Screen(..), State)
import StaticData (walletLibraryLocalStorageKey)
import Template.Lenses (_extendedContract, _roleWalletInputs, _template, _templateContent)
import Template.State (dummyState, handleAction, mkInitialState) as Template
import Template.State (instantiateExtendedContract)
import Template.Types (Action(..), State) as Template
import Toast.Types (ajaxErrorToast, decodedAjaxErrorToast, errorToast, successToast)
import WalletData.Lenses (_companionAppId, _pubKeyHash, _walletInfo)
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, parsePlutusAppId, walletIdError, walletNicknameError)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty defaultWalletDetails mempty (Slot zero) (Minutes zero)

mkInitialState :: WalletLibrary -> WalletDetails -> Map PlutusAppId ContractHistory -> Slot -> Minutes -> State
mkInitialState walletLibrary walletDetails contracts currentSlot timezoneOffset =
  { walletLibrary
  , walletDetails
  , menuOpen: false
  , screen: ContractsScreen
  , cards: mempty
  , walletNicknameInput: InputField.initialState
  , walletIdInput: InputField.initialState
  , remoteWalletInfo: NotAsked
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
  ManageLocalStorage m =>
  ManageMarlowe m =>
  Toast m =>
  Input -> Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction _ PutdownWallet = do
  walletLibrary <- use _walletLibrary
  walletDetails <- use _walletDetails
  runningContracts <- use _allContracts
  callMainFrameAction $ MainFrame.EnterPickupState walletLibrary walletDetails runningContracts

handleAction _ (WalletNicknameInputAction inputFieldAction) = toWalletNicknameInput $ InputField.handleAction inputFieldAction

handleAction input (WalletIdInputAction inputFieldAction) = do
  case inputFieldAction of
    InputField.SetValue walletIdString -> do
      -- note we handle the inputFieldAction _first_ so that the InputField value is set - otherwise the
      -- validation feedback is wrong while the rest is happening
      toWalletIdInput $ InputField.handleAction inputFieldAction
      handleAction input $ SetRemoteWalletInfo NotAsked
      -- if this is a valid contract ID ...
      for_ (parsePlutusAppId walletIdString) \walletId -> do
        handleAction input $ SetRemoteWalletInfo Loading
        -- .. lookup wallet info
        ajaxWalletInfo <- lookupWalletInfo walletId
        handleAction input $ SetRemoteWalletInfo $ fromEither ajaxWalletInfo
    _ -> toWalletIdInput $ InputField.handleAction inputFieldAction

handleAction input (SetRemoteWalletInfo remoteWalletInfo) = do
  assign _remoteWalletInfo remoteWalletInfo
  walletLibrary <- use _walletLibrary
  handleAction input $ WalletIdInputAction $ InputField.SetValidator $ walletIdError remoteWalletInfo walletLibrary

handleAction input (SaveNewWallet mTokenName) = do
  oldWalletLibrary <- use _walletLibrary
  walletNickname <- use (_walletNicknameInput <<< _value)
  walletIdString <- use (_walletIdInput <<< _value)
  remoteWalletInfo <- use _remoteWalletInfo
  let
    mWalletId = parsePlutusAppId walletIdString
  case remoteWalletInfo, mWalletId of
    Success walletInfo, Just walletId -> do
      handleAction input CloseCard
      let
        -- note the empty properties are fine for saved wallets - these will be fetched if/when
        -- this wallet is picked up
        walletDetails =
          { walletNickname
          , companionAppId: walletId
          , marloweAppId: PlutusAppId emptyUUID
          , walletInfo
          , assets: mempty
          }
      modifying _walletLibrary (insert walletNickname walletDetails)
      newWalletLibrary <- use _walletLibrary
      liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWalletLibrary
      -- if a tokenName was also passed, we need to update the contract setup data
      for_ mTokenName \tokenName -> do
        handleAction input $ TemplateAction $ Template.UpdateRoleWalletValidators newWalletLibrary
        handleAction input $ TemplateAction $ Template.RoleWalletInputAction tokenName $ InputField.SetValue walletNickname
    -- TODO: show error feedback to the user (just to be safe - but this should never happen, because
    -- the button to save a new wallet should be disabled in this case)
    _, _ -> pure unit

handleAction _ ToggleMenu = modifying _menuOpen not

handleAction _ (SetScreen screen) =
  modify_
    $ set _menuOpen false
    <<< set _cards mempty
    <<< set _screen screen

handleAction input (OpenCard card) = do
  case card of
    SaveWalletCard _ -> do
      walletLibrary <- use _walletLibrary
      assign _remoteWalletInfo NotAsked
      handleAction input $ WalletNicknameInputAction InputField.Reset
      handleAction input $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
      handleAction input $ WalletIdInputAction $ InputField.SetValidator $ walletIdError NotAsked walletLibrary
    _ -> pure unit
  modify_
    $ over _cards (flip snoc card)
    <<< set _menuOpen false

handleAction _ CloseCard = do
  cards <- use _cards
  for_ (init cards) \remainingCards ->
    assign _cards remainingCards

-- FIXME: until the PAB is working, we get the latest data from local storage here (this action
-- is called every second)
handleAction { currentSlot } UpdateFromStorage = do
  let
    foo = spy "update called" "yay!"
  walletDetails <- use _walletDetails
  storedWalletLibrary <- getWalletLibrary
  mStoredWalletDetails <- getCurrentWalletDetails
  assign _walletLibrary storedWalletLibrary
  for_ mStoredWalletDetails \storedWalletDetails ->
    when (view _companionAppId walletDetails == view _companionAppId storedWalletDetails)
      $ assign _walletDetails storedWalletDetails
  updatedWalletDetails <- use _walletDetails
  ajaxFollowerApps <- getFollowerApps updatedWalletDetails
  case ajaxFollowerApps of
    Left error -> pure unit
    Right followerApps ->
      let
        unfoldedFollowerApps :: Array (Tuple PlutusAppId ContractHistory)
        unfoldedFollowerApps = toUnfoldable followerApps
      in
        void
          $ for unfoldedFollowerApps \(plutusAppId /\ contractHistory) -> case contractHistory of
              None -> pure unit
              History marloweParams marloweData transactionInputs -> do
                allContracts <- use _allContracts
                case lookup plutusAppId allContracts of
                  Just contractState -> modifying _allContracts $ insert plutusAppId $ Contract.updateState currentSlot transactionInputs contractState
                  Nothing -> do
                    let
                      mContractState = Contract.mkInitialState updatedWalletDetails currentSlot plutusAppId contractHistory
                    case mContractState of
                      Just contractState -> do
                        modifying _allContracts $ insert plutusAppId contractState
                        addToast $ successToast "You have been given a role in a new contract."
                      Nothing -> addToast $ errorToast "Could not determine contract type." $ Just "You have been given a role in a new contract, but we could not determine the type of the contract and therefore cannot display it."

handleAction _ (UpdateRunningContracts companionAppState) = do
  walletDetails <- use _walletDetails
  allContracts <- use _allContracts
  let
    allMarloweParams = Set.toUnfoldable $ keys companionAppState

    existingMarloweParams = List.toUnfoldable $ map (view _marloweParams) (values allContracts)

    newMarloweParams = difference allMarloweParams existingMarloweParams
  void
    $ for newMarloweParams \marloweParams -> do
        ajaxFollowerContract <- followContract walletDetails marloweParams
        case ajaxFollowerContract of
          Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
          Right (plutusAppId /\ history) -> subscribeToPlutusApp plutusAppId

handleAction { currentSlot } AdvanceTimedoutSteps = do
  walletDetails <- use _walletDetails
  selectedStep <- peruse $ _selectedContract <<< _selectedStep
  modify_
    $ over
        (_contractsState <<< _contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout /= Nothing && contract.executionState.mNextTimeout < Just currentSlot))
        (applyTimeout currentSlot)
  selectedStep' <- peruse $ _selectedContract <<< _selectedStep
  when (selectedStep /= selectedStep')
    $ for_ selectedStep'
    $ \step ->
        let
          contractInput = { currentSlot, walletDetails }
        in
          toContract $ Contract.handleAction contractInput $ Contract.MoveToStep step

-- TODO: we have to handle quite a lot of submodule actions here (mainly just because of the cards),
-- so there's probably a better way of structuring this - perhaps making cards work more like toasts
handleAction input@{ currentSlot } (TemplateAction templateAction) = case templateAction of
  Template.SetTemplate template -> do
    mCurrentTemplate <- peruse (_templateState <<< _template)
    when (mCurrentTemplate /= Just template) $ assign _templateState $ Template.mkInitialState template
    walletLibrary <- use _walletLibrary
    handleAction input $ TemplateAction $ Template.UpdateRoleWalletValidators walletLibrary
    handleAction input $ SetScreen TemplateScreen
  Template.OpenTemplateLibraryCard -> handleAction input $ OpenCard TemplateLibraryCard
  Template.OpenCreateWalletCard tokenName -> handleAction input $ OpenCard $ SaveWalletCard $ Just tokenName
  Template.OpenSetupConfirmationCard -> handleAction input $ OpenCard ContractSetupConfirmationCard
  Template.CloseSetupConfirmationCard -> handleAction input CloseCard -- TODO: guard against closing the wrong card
  Template.StartContract -> do
    extendedContract <- use (_templateState <<< _template <<< _extendedContract)
    templateContent <- use (_templateState <<< _templateContent)
    case instantiateExtendedContract currentSlot extendedContract templateContent of
      Nothing -> addToast $ errorToast "Failed to instantiate contract." $ Just "Something went wrong when trying to instantiate a contract from this template using the parameters you specified."
      Just contract -> do
        -- the user enters wallet nicknames for roles; here we convert these into pubKeyHashes
        walletDetails <- use _walletDetails
        walletLibrary <- use _walletLibrary
        roleWalletInputs <- use (_templateState <<< _roleWalletInputs)
        let
          roleWallets = map (view _value) roleWalletInputs

          roles = mapMaybe (\walletNickname -> view (_walletInfo <<< _pubKeyHash) <$> lookup walletNickname walletLibrary) roleWallets
        ajaxCreateContract <- createContract walletDetails roles contract
        case ajaxCreateContract of
          -- TODO: make this error message more informative
          Left ajaxError -> addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
          _ -> do
            -- FIXME: If the user gives themselves a role in this contract, their WalletCompanion contract
            -- should notice, and that will trigger all the other necessary updates. But if they don't, we
            -- should create a WalletFollower contract manually here.
            handleAction input $ SetScreen ContractsScreen
            addToast $ successToast "Contract started."
  _ -> toTemplate $ Template.handleAction templateAction

handleAction input (ContractHomeAction contractHomeAction) = case contractHomeAction of
  ContractHome.OpenTemplateLibraryCard -> handleAction input $ OpenCard TemplateLibraryCard
  a@(ContractHome.OpenContract _) -> do
    walletDetails <- use _walletDetails
    toContractHome $ ContractHome.handleAction a
    handleAction input $ OpenCard ContractCard
  _ -> toContractHome $ ContractHome.handleAction contractHomeAction

handleAction input@{ currentSlot } (ContractAction contractAction) = do
  walletDetails <- use _walletDetails
  let
    contractInput = { currentSlot, walletDetails }
  case contractAction of
    Contract.AskConfirmation action -> handleAction input $ OpenCard $ ContractActionConfirmationCard action
    Contract.ConfirmAction action -> do
      void $ toContract $ Contract.handleAction contractInput contractAction
      handleAction input CloseCard -- TODO: guard against closing the wrong card
    Contract.CancelConfirmation -> handleAction input CloseCard -- TODO: guard against closing the wrong card
    _ -> toContract $ Contract.handleAction contractInput contractAction

------------------------------------------------------------
toWalletNicknameInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameError) (InputField.Action WalletNicknameError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameInput = mapSubmodule _walletNicknameInput WalletNicknameInputAction

toWalletIdInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletIdError) (InputField.Action WalletIdError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletIdInput = mapSubmodule _walletIdInput WalletIdInputAction

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
