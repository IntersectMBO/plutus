module Play.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.Contract (class ManageContract)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createContract, createPendingFollowerApp, followContract, followContractWithPendingFollowerApp, getFollowerApps, getRoleContracts, lookupWalletInfo, subscribeToPlutusApp)
import Capability.MarloweStorage (class ManageMarloweStorage, getWalletLibrary, insertIntoContractNicknames, insertIntoWalletLibrary)
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_mMarloweParams, _nickname, _selectedStep)
import Contract.State (applyTimeout)
import Contract.State (dummyState, handleAction, mkInitialState, mkPlaceholderState, updateState) as Contract
import Contract.Types (Action(..), State) as Contract
import ContractHome.Lenses (_contracts)
import ContractHome.State (handleAction, mkInitialState) as ContractHome
import ContractHome.Types (Action(..), State) as ContractHome
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Class (ask)
import Data.Array (elem, head, init, reverse, snoc)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, filtered, modifying, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Traversal (traversed)
import Data.Map (Map, alter, delete, filter, filterKeys, findMin, insert, lookup, mapMaybe, toUnfoldable, values)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes(..))
import Data.Traversable (for)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (emptyUUID)
import Effect.Aff.Class (class MonadAff)
import Env (DataProvider(..), Env)
import Halogen (HalogenM, modify_)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import InputField.Lenses (_value)
import InputField.State (handleAction, initialState) as InputField
import InputField.Types (Action(..), State) as InputField
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Execution.Types (NamedAction(..))
import Marlowe.Extended.Metadata (_extendedContract, _metaData)
import Marlowe.PAB (ContractHistory, MarloweParams, PlutusAppId(..), MarloweData)
import Marlowe.Semantics (Slot(..))
import Network.RemoteData (RemoteData(..), fromEither)
import Play.Lenses (_allContracts, _cards, _contractsState, _menuOpen, _remoteWalletInfo, _screen, _selectedContract, _templateState, _walletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput)
import Play.Types (Action(..), Card(..), Input, Screen(..), State)
import Template.Lenses (_contractNickname, _roleWalletInputs, _template, _templateContent)
import Template.State (dummyState, handleAction, mkInitialState) as Template
import Template.State (instantiateExtendedContract)
import Template.Types (Action(..), State) as Template
import Toast.Types (ajaxErrorToast, decodedAjaxErrorToast, errorToast, successToast)
import WalletData.Lenses (_pubKeyHash, _walletInfo, _walletNickname)
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, parsePlutusAppId, walletIdError, walletNicknameError)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty defaultWalletDetails mempty mempty (Slot zero) (Minutes zero)

mkInitialState :: WalletLibrary -> WalletDetails -> Map PlutusAppId ContractHistory -> Map PlutusAppId String -> Slot -> Minutes -> State
mkInitialState walletLibrary walletDetails contracts contractNicknames currentSlot timezoneOffset =
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
  , contractsState: ContractHome.mkInitialState walletDetails currentSlot contracts contractNicknames
  }

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageContract m =>
  ManageMarloweStorage m =>
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
      handleAction input $ CloseCard $ SaveWalletCard Nothing
      let
        -- note the empty properties are fine for saved wallets - these will be fetched if/when
        -- this wallet is picked up
        walletDetails =
          { walletNickname
          , companionAppId: walletId
          , marloweAppId: PlutusAppId emptyUUID
          , walletInfo
          , assets: mempty
          , previousCompanionAppState: Nothing
          }
      modifying _walletLibrary (insert walletNickname walletDetails)
      insertIntoWalletLibrary walletDetails
      newWalletLibrary <- use _walletLibrary
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
      handleAction input $ WalletIdInputAction InputField.Reset
      handleAction input $ WalletIdInputAction $ InputField.SetValidator $ walletIdError NotAsked walletLibrary
    _ -> pure unit
  modify_
    $ over _cards (flip snoc card)
    <<< set _menuOpen false

handleAction _ (CloseCard card) = do
  cards <- use _cards
  let
    topCard = head $ reverse cards

    cardsMatch = case topCard, card of
      Just (SaveWalletCard _), SaveWalletCard _ -> true
      Just (ViewWalletCard _), ViewWalletCard _ -> true
      Just (ContractActionConfirmationCard _), ContractActionConfirmationCard _ -> true
      _, _ -> topCard == Just card
  when cardsMatch $ void
    $ for_ (init cards) \remainingCards ->
        assign _cards remainingCards

-- Until everything is working in the PAB, we are simulating persistent and shared data using localStorage; this
-- action updates the state to match the localStorage, and should be called whenever the stored data changes.
-- It's not very subtle or efficient - it just updates everything in one go.
handleAction input@{ currentSlot } UpdateFromStorage = do
  { dataProvider } <- ask
  when (dataProvider == LocalStorage) do
    walletDetails <- use _walletDetails
    -- update the wallet library
    storedWalletLibrary <- getWalletLibrary
    assign _walletLibrary storedWalletLibrary
    -- update the current wallet details to match those from the wallet library
    let
      mStoredWalletDetails = lookup (view _walletNickname walletDetails) storedWalletLibrary
    for_ mStoredWalletDetails \storedWalletDetails -> assign _walletDetails storedWalletDetails
    -- make sure we have contracts for all the follower apps
    updatedWalletDetails <- use _walletDetails
    ajaxCompanionAppState <- getRoleContracts updatedWalletDetails
    for_ ajaxCompanionAppState (handleAction input <<< UpdateFollowerApps)
    -- make sure all contracts are in sync with their follower apps
    ajaxFollowerApps <- getFollowerApps walletDetails
    for_ ajaxFollowerApps \followerApps ->
      let
        unfoldedFollowerApps :: Array (Tuple PlutusAppId ContractHistory)
        unfoldedFollowerApps = toUnfoldable followerApps
      in
        void $ for unfoldedFollowerApps \(plutusAppId /\ contractHistory) -> handleAction input $ UpdateContract plutusAppId contractHistory

-- this handler takes the wallet companion app state (which contains MarloweParams of all the contracts)
-- the wallet is interested in, compares it to the existing contracts, and either creates new follower
-- apps or activates pending ones for any contracts that aren't yet being followed
handleAction input (UpdateFollowerApps companionAppState) = do
  walletDetails <- use _walletDetails
  existingContracts <- use _allContracts
  let
    contractExists marloweParams = elem (Just marloweParams) (view _mMarloweParams <$> values existingContracts)

    newContracts = filterKeys (not contractExists) companionAppState

    newContractsArray :: Array (Tuple MarloweParams MarloweData)
    newContractsArray = toUnfoldable newContracts
  void
    $ for newContractsArray \(marloweParams /\ marloweData) -> do
        let
          mTemplate = findTemplate marloweData.marloweContract

          hasRightMetaData :: Contract.State -> Boolean
          hasRightMetaData { mMarloweParams, metadata } = case mMarloweParams, mTemplate of
            Nothing, Just template -> template.metaData == metadata
            _, _ -> false

          mPendingContract = findMin $ filter hasRightMetaData existingContracts
        -- Note [PendingContracts]: Okay, here's the problem: When we're using the PAB, and a contract is created,
        -- we create a follower app immediately as a placeholder (and remember its PlutusAppId), then we wait for
        -- the wallet companion app to tell us the MarloweParams of the contract we created, and pass those to the
        -- pending follower app. Fine. But when we're using the LocalStorage as our dataProvider, this workflow
        -- doesn't quite work. This is because the LocalStorage doesn't keep a record of PlutusAppIds, but just
        -- derives them as a function of the MarloweParams (see note [MarloweParams] in Capability.Marlowe). So
        -- when we create a pending follower app with LocalStorage, we get back what is ultimately the wrong
        -- PlutusAppId (and we can't know the right one until we've generated the MarloweParams). At that point we
        -- could try to update the PlutusAppId, but it's simpler to just delete the pending follower app and
        -- create a new one with the right ID (and the right key in the contracts map).
        --
        -- This solution is ugly for two reasons: (1) In general, the Marlowe capability should be the only thing
        -- that cares about the dataProvider and does things differently depending on what it is. (2) In particular,
        -- what we're doing here means that the LocalStorage implementations of `createPendingFollowerApp` and
        -- `followContractWithPendingFollowerApp` are completely pointless (the first one is called at the
        -- appropriate point, but here we just delete the pending follower app that it created without making any
        -- use of it; and the second is never even called).
        --
        -- (Note: There are sensible LocalStorage implementations of these useless functions in the Marlowe capability.
        -- Why? Because I wrote them before I realised that the simplest solution to the present problem would be to
        -- stop using them. I might as well leave them there in case they become useful again at some point.)
        --
        -- But the good news is that all of this is for the bin anyway, as soon as the PAB is working fully and we can
        -- get rid of the LocalStorage hack altogether. So I think in the meantime this will do (and I don't want to
        -- waste any more time than I already have on trying to do something nicer).
        { dataProvider } <- ask
        case dataProvider of
          LocalStorage -> do
            ajaxFollowerApp <- followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> do
                handleAction input $ UpdateContract followerAppId contractHistory
                for_ mPendingContract \{ key, value } -> do
                  modifying _allContracts
                    $ delete key
                    <<< alter (map (set _nickname value.nickname)) followerAppId
                  insertIntoContractNicknames followerAppId value.nickname
          PAB _ -> do
            ajaxFollowerApp <- case mPendingContract of
              Just { key: followerAppId } -> followContractWithPendingFollowerApp walletDetails marloweParams followerAppId
              Nothing -> followContract walletDetails marloweParams
            case ajaxFollowerApp of
              Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load new contract." decodedAjaxError
              Right (followerAppId /\ contractHistory) -> subscribeToPlutusApp dataProvider followerAppId

-- this handler updates the state of an individual contract
handleAction input@{ currentSlot } (UpdateContract plutusAppId contractHistory@{ chParams, chHistory }) =
  -- if the chParams have not yet been set, we can't do anything; that's fine though, we'll get
  -- another notification through the websocket as soon as they are set
  for_ chParams \(marloweParams /\ marloweData) -> do
    walletDetails <- use _walletDetails
    allContracts <- use _allContracts
    case lookup plutusAppId allContracts of
      Just contractState -> do
        selectedStep <- peruse $ _selectedContract <<< _selectedStep
        modifying _allContracts $ insert plutusAppId $ Contract.updateState walletDetails marloweParams currentSlot chHistory contractState
        -- if the modification changed the currently selected step, that means the card for the contract
        -- that was changed is currently open, so we need to realign the step cards
        selectedStep' <- peruse $ _selectedContract <<< _selectedStep
        when (selectedStep /= selectedStep')
          $ for_ selectedStep' (handleAction input <<< ContractAction <<< Contract.MoveToStep)
      Nothing -> for_ (Contract.mkInitialState walletDetails currentSlot plutusAppId mempty contractHistory) (modifying _allContracts <<< insert plutusAppId)

handleAction input@{ currentSlot } AdvanceTimedoutSteps = do
  walletDetails <- use _walletDetails
  selectedStep <- peruse $ _selectedContract <<< _selectedStep
  modify_
    $ over
        (_contractsState <<< _contracts <<< traversed <<< filtered (\contract -> contract.executionState.mNextTimeout /= Nothing && contract.executionState.mNextTimeout <= Just currentSlot))
        (applyTimeout currentSlot)
  -- If the modification changed the currently selected step, that means the card for the contract
  -- that was changed is currently open, so we need to realign the step cards. We also call the
  -- CancelConfirmation action - because if the user had the action confirmation card open for an
  -- action in the current step, we want to close it (otherwise they could confirm an action that
  -- is no longer possible).
  selectedStep' <- peruse $ _selectedContract <<< _selectedStep
  when (selectedStep /= selectedStep') do
    for_ selectedStep' (handleAction input <<< ContractAction <<< Contract.MoveToStep)
    handleAction input $ ContractAction Contract.CancelConfirmation

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
  Template.CloseSetupConfirmationCard -> handleAction input $ CloseCard ContractSetupConfirmationCard
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
            -- We create a follower app now with no MarloweParams; when the next notification of a new contract
            -- notification comes in, a follower app with no MarloweParams but the right metadata will be used.
            ajaxPendingFollowerApp <- createPendingFollowerApp walletDetails
            case ajaxPendingFollowerApp of
              Left ajaxError -> addToast $ ajaxErrorToast "Failed to initialise contract." ajaxError
              Right followerAppId -> do
                contractNickname <- use (_templateState <<< _contractNickname)
                insertIntoContractNicknames followerAppId contractNickname
                metaData <- use (_templateState <<< _template <<< _metaData)
                modifying _allContracts $ insert followerAppId $ Contract.mkPlaceholderState followerAppId contractNickname metaData contract
                handleAction input $ SetScreen ContractsScreen
                addToast $ successToast "The request to initialise this contract has been submitted."
                { dataProvider } <- ask
                when (dataProvider == LocalStorage) (handleAction input UpdateFromStorage)
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
      handleAction input $ CloseCard $ ContractActionConfirmationCard CloseContract
    Contract.CancelConfirmation -> handleAction input $ CloseCard $ ContractActionConfirmationCard CloseContract
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
