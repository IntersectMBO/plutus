module MainFrame.State (mkMainFrame, handleAction) where

import Prelude
import Bridge (toFront)
import Capability.Contract (class ManageContract, getContractInstanceClientState, getWalletContractInstances)
import Capability.Marlowe (class ManageMarloweContract, marloweCreateWalletCompanionContract, marloweGetWalletCompanionContractObservableState)
import Capability.Toast (class Toast, addToast)
import Capability.Wallet (class ManageWallet, createWallet, getWalletInfo, getWalletTotalFunds)
import Capability.Websocket (class MonadWebsocket, subscribeToWallet, unsubscribeFromWallet)
import ContractHome.State (loadExistingContracts)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Rec.Class (forever)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Map (empty, filter, findMin, insert, lookup, member)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Time.Duration (Milliseconds(..))
import Data.UUID (parseUUID)
import Data.UUID (toString) as UUID
import Effect.Aff (error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, subscribe)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _newWalletDetails, _pickupState, _playState, _subState, _toast, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Marlowe.Slot (currentSlot)
import Network.RemoteData (RemoteData(..))
import Pickup.Lenses (_pickupWalletString)
import Pickup.State (handleAction, dummyState, initialState) as Pickup
import Pickup.Types (Action(..), State) as Pickup
import Pickup.Types (Card(..), PickupNewWalletContext(..))
import Play.Lenses (_allContracts, _currentSlot, _templateState, _walletDetails)
import Play.State (dummyState, handleAction, mkInitialState) as Play
import Play.Types (Action(..), State) as Play
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..), ContractInstanceClientState(..))
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Template.State (dummyState, handleAction) as Template
import Template.Types (Action(..), State) as Template
import Toast.State (defaultState, handleAction) as Toast
import Toast.Types (Action, State) as Toast
import Toast.Types (connectivityErrorToast)
import Types (ContractInstanceId(..))
import WalletData.Lenses (_assets, _contractInstanceId, _contractInstanceIdString, _remoteDataWalletInfo, _remoteDataAssets, _wallet, _walletNicknameString)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletInfo(..))
import WalletData.Validation (parseContractInstanceId)
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  ManageMarloweContract m =>
  MonadWebsocket m =>
  Toast m =>
  Component HTML Query Action Msg m
mkMainFrame =
  mkComponent
    { initialState: const initialState
    , render: render
    , eval:
        mkEval
          { handleQuery
          , handleAction
          , receive: const Nothing
          , initialize: Just Init
          , finalize: Nothing
          }
    }

initialState :: State
initialState =
  { wallets: empty
  , newWalletDetails: emptyNewWalletDetails
  , templates: contractTemplates
  , webSocketStatus: WebSocketClosed Nothing
  , subState: Left Pickup.initialState
  , toast: Toast.defaultState
  }

handleQuery ::
  forall a m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  ManageMarloweContract m =>
  MonadWebsocket m =>
  Toast m =>
  Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    WS.WebSocketOpen -> assign _webSocketStatus WebSocketOpen
    (WS.WebSocketClosed reason) -> assign _webSocketStatus (WebSocketClosed (Just reason)) -- TODO: show warning to the user
    (WS.ReceiveMessage (Left errors)) -> pure unit -- TODO: show error to the user
    (WS.ReceiveMessage (Right streamToClient)) -> case streamToClient of
      InstanceUpdate contractInstanceId instanceStatusToClient -> pure unit
      SlotChange slot -> assign (_playState <<< _currentSlot) $ toFront slot
      WalletFundsChange wallet value -> do
        mCurrentWallet <- peruse (_playState <<< _walletDetails <<< _wallet)
        for_ mCurrentWallet \currentWallet ->
          when (currentWallet == toFront wallet)
            $ assign (_playState <<< _walletDetails <<< _assets) (toFront value)
  pure $ Just next

handleQuery (MainFrameActionQuery action next) = do
  handleAction action
  pure $ Just next

-- FIXME: We need to discuss if we should remove this after we connect to the PAB. In case we do,
--        if there is a disconnection we might lose some seconds and timeouts will freeze.
currentSlotSubscription ::
  forall m.
  MonadAff m =>
  EventSource m Action
currentSlotSubscription =
  EventSource.affEventSource \emitter -> do
    fiber <-
      Aff.forkAff
        $ forever do
            Aff.delay $ Milliseconds 1000.0
            slot <- liftEffect $ currentSlot
            EventSource.emit emitter (PlayAction $ Play.SetCurrentSlot slot)
    pure $ EventSource.Finalizer $ Aff.killFiber (error "removing aff") fiber

-- Note [State]: Some actions belong logically in one part of the state, but
-- from the user's point of view in another. For example, the action of picking
-- up a wallet belongs logically in the MainFrame state (because it modifies
-- that state), but from the user's point of view it belongs in the Pickup
-- state (because that's the state the app is in when you perform it). To work
-- around this, we can either make our `handleAction` functions a bit awkward,
-- or our `render` functions a bit awkward. I prefer the former. Hence some
-- submodule actions (triggered straightforwardly in the submodule's `render`
-- functions) are handled by their parent module's `handleAction` function.
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  ManageMarloweContract m =>
  MonadWebsocket m =>
  Toast m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
-- mainframe actions
handleAction Init = do
  -- maybe load wallet library from localStorage
  mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
  for_ mWalletLibraryJson \json ->
    for_ (runExcept $ decodeJSON json) \wallets ->
      assign _wallets wallets
  -- maybe load picked up wallet from localStorage and pick it up again
  mWalletDetailsJson <- liftEffect $ getItem walletDetailsLocalStorageKey
  for_ mWalletDetailsJson \json ->
    for_ (runExcept $ decodeJSON json) \walletDetails ->
      handleAction $ PickupAction $ Pickup.PickupWallet walletDetails
  -- subscribe to local currentSlot counter
  void $ subscribe currentSlotSubscription

handleAction (SetNewWalletNicknameString walletNicknameString) = assign (_newWalletDetails <<< _walletNicknameString) walletNicknameString

handleAction (SetNewWalletContractIdString contractInstanceIdString) = do
  assign (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
  -- if this is a valid contract ID ...
  for_ (parseContractInstanceId contractInstanceIdString)
    $ \contractInstanceId -> do
        -- lookup wallet companion contract with this ID on the PAB
        remoteDataWalletCompanionContract <- getContractInstanceClientState contractInstanceId
        case remoteDataWalletCompanionContract of
          Success (ContractInstanceClientState { cicWallet }) -> do
            -- if the companion contract is found, lookup wallet info and assets
            let
              wallet = toFront cicWallet
            remoteDataWalletInfo <- getWalletInfo wallet
            remoteDataAssets <- getWalletTotalFunds wallet
            modify_
              $ set (_newWalletDetails <<< _remoteDataWalletInfo) remoteDataWalletInfo
              <<< set (_newWalletDetails <<< _remoteDataAssets) remoteDataAssets
          -- otherwise assign the remoteData value to remoteDataWalletInfo
          -- (this is used when validating the contractInstanceIdString)
          Failure ajaxError -> assign (_newWalletDetails <<< _remoteDataWalletInfo) $ Failure ajaxError
          Loading -> assign (_newWalletDetails <<< _remoteDataWalletInfo) Loading
          NotAsked -> assign (_newWalletDetails <<< _remoteDataWalletInfo) NotAsked

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletDetails <- use _newWalletDetails
  newWalletNickname <- use (_newWalletDetails <<< _walletNicknameString)
  -- try and make a new wallet from the newWalletDetails (succeeds if all RemoteData properties are Success)
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails ->
        when (not $ member newWalletNickname oldWallets) do
          modify_
            $ over _wallets (insert newWalletNickname walletDetails)
            <<< set _newWalletDetails emptyNewWalletDetails
          handleAction $ PlayAction Play.CloseCard
          newWallets <- use _wallets
          liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWallets

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNicknameString nickname

handleAction (PickupAction (Pickup.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractIdString contractId

handleAction (PickupAction Pickup.PickupNewWallet) = do
  newWalletDetails <- use _newWalletDetails
  -- try and make a new wallet from the newWalletDetails (succeeds if all RemoteData properties are Success)
  -- TODO: add error toast when this fails
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails -> do
        handleAction AddNewWallet
        handleAction $ PickupAction $ Pickup.PickupWallet walletDetails

handleAction (PickupAction (Pickup.PickupWallet walletDetails)) = do
  let
    wallet = view _wallet walletDetails

    networkErrorToast = \_ -> addToast $ connectivityErrorToast "Couldn't pickup wallet"
  -- we need the local timezoneOffset in Play.State in order to convert datetimeLocal
  -- values to UTC (and vice versa), so we can manage date-to-slot conversions
  timezoneOffset <- liftEffect getTimezoneOffset
  -- get up to date balance for this wallet
  remoteDataAssets <- getWalletTotalFunds wallet
  -- get map of contracts for which this wallet has a role token (from the wallet companion contract)
  let
    contractInstanceId = view _contractInstanceId walletDetails
  remoteDataCompanionContractObservableState <- marloweGetWalletCompanionContractObservableState contractInstanceId
  remoteDataWalletContractInstances <- getWalletContractInstances wallet
  -- FIXME: For now, we're just loading some dummy contracts for testing. Soon we need to get this from
  --        the wallet's contract instances together with the wallet companion contract (the companion
  --        contract will tell us if there are any contracts for which this wallet has a role that do not
  --        yet have running instances).
  contracts <- liftEffect $ loadExistingContracts
  currentSlot' <- liftEffect currentSlot
  case remoteDataAssets of
    Success assets -> do
      let
        updatedWalletDetails = set _assets assets walletDetails
      modify_
        $ set (_playState <<< _allContracts) contracts
        <<< set _subState (Right $ Play.mkInitialState updatedWalletDetails currentSlot' timezoneOffset)
        <<< set (_pickupState <<< _card) Nothing
      -- subscribe to the wallet to get updates about balance changes
      subscribeToWallet wallet
      liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON updatedWalletDetails
    Failure err -> networkErrorToast err
    _ -> pure unit

handleAction (PickupAction Pickup.GenerateNewWallet) = do
  remoteDataWalletInfo <- createWallet
  assign (_newWalletDetails <<< _remoteDataWalletInfo) remoteDataWalletInfo
  let
    networkErrorToast = \_ -> addToast $ connectivityErrorToast "Couldn't generate wallet"
  case remoteDataWalletInfo of
    Success (WalletInfo { wallet }) -> do
      remoteDataAssets <- getWalletTotalFunds wallet
      assign (_newWalletDetails <<< _remoteDataAssets) remoteDataAssets
      remoteDataContractInstanceId <- marloweCreateWalletCompanionContract wallet
      case remoteDataContractInstanceId of
        Success contractInstanceId -> do
          let
            contractInstanceIdString = UUID.toString $ unwrap contractInstanceId
          modify_
            $ set (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
            <<< set (_pickupState <<< _card) (Just (PickupNewWalletCard WalletGenerated))
        Failure err -> networkErrorToast err
        _ -> pure unit
    Failure err -> networkErrorToast err
    _ -> pure unit

handleAction (PickupAction (Pickup.SetPickupWalletString string)) = do
  assign (_pickupState <<< _pickupWalletString) string
  wallets <- use _wallets
  -- first check for a matching nickname in the wallet library
  case lookup string wallets of
    Just walletDetails -> assign (_pickupState <<< _card) $ Just $ PickupWalletCard walletDetails
    -- then check for a matching ID in the wallet library
    Nothing -> case findMin $ filter (\walletDetails -> UUID.toString (unwrap (view _contractInstanceId walletDetails)) == string) wallets of
      Just { key, value } -> assign (_pickupState <<< _card) $ Just $ PickupWalletCard value
      -- then check whether the string is a valid UUID
      Nothing -> case parseContractInstanceId string of
        Just contractInstanceId -> do
          -- set this as the _newWalletDetails <<< _contractInstanceIdString, which will lookup on the PAB and
          -- populate _newWalletDetails <<< _remoteDataWalletInfo with the result
          handleAction $ SetNewWalletContractIdString string
          -- if that triggered a match, show the pickup wallet card
          remoteDataWalletInfo <- use (_newWalletDetails <<< _remoteDataWalletInfo)
          case remoteDataWalletInfo of
            Success _ -> assign (_pickupState <<< _card) $ Just $ PickupNewWalletCard WalletFound
            _ -> pure unit
        -- otherwise there's nothing we can do
        Nothing -> pure unit

-- other pickup actions
handleAction (PickupAction pickupAction) = toPickup $ Pickup.handleAction pickupAction

-- play actions that need to be handled here
handleAction (PlayAction Play.PutdownWallet) = do
  mWallet <- peruse (_playState <<< _walletDetails <<< _wallet)
  for_ mWallet \wallet -> do
    assign _subState $ Left Pickup.initialState
    liftEffect $ removeItem walletDetailsLocalStorageKey
    unsubscribeFromWallet wallet

handleAction (PlayAction (Play.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNicknameString nickname

handleAction (PlayAction (Play.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractIdString contractId

handleAction (PlayAction (Play.AddNewWallet mTokenName)) = do
  walletNickname <- use (_newWalletDetails <<< _walletNicknameString)
  handleAction AddNewWallet
  for_ mTokenName \tokenName ->
    toTemplate $ Template.handleAction $ Template.SetRoleWallet tokenName walletNickname

-- other play actions
handleAction (PlayAction playAction) = toPlay $ Play.handleAction playAction

handleAction (ToastAction toastAction) = toToast $ Toast.handleAction toastAction

------------------------------------------------------------
-- Note [dummyState]: In order to map a submodule whose state might not exist, we need
-- to provide a dummyState for that submodule. Halogen would use this dummyState to play
-- with if we ever tried to call one of these handlers when the submodule state does not
-- exist. In practice this should never happen.
toPickup ::
  forall m msg slots.
  Functor m =>
  HalogenM Pickup.State Pickup.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toPickup = mapMaybeSubmodule _pickupState PickupAction Pickup.dummyState

toPlay ::
  forall m msg slots.
  Functor m =>
  HalogenM Play.State Play.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toPlay = mapMaybeSubmodule _playState PlayAction Play.dummyState

toTemplate ::
  forall m msg slots.
  Functor m =>
  HalogenM Template.State Template.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toTemplate = mapMaybeSubmodule (_playState <<< _templateState) (PlayAction <<< Play.TemplateAction) Template.dummyState

toToast ::
  forall m msg slots.
  Functor m =>
  HalogenM Toast.State Toast.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toToast = mapSubmodule _toast ToastAction

------------------------------------------------------------
emptyNewWalletDetails :: NewWalletDetails
emptyNewWalletDetails =
  { walletNicknameString: mempty
  , contractInstanceIdString: mempty
  , remoteDataWalletInfo: NotAsked
  , remoteDataAssets: NotAsked
  }

mkNewWallet :: NewWalletDetails -> Maybe WalletDetails
mkNewWallet newWalletDetails =
  let
    walletNickname = view _walletNicknameString newWalletDetails

    contractInstanceIdString = view _contractInstanceIdString newWalletDetails

    mContractInstanceId = map ContractInstanceId $ parseUUID contractInstanceIdString

    remoteDataWalletInfo = view _remoteDataWalletInfo newWalletDetails

    remoteDataAssets = view _remoteDataAssets newWalletDetails
  in
    case mContractInstanceId, remoteDataWalletInfo, remoteDataAssets of
      Just contractInstanceId, Success (WalletInfo { wallet, pubKey, pubKeyHash }), Success assets -> Just { walletNickname, contractInstanceId, wallet, pubKey, pubKeyHash, assets }
      _, _, _ -> Nothing
