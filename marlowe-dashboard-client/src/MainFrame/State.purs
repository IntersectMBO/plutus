module MainFrame.State (mkMainFrame) where

import Prelude
import Bridge (toFront)
import Capability.Contract (class ManageContract, getContractInstance)
import Capability.Marlowe (class ManageMarlowe, marloweCreateWalletCompanionContract)
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
import Halogen.HTML (HTML)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _newWalletDetails, _pickupState, _subState, _playState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Marlowe.Slot (currentSlot)
import Network.RemoteData (RemoteData(..))
import Pickup.State (handleAction, initialState) as Pickup
import Pickup.Types (Action(..), Card(..)) as Pickup
import Play.Lenses (_allContracts, _walletDetails)
import Play.State (handleAction, handleQuery, mkInitialState) as Play
import Play.Types (Action(..)) as Play
import Plutus.PAB.Webserver.Types (ContractInstanceClientState(..))
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Template.State (handleAction) as Template
import Template.Types (Action(..)) as Template
import Types (ContractInstanceId(..), contractInstanceIdFromString)
import WalletData.Lenses (_assets, _contractInstanceId, _contractInstanceIdString, _remoteDataWalletInfo, _remoteDataAssets, _wallet, _walletNicknameString)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletInfo(..))
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  ManageMarlowe m =>
  MonadWebsocket m =>
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
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    WS.WebSocketOpen -> assign _webSocketStatus WebSocketOpen
    (WS.WebSocketClosed reason) -> assign _webSocketStatus (WebSocketClosed (Just reason))
    (WS.ReceiveMessage (Left errors)) -> pure unit -- failed to decode message, do nothing for now
    (WS.ReceiveMessage (Right streamToClient)) -> Play.handleQuery streamToClient
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
  ManageMarlowe m =>
  MonadWebsocket m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = do
  mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
  for_ mWalletLibraryJson \json ->
    for_ (runExcept $ decodeJSON json) \wallets ->
      assign _wallets wallets
  mWalletDetailsJson <- liftEffect $ getItem walletDetailsLocalStorageKey
  for_ mWalletDetailsJson \json ->
    for_ (runExcept $ decodeJSON json) \walletDetails ->
      handleAction $ PickupAction $ Pickup.PickupWallet walletDetails
  void $ subscribe currentSlotSubscription

handleAction (SetNewWalletNicknameString walletNicknameString) = assign (_newWalletDetails <<< _walletNicknameString) walletNicknameString

handleAction (SetNewWalletContractIdString contractInstanceIdString) = do
  assign (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
  for_ (contractInstanceIdFromString contractInstanceIdString)
    $ \contractInstanceId -> do
        remoteDataWalletCompanionContract <- getContractInstance contractInstanceId
        case remoteDataWalletCompanionContract of
          Success (ContractInstanceClientState { cicWallet }) -> do
            let
              wallet = toFront cicWallet
            remoteDataWalletInfo <- getWalletInfo wallet
            remoteDataAssets <- getWalletTotalFunds wallet
            assign (_newWalletDetails <<< _remoteDataWalletInfo) remoteDataWalletInfo
            assign (_newWalletDetails <<< _remoteDataAssets) remoteDataAssets
          Failure ajaxError -> do
            assign (_newWalletDetails <<< _remoteDataWalletInfo) $ Failure ajaxError
            assign (_newWalletDetails <<< _remoteDataAssets) $ Failure ajaxError
          _ -> pure unit

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletDetails <- use _newWalletDetails
  newWalletNickname <- use (_newWalletDetails <<< _walletNicknameString)
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails ->
        when (not $ member newWalletNickname oldWallets) do
          modify_
            $ over _wallets (insert newWalletNickname walletDetails)
            <<< set _newWalletDetails emptyNewWalletDetails
            <<< set (_playState <<< _card) Nothing
          newWallets <- use _wallets
          liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWallets

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNicknameString nickname

handleAction (PickupAction (Pickup.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractIdString contractId

handleAction (PickupAction Pickup.PickupNewWallet) = do
  newWalletDetails <- use _newWalletDetails
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails -> do
        handleAction AddNewWallet
        handleAction $ PickupAction $ Pickup.PickupWallet walletDetails

handleAction (PickupAction (Pickup.PickupWallet walletDetails)) = do
  let
    wallet = view _wallet walletDetails
  -- we need the local timezoneOffset in Play.State in order to convert datetimeLocal
  -- values to UTC (and vice versa), so we can manage date-to-slot conversions
  timezoneOffset <- liftEffect getTimezoneOffset
  -- FIXME: Remove this, only for debugging. Replace with actually loading existing contracts
  --        from the PAB.
  contracts <- liftEffect $ loadExistingContracts
  currentSlot' <- liftEffect currentSlot
  remoteDataAssets <- getWalletTotalFunds wallet
  case remoteDataAssets of
    Success assets -> do
      let
        updatedWalletDetails = set _assets assets walletDetails
      modify_
        $ set (_playState <<< _allContracts) contracts
        <<< set _subState (Right $ Play.mkInitialState updatedWalletDetails currentSlot' timezoneOffset)
        <<< set (_pickupState <<< _card) Nothing
      subscribeToWallet wallet
      liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON updatedWalletDetails
    _ -> pure unit

handleAction (PickupAction Pickup.GenerateNewWallet) = do
  remoteDataWalletInfo <- createWallet
  assign (_newWalletDetails <<< _remoteDataWalletInfo) remoteDataWalletInfo
  case remoteDataWalletInfo of
    Success (WalletInfo { wallet }) -> do
      remoteDataAssets <- getWalletTotalFunds wallet
      assign (_newWalletDetails <<< _remoteDataAssets) remoteDataAssets
      remoteDataContractInstanceId <- marloweCreateWalletCompanionContract wallet
      case remoteDataContractInstanceId of
        Success contractInstanceId -> do
          let
            contractInstanceIdString = UUID.toString $ unwrap contractInstanceId
          assign (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
          assign (_pickupState <<< _card) (Just Pickup.PickupNewWalletCard)
        -- TODO: show errors to the user
        _ -> pure unit
    -- TODO: show errors to the user
    _ -> pure unit -}

handleAction (PickupAction (Pickup.LookupWallet string)) = do
  wallets <- use _wallets
  -- check for a matching nickname in the wallet library first
  case lookup string wallets of
    Just walletDetails -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard walletDetails
    -- failing that, check for a matching ID in the wallet library
    Nothing -> case findMin $ filter (\walletDetails -> UUID.toString (unwrap (view _contractInstanceId walletDetails)) == string) wallets of
      Just { key, value } -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard value
      -- TODO: and failing that, lookup the wallet contractId from PAB
      Nothing -> pure unit

-- other pickup actions
handleAction (PickupAction pickupAction) = Pickup.handleAction pickupAction

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
    Template.handleAction $ Template.SetRoleWallet tokenName walletNickname

-- other play actions
handleAction (PlayAction playAction) = Play.handleAction playAction

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
