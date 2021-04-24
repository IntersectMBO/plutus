module MainFrame.State (mkMainFrame, handleAction) where

import Prelude
import Bridge (toFront)
import Capability.Contract (class ManageContract)
import Capability.Marlowe (class ManageMarlowe)
import Capability.Toast (class Toast, addToast)
import Capability.Wallet (class ManageWallet, getWalletTotalFunds)
import Capability.Websocket (class MonadWebsocket, subscribeToContract, subscribeToWallet, unsubscribeFromContract, unsubscribeFromWallet)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, set, view)
import Data.Lens.Extra (peruse)
import Data.Map (lookup)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem, setItem, removeItem)
import MainFrame.Lenses (_pickupState, _playState, _subState, _toast, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Slot (currentSlot)
import Pickup.Lenses (_walletLibrary)
import Pickup.State (handleAction, dummyState, mkInitialState) as Pickup
import Pickup.Types (Action(..), State) as Pickup
import Play.Lenses (_allContracts, _templateState, _walletDetails)
import Play.State (dummyState, handleAction, mkInitialState) as Play
import Play.Types (Action(..), State) as Play
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..), InstanceStatusToClient(..))
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Template.State (dummyState) as Template
import Template.Types (Action, State) as Template
import Toast.State (defaultState, handleAction) as Toast
import Toast.Types (ajaxErrorToast)
import Toast.Types (Action, State) as Toast
import WalletData.Lenses (_assets, _companionContractId, _wallet, _walletInfo, _walletNickname)
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageContract m =>
  ManageWallet m =>
  ManageMarlowe m =>
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
  { webSocketStatus: WebSocketClosed Nothing
  , subState: Left Pickup.dummyState
  , toast: Toast.defaultState
  }

handleQuery ::
  forall a m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
  MonadWebsocket m =>
  Toast m =>
  Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    WS.WebSocketOpen -> assign _webSocketStatus WebSocketOpen
    (WS.WebSocketClosed closeEvent) -> do
      -- TODO: When we change our websocket subscriptions, the websocket is closed and then reopened.
      -- We don't want to warn the user in this case, but we do want to warn them if the websocket
      -- closes for some unexpected reason. But currently I don't know how to distinguish these cases.
      -- addToast $ connectivityErrorToast "Connection to the server has been lost"
      assign _webSocketStatus (WebSocketClosed (Just closeEvent))
    (WS.ReceiveMessage (Left errors)) -> pure unit -- TODO: show error to the user
    (WS.ReceiveMessage (Right streamToClient)) -> case streamToClient of
      -- update the current slot
      SlotChange slot -> handleAction $ PlayAction $ Play.SetCurrentSlot $ toFront slot
      -- update the wallet funds (if the change is to the current wallet)
      -- note: we should only ever be notified of changes to the current wallet,
      -- since we subscribe to this update when we pick it up, and unsubscribe
      -- when we put it down - but we check here anyway in case
      WalletFundsChange wallet value -> do
        mCurrentWallet <- peruse (_playState <<< _walletDetails <<< _walletInfo <<< _wallet)
        for_ mCurrentWallet \currentWallet ->
          when (currentWallet == toFront wallet)
            $ assign (_playState <<< _walletDetails <<< _assets) (toFront value)
      -- update the state when a contract instance changes
      -- note: we should be subsribed to updates from all (and only) the current
      -- wallet's contract instances, including its wallet companion contract
      InstanceUpdate bContractInstanceId instanceStatusToClient -> case instanceStatusToClient of
        NewObservableState rawJson -> do
          let
            contractInstanceId = toFront bContractInstanceId
          mPlayState <- peruse _playState
          -- these updates should only ever be coming when we are in the Play state (and if
          -- we're not, we don't care about them anyway)
          for_ mPlayState \playState -> do
            let
              walletCompanionContractInstanceId = view (_walletDetails <<< _companionContractId) playState
            if contractInstanceId == walletCompanionContractInstanceId then
              -- this is the WalletCompanion contract
              -- FIXME: parse the rawJson and check for roles in new contracts that need we need to join
              pure unit
            else
              -- this should be one of the wallet's FollowContracts (if it isn't, we don't care about it
              -- anyway)
              for_ (lookup contractInstanceId $ view _allContracts playState) \contractState ->
                -- FIXME: parse the jawJson and update the contract state accordingly
                pure unit
        -- Plutus contracts in general can change in other ways, but the Marlowe contracts don't, so
        -- we can ignore these cases here
        _ -> pure unit
  pure $ Just next

handleQuery (MainFrameActionQuery action next) = do
  handleAction action
  pure $ Just next

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
  Toast m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
-- mainframe actions
handleAction Init = do
  -- maybe load wallet library from localStorage
  mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
  for_ mWalletLibraryJson \json ->
    for_ (runExcept $ decodeJSON json) \wallets ->
      assign (_pickupState <<< _walletLibrary) wallets
  -- maybe load picked up wallet from localStorage and show prompt to pick it up again
  mWalletDetailsJson <- liftEffect $ getItem walletDetailsLocalStorageKey
  for_ mWalletDetailsJson \json ->
    for_ (runExcept $ decodeJSON json) \walletDetails -> do
      handleAction $ PickupAction $ Pickup.SetPickupWalletString $ view _walletNickname walletDetails

handleAction (EnterPickupState walletLibrary walletDetails) = do
  let
    wallet = view (_walletInfo <<< _wallet) walletDetails

    companionContractId = view _companionContractId walletDetails
  unsubscribeFromWallet wallet
  unsubscribeFromContract companionContractId
  -- FIXME: unsubscribe from the current wallet's contracts
  assign _subState $ Left $ Pickup.mkInitialState walletLibrary
  liftEffect $ removeItem walletDetailsLocalStorageKey

handleAction (EnterPlayState walletLibrary walletDetails) = do
  let
    wallet = view (_walletInfo <<< _wallet) walletDetails

    companionContractId = view _companionContractId walletDetails
  ajaxAssets <- getWalletTotalFunds wallet
  case ajaxAssets of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to load wallet" ajaxError
    Right assets -> do
      let
        updatedWalletDetails = set _assets assets walletDetails
      subscribeToWallet wallet
      subscribeToContract companionContractId
      timezoneOffset <- liftEffect getTimezoneOffset
      slot <- liftEffect currentSlot
      -- FIXME: get contracts for this wallet
      -- FIXME: subscribe to contracts for this wallet
      let
        contracts = mempty
      assign _subState $ Right $ Play.mkInitialState walletLibrary updatedWalletDetails contracts slot timezoneOffset
      liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON updatedWalletDetails

handleAction (PickupAction pickupAction) = toPickup $ Pickup.handleAction pickupAction

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
