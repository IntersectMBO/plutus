module MainFrame.State (mkMainFrame, handleAction) where

import Prelude
import Bridge (toFront)
import Capability.Marlowe.Dummy (class ManageMarlowe, getFollowerApps, getRoleContracts, subscribeToPlutusApp, subscribeToWallet, unsubscribeFromPlutusApp, unsubscribeFromWallet)
import Capability.Toast (class Toast, addToast)
import Contract.State (mkInitialState, updateState) as Contract
import ContractHome.Types (Action(..)) as ContractHome
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, use, view)
import Data.Lens.Extra (peruse)
import Data.Map (insert, keys, lookup)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Set (toUnfoldable) as Set
import Data.Traversable (for)
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, subscribe)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.LocalStorage (localStorageEvents)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_currentSlot, _pickupState, _playState, _subState, _toast, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.PAB (ContractHistory(..), PlutusAppId)
import Pickup.Lenses (_walletLibrary)
import Pickup.State (handleAction, dummyState, mkInitialState) as Pickup
import Pickup.Types (Action(..), State) as Pickup
import Play.Lenses (_allContracts, _walletDetails)
import Play.State (dummyState, handleAction, mkInitialState) as Play
import Play.Types (Action(..), State) as Play
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..), InstanceStatusToClient(..))
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Toast.State (defaultState, handleAction) as Toast
import Toast.Types (Action, State) as Toast
import Toast.Types (decodedAjaxErrorToast, decodingErrorToast, errorToast, successToast)
import WalletData.Lenses (_assets, _companionAppId, _marloweAppId, _wallet, _walletInfo)
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
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
  , currentSlot: zero -- this will be updated as soon as the websocket connection is working
  , subState: Left Pickup.dummyState
  , toast: Toast.defaultState
  }

handleQuery ::
  forall a m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
  Toast m =>
  Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    WS.WebSocketOpen -> do
      assign _webSocketStatus WebSocketOpen
      -- potentially renew websocket subscriptions
      mPlayState <- peruse _playState
      for_ mPlayState \playState -> do
        let
          wallet = view (_walletDetails <<< _walletInfo <<< _wallet) playState

          followAppIds :: Array PlutusAppId
          followAppIds = Set.toUnfoldable $ keys $ view _allContracts playState
        subscribeToWallet wallet
        for followAppIds subscribeToPlutusApp
    (WS.WebSocketClosed closeEvent) -> do
      -- TODO: Consider whether we should show an error/warning when this happens. It might be more
      -- confusing than helpful, since the websocket is automatically reopened if it closes for any
      -- reason.
      assign _webSocketStatus (WebSocketClosed (Just closeEvent))
    (WS.ReceiveMessage (Left multipleErrors)) -> addToast $ decodingErrorToast "Failed to parse message from the server." multipleErrors
    (WS.ReceiveMessage (Right streamToClient)) -> case streamToClient of
      -- update the current slot
      SlotChange slot -> do
        assign _currentSlot $ toFront slot
        handleAction $ PlayAction Play.AdvanceTimedoutSteps
      -- update the wallet funds (if the change is to the current wallet)
      -- note: we should only ever be notified of changes to the current wallet, since we subscribe to
      -- this update when we pick it up, and unsubscribe when we put it down - but we check here
      -- anyway in case
      WalletFundsChange wallet value -> do
        mCurrentWallet <- peruse (_playState <<< _walletDetails <<< _walletInfo <<< _wallet)
        for_ mCurrentWallet \currentWallet -> do
          when (currentWallet == toFront wallet)
            $ assign (_playState <<< _walletDetails <<< _assets) (toFront value)
      -- update the state when a contract instance changes
      -- note: we should be subsribed to updates from all (and only) the current wallet's contract
      -- instances, including its wallet companion contract
      InstanceUpdate contractInstanceId instanceStatusToClient -> case instanceStatusToClient of
        NewObservableState rawJson -> do
          let
            plutusAppId = toFront contractInstanceId
          mPlayState <- peruse _playState
          -- these updates should only ever be coming when we are in the Play state (and if
          -- we're not, we don't care about them anyway)
          for_ mPlayState \playState -> do
            let
              walletCompanionAppId = view (_walletDetails <<< _companionAppId) playState

              marloweAppId = view (_walletDetails <<< _marloweAppId) playState
            -- if this is the wallet's WalletCompanionApp...
            if (plutusAppId == walletCompanionAppId) then case runExcept $ decodeJSON $ unwrap rawJson of
              Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
              Right companionState -> handleAction $ PlayAction $ Play.UpdateRunningContracts companionState
            else
              -- if this is the wallet's MarloweApp...
              if (plutusAppId == marloweAppId) then
                -- TODO: in the future the Marlowe app's state will change when there is an error, and we can
                -- use this to show feedback to the user
                pure unit
              -- otherwise this should be one of the wallet's WalletFollowerApps
              else case runExcept $ decodeJSON $ unwrap rawJson of
                Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
                Right contractHistory -> case contractHistory of
                  None -> pure unit -- we can ignore this; we'll get another update with history when it's ready
                  History marloweParams marloweData transactionInputs -> do
                    currentSlot <- use _currentSlot
                    case lookup plutusAppId (view _allContracts playState) of
                      Just contractState -> modifying (_playState <<< _allContracts) $ insert plutusAppId $ Contract.updateState currentSlot transactionInputs contractState
                      Nothing -> do
                        let
                          walletDetails = view _walletDetails playState

                          mContractState = Contract.mkInitialState walletDetails currentSlot plutusAppId contractHistory
                        case mContractState of
                          Just contractState -> do
                            modifying (_playState <<< _allContracts) $ insert plutusAppId contractState
                            handleAction $ PlayAction $ Play.ContractHomeAction $ ContractHome.OpenContract plutusAppId
                            addToast $ successToast "You have been given a role in a new contract."
                          Nothing -> addToast $ errorToast "Could not determine contract type." $ Just "You have been given a role in a new contract, but we could not determine the type of the contract and therefore cannot display it."
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
  ManageMarlowe m =>
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
      handleAction $ PickupAction $ Pickup.OpenPickupWalletCardWithDetails walletDetails
  -- FIXME: Remove after the PAB is connected
  void $ subscribe $ localStorageEvents $ const $ PlayAction $ Play.UpdateFromStorage

handleAction (EnterPickupState walletLibrary walletDetails followerApps) = do
  unsubscribeFromWallet $ view (_walletInfo <<< _wallet) walletDetails
  unsubscribeFromPlutusApp $ view _companionAppId walletDetails
  let
    followerAppIds :: Array PlutusAppId
    followerAppIds = Set.toUnfoldable $ keys followerApps
  for_ followerAppIds unsubscribeFromPlutusApp
  assign _subState $ Left $ Pickup.mkInitialState walletLibrary
  liftEffect $ removeItem walletDetailsLocalStorageKey

handleAction (EnterPlayState walletLibrary walletDetails) = do
  ajaxFollowerApps <- getFollowerApps walletDetails
  currentSlot <- use _currentSlot
  case ajaxFollowerApps of
    Left decodedAjaxError -> do
      handleAction $ PickupAction Pickup.CloseCard
      addToast $ decodedAjaxErrorToast "Failed to load wallet contracts." decodedAjaxError
    Right followerApps -> do
      subscribeToWallet $ view (_walletInfo <<< _wallet) walletDetails
      subscribeToPlutusApp $ view _companionAppId walletDetails
      timezoneOffset <- liftEffect getTimezoneOffset
      let
        followerAppIds :: Array PlutusAppId
        followerAppIds = Set.toUnfoldable $ keys followerApps
      for_ followerAppIds subscribeToPlutusApp
      assign _subState $ Right $ Play.mkInitialState walletLibrary walletDetails followerApps currentSlot timezoneOffset
      liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON walletDetails
      -- we now have all the running contracts for this wallet, but if new role tokens have been given to the
      -- wallet since we last picked it up, we have to create FollowerApps for those contracts here
      ajaxRoleContracts <- getRoleContracts walletDetails
      case ajaxRoleContracts of
        Left decodedAjaxError -> do
          handleAction $ PickupAction Pickup.CloseCard
          addToast $ decodedAjaxErrorToast "Failed to load wallet contracts." decodedAjaxError
        Right companionState -> handleAction $ PlayAction $ Play.UpdateRunningContracts companionState

handleAction (PickupAction pickupAction) = toPickup $ Pickup.handleAction pickupAction

handleAction (PlayAction playAction) = do
  currentSlot <- use _currentSlot
  let
    inputs = { currentSlot }
  toPlay $ Play.handleAction inputs playAction

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

toToast ::
  forall m msg slots.
  Functor m =>
  HalogenM Toast.State Toast.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toToast = mapSubmodule _toast ToastAction
