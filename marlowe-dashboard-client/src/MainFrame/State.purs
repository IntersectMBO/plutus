module MainFrame.State (mkMainFrame, handleAction) where

import Prelude
import Bridge (toFront)
import Capability.Marlowe (class ManageMarlowe, getFollowerApps, getRoleContracts, subscribeToPlutusApp, subscribeToWallet, unsubscribeFromPlutusApp, unsubscribeFromWallet)
import Capability.MarloweStorage (class ManageMarloweStorage, getContractNicknames, getWalletLibrary)
import Capability.Toast (class Toast, addToast)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Class (ask)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, use, view)
import Data.Lens.Extra (peruse)
import Data.Map (keys)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Set (toUnfoldable) as Set
import Data.Traversable (for)
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Env (DataProvider(..), Env)
import Foreign.Generic (decodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, subscribe)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.LocalStorage (localStorageEvents)
import MainFrame.Lenses (_currentSlot, _playState, _subState, _toast, _webSocketStatus, _welcomeState)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.PAB (PlutusAppId)
import Play.Lenses (_allContracts, _walletDetails)
import Play.State (dummyState, handleAction, mkInitialState) as Play
import Play.Types (Action(..), State) as Play
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..), InstanceStatusToClient(..))
import Toast.State (defaultState, handleAction) as Toast
import Toast.Types (Action, State) as Toast
import Toast.Types (decodedAjaxErrorToast, decodingErrorToast)
import WalletData.Lenses (_assets, _companionAppId, _marloweAppId, _previousCompanionAppState, _wallet, _walletInfo)
import WebSocket.Support as WS
import Welcome.Lenses (_walletLibrary)
import Welcome.State (handleAction, dummyState, mkInitialState) as Welcome
import Welcome.Types (Action(..), Card(..), State) as Welcome

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
  , subState: Left Welcome.dummyState
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
        { dataProvider } <- ask
        subscribeToWallet dataProvider wallet
        for followAppIds $ subscribeToPlutusApp dataProvider
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
            -- if this is the wallet's WalletCompanion app...
            if (plutusAppId == walletCompanionAppId) then case runExcept $ decodeJSON $ unwrap rawJson of
              Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
              Right companionAppState ->
                -- this check shouldn't be necessary, but at the moment we are getting too many update notifications
                -- through the PAB - so until that bug is fixed, this will have to mask it
                when (view (_walletDetails <<< _previousCompanionAppState) playState /= Just companionAppState) do
                  assign (_playState <<< _walletDetails <<< _previousCompanionAppState) (Just companionAppState)
                  handleAction $ PlayAction $ Play.UpdateFollowerApps companionAppState
            else do
              let
                marloweAppId = view (_walletDetails <<< _marloweAppId) playState
              -- if this is the wallet's MarloweApp...
              if (plutusAppId == marloweAppId) then
                -- TODO: in the future the Marlowe app's state will change when there is an error, and we can
                -- use this to show feedback to the user
                pure unit
              -- otherwise this should be one of the wallet's WalletFollowerApps
              else case runExcept $ decodeJSON $ unwrap rawJson of
                Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
                Right contractHistory -> handleAction $ PlayAction $ Play.UpdateContract plutusAppId contractHistory
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
  ManageMarloweStorage m =>
  Toast m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
-- mainframe actions
handleAction Init = do
  walletLibrary <- getWalletLibrary
  assign (_welcomeState <<< _walletLibrary) walletLibrary
  { dataProvider } <- ask
  when (dataProvider == LocalStorage) (void $ subscribe $ localStorageEvents $ const $ PlayAction $ Play.UpdateFromStorage)

handleAction (EnterWelcomeState walletLibrary walletDetails followerApps) = do
  { dataProvider } <- ask
  let
    followerAppIds :: Array PlutusAppId
    followerAppIds = Set.toUnfoldable $ keys followerApps
  unsubscribeFromWallet dataProvider $ view (_walletInfo <<< _wallet) walletDetails
  unsubscribeFromPlutusApp dataProvider $ view _companionAppId walletDetails
  for_ followerAppIds $ unsubscribeFromPlutusApp dataProvider
  assign _subState $ Left $ Welcome.mkInitialState walletLibrary

handleAction (EnterPlayState walletLibrary walletDetails) = do
  ajaxFollowerApps <- getFollowerApps walletDetails
  currentSlot <- use _currentSlot
  case ajaxFollowerApps of
    Left decodedAjaxError -> do
      handleAction $ WelcomeAction $ Welcome.CloseCard Welcome.UseWalletCard
      handleAction $ WelcomeAction $ Welcome.CloseCard Welcome.UseNewWalletCard
      addToast $ decodedAjaxErrorToast "Failed to load wallet contracts." decodedAjaxError
    Right followerApps -> do
      { dataProvider } <- ask
      let
        followerAppIds :: Array PlutusAppId
        followerAppIds = Set.toUnfoldable $ keys followerApps
      subscribeToWallet dataProvider $ view (_walletInfo <<< _wallet) walletDetails
      subscribeToPlutusApp dataProvider $ view _companionAppId walletDetails
      for_ followerAppIds $ subscribeToPlutusApp dataProvider
      timezoneOffset <- liftEffect getTimezoneOffset
      contractNicknames <- getContractNicknames
      assign _subState $ Right $ Play.mkInitialState walletLibrary walletDetails followerApps contractNicknames currentSlot timezoneOffset
      -- we now have all the running contracts for this wallet, but if new role tokens have been given to the
      -- wallet since we last picked it up, we have to create FollowerApps for those contracts here
      ajaxRoleContracts <- getRoleContracts walletDetails
      case ajaxRoleContracts of
        Left decodedAjaxError -> do
          handleAction $ WelcomeAction $ Welcome.CloseCard Welcome.UseWalletCard
          handleAction $ WelcomeAction $ Welcome.CloseCard Welcome.UseNewWalletCard
          addToast $ decodedAjaxErrorToast "Failed to load wallet contracts." decodedAjaxError
        Right companionState -> handleAction $ PlayAction $ Play.UpdateFollowerApps companionState

handleAction (WelcomeAction welcomeAction) = toWelcome $ Welcome.handleAction welcomeAction

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
toWelcome ::
  forall m msg slots.
  Functor m =>
  HalogenM Welcome.State Welcome.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWelcome = mapMaybeSubmodule _welcomeState WelcomeAction Welcome.dummyState

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
