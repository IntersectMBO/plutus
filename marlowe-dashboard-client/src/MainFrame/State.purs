module MainFrame.State (mkMainFrame, handleAction) where

import Prologue
import Bridge (toFront)
import Capability.Marlowe (class ManageMarlowe, getFollowerApps, subscribeToPlutusApp, subscribeToWallet, unsubscribeFromPlutusApp, unsubscribeFromWallet)
import Capability.MarloweStorage (class ManageMarloweStorage, getContractNicknames, getWalletLibrary)
import Capability.PlutusApps.MarloweApp as MarloweApp
import Capability.PlutusApps.MarloweApp.Types (LastResult(..))
import Capability.Toast (class Toast, addToast)
import Clipboard (class MonadClipboard)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Class (ask)
import Dashboard.Lenses (_contracts, _walletDetails)
import Dashboard.State (dummyState, handleAction, mkInitialState) as Dashboard
import Dashboard.Types (Action(..), State) as Dashboard
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Map (keys)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Set (toUnfoldable) as Set
import Data.Time.Duration (Minutes(..))
import Data.Traversable (for)
import Effect.Aff.Class (class MonadAff)
import Env (DataProvider(..), Env)
import Foreign.Generic (decodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, subscribe)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import Halogen.HTML (HTML)
import Halogen.LocalStorage (localStorageEvents)
import Humanize (getTimezoneOffset)
import MainFrame.Lenses (_currentSlot, _dashboardState, _subState, _toast, _tzOffset, _webSocketStatus, _welcomeState)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.PAB (PlutusAppId)
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient(..), InstanceStatusToClient(..))
import Toast.State (defaultState, handleAction) as Toast
import Toast.Types (Action, State) as Toast
import Toast.Types (decodedAjaxErrorToast, decodingErrorToast, errorToast, successToast)
import Contacts.Lenses (_assets, _companionAppId, _marloweAppId, _previousCompanionAppState, _wallet, _walletInfo)
import WebSocket.Support as WS
import Welcome.Lenses (_walletLibrary)
import Welcome.State (handleAction, dummyState, mkInitialState) as Welcome
import Welcome.Types (Action, State) as Welcome

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
  Toast m =>
  MonadClipboard m =>
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
  , tzOffset: Minutes 0.0 -- This will be updated on MainFrame.Init
  }

handleQuery ::
  forall a m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
  Toast m =>
  MonadClipboard m =>
  Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    WS.WebSocketOpen -> do
      assign _webSocketStatus WebSocketOpen
      -- potentially renew websocket subscriptions
      mDashboardState <- peruse _dashboardState
      for_ mDashboardState \dashboardState -> do
        let
          wallet = view (_walletDetails <<< _walletInfo <<< _wallet) dashboardState

          followAppIds :: Array PlutusAppId
          followAppIds = Set.toUnfoldable $ keys $ view _contracts dashboardState
        subscribeToWallet wallet
        for followAppIds $ subscribeToPlutusApp
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
        handleAction $ DashboardAction Dashboard.AdvanceTimedoutSteps
      -- update the wallet funds (if the change is to the current wallet)
      -- note: we should only ever be notified of changes to the current wallet, since we subscribe to
      -- this update when we pick it up, and unsubscribe when we put it down - but we check here
      -- anyway in case
      WalletFundsChange wallet value -> do
        mCurrentWallet <- peruse (_dashboardState <<< _walletDetails <<< _walletInfo <<< _wallet)
        for_ mCurrentWallet \currentWallet -> do
          when (currentWallet == toFront wallet)
            $ assign (_dashboardState <<< _walletDetails <<< _assets) (toFront value)
      -- update the state when a contract instance changes
      -- note: we should be subscribed to updates from all (and only) the current wallet's contract
      -- instances, including its wallet companion contract
      InstanceUpdate contractInstanceId instanceStatusToClient -> case instanceStatusToClient of
        NewObservableState rawJson -> do
          -- TODO: If we receive a second status update for the same contract / plutus app, while
          -- the previous update is still being handled, then strange things could happen. This
          -- does not seem very likely. Still, it might be worth considering guarding against this
          -- possibility by e.g. keeping a list/array of updates and having a subscription that
          -- handles them synchronously in the order in which they arrive.
          let
            plutusAppId = toFront contractInstanceId
          mDashboardState <- peruse _dashboardState
          -- these updates should only ever be coming when we are in the Dashboard state (and if
          -- we're not, we don't care about them anyway)
          for_ mDashboardState \dashboardState ->
            let
              walletCompanionAppId = view (_walletDetails <<< _companionAppId) dashboardState

              marloweAppId = view (_walletDetails <<< _marloweAppId) dashboardState
            in
              -- if this is the wallet's WalletCompanion app...
              if (plutusAppId == walletCompanionAppId) then case runExcept $ decodeJSON $ unwrap rawJson of
                Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
                Right companionAppState -> do
                  -- this check shouldn't be necessary, but at the moment we are getting too many update notifications
                  -- through the PAB - so until that bug is fixed, this will have to mask it
                  when (view (_walletDetails <<< _previousCompanionAppState) dashboardState /= Just companionAppState) do
                    assign (_dashboardState <<< _walletDetails <<< _previousCompanionAppState) (Just companionAppState)
                    handleAction $ DashboardAction $ Dashboard.UpdateFollowerApps companionAppState
              else do
                -- if this is the wallet's MarloweApp...
                if (plutusAppId == marloweAppId) then case runExcept $ decodeJSON $ unwrap rawJson of
                  Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
                  Right lastResult -> case lastResult of
                    OK "create" -> addToast $ successToast "Contract initialised."
                    OK "apply-inputs" -> addToast $ successToast "Contract update applied."
                    SomeError "create" marloweError -> addToast $ errorToast "Failed to initialise contract." Nothing
                    SomeError "apply-inputs" marloweError -> addToast $ errorToast "Failed to update contract." Nothing
                    _ -> pure unit
                -- otherwise this should be one of the wallet's WalletFollowerApps
                else case runExcept $ decodeJSON $ unwrap rawJson of
                  Left decodingError -> addToast $ decodingErrorToast "Failed to parse contract update." decodingError
                  Right contractHistory -> do
                    handleAction $ DashboardAction $ Dashboard.UpdateContract plutusAppId contractHistory
                    handleAction $ DashboardAction $ Dashboard.RedeemPayments plutusAppId
        NewActiveEndpoints activeEndpoints -> do
          mDashboardState <- peruse _dashboardState
          -- these updates should only ever be coming when we are in the Dashboard state (and if
          -- we're not, we don't care about them anyway)
          for_ mDashboardState \dashboardState -> do
            let
              plutusAppId = toFront contractInstanceId

              marloweAppId = view (_walletDetails <<< _marloweAppId) dashboardState
            when (plutusAppId == marloweAppId) $ MarloweApp.onNewActiveEndpoints activeEndpoints
        ContractFinished _ -> pure unit
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
  MonadClipboard m =>
  Action ->
  HalogenM State Action ChildSlots Msg m Unit
-- mainframe actions
handleAction Init = do
  tzOffset <- liftEffect getTimezoneOffset
  walletLibrary <- getWalletLibrary
  modify_
    $ set (_welcomeState <<< _walletLibrary) walletLibrary
    <<< set _tzOffset tzOffset
  { dataProvider } <- ask
  when (dataProvider == LocalStorage) (void $ subscribe $ localStorageEvents $ const $ DashboardAction $ Dashboard.UpdateFromStorage)

handleAction (EnterWelcomeState walletLibrary walletDetails followerApps) = do
  let
    followerAppIds :: Array PlutusAppId
    followerAppIds = Set.toUnfoldable $ keys followerApps
  unsubscribeFromWallet $ view (_walletInfo <<< _wallet) walletDetails
  unsubscribeFromPlutusApp $ view _companionAppId walletDetails
  unsubscribeFromPlutusApp $ view _marloweAppId walletDetails
  for_ followerAppIds unsubscribeFromPlutusApp
  assign _subState $ Left $ Welcome.mkInitialState walletLibrary

handleAction (EnterDashboardState walletLibrary walletDetails) = do
  ajaxFollowerApps <- getFollowerApps walletDetails
  currentSlot <- use _currentSlot
  case ajaxFollowerApps of
    Left decodedAjaxError -> addToast $ decodedAjaxErrorToast "Failed to load wallet contracts." decodedAjaxError
    Right followerApps -> do
      let
        followerAppIds :: Array PlutusAppId
        followerAppIds = Set.toUnfoldable $ keys followerApps
      subscribeToWallet $ view (_walletInfo <<< _wallet) walletDetails
      subscribeToPlutusApp $ view _companionAppId walletDetails
      subscribeToPlutusApp $ view _marloweAppId walletDetails
      for_ followerAppIds subscribeToPlutusApp
      -- we now have all the running contracts for this wallet, but if new role tokens have been
      -- given to the wallet since we last connected it, we'll need to create some more - but since
      -- we've just subscribed to the wallet companion contract, this will be triggered by the
      -- initial websocket status notification
      contractNicknames <- getContractNicknames
      assign _subState $ Right $ Dashboard.mkInitialState walletLibrary walletDetails followerApps contractNicknames currentSlot

handleAction (WelcomeAction welcomeAction) = toWelcome $ Welcome.handleAction welcomeAction

handleAction (DashboardAction dashboardAction) = do
  currentSlot <- use _currentSlot
  tzOffset <- use _tzOffset
  toDashboard $ Dashboard.handleAction { currentSlot, tzOffset } dashboardAction

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

toDashboard ::
  forall m msg slots.
  Functor m =>
  HalogenM Dashboard.State Dashboard.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toDashboard = mapMaybeSubmodule _dashboardState DashboardAction Dashboard.dummyState

toToast ::
  forall m msg slots.
  Functor m =>
  HalogenM Toast.State Toast.Action slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toToast = mapSubmodule _toast ToastAction
