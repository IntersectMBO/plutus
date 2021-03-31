module MainFrame.State (mkMainFrame) where

import Prelude
import ContractHome.State (loadExistingContracts)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Rec.Class (forever)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, over, set, use)
import Data.Map (empty, filter, findMin, insert, lookup, member)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Effect.Random (random)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, subscribe)
import Halogen.HTML (HTML)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _newWalletContractId, _newWalletNickname, _remoteDataPubKey, _pickupState, _subState, _playState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Marlowe.Semantics (PubKey)
import Marlowe.Slot (currentSlot)
import Network.RemoteData (RemoteData(..))
import Pickup.State (handleAction, initialState) as Pickup
import Pickup.Types (Action(..), Card(..)) as Pickup
import Play.Lenses (_allContracts)
import Play.State (handleAction, mkInitialState) as Play
import Play.Types (Action(..)) as Play
import Plutus.PAB.Webserver.Types (StreamToClient(..))
import Servant.PureScript.Ajax (AjaxError)
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Template.State (handleAction) as Template
import Template.Types (Action(..)) as Template
import WalletData.Types (Nickname, WalletDetails)
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
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
  , newWalletNickname: mempty
  , newWalletContractId: mempty
  , remoteDataPubKey: NotAsked
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
    -- TODO: This is where the main logic of dealing with messages goes
    (WS.ReceiveMessage (Right stc)) -> case stc of
      (NewChainReport report) -> pure unit
      (NewContractReport report) -> pure unit
      (NewChainEvents events) -> pure unit
      (FetchedProperties subjectProperties) -> pure unit
      (FetchedProperty subject properties) -> pure unit
      (ErrorResponse error) -> pure unit
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

handleAction (SetNewWalletNickname nickname) = assign _newWalletNickname nickname

handleAction (SetNewWalletContractId contractId) = do
  assign _newWalletContractId contractId
  --TODO: use the contract ID to lookup the wallet's public key from PAB
  randomNumber <- liftEffect random
  let
    pubKey = show randomNumber
  assign _remoteDataPubKey $ Success pubKey

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletNickname <- use _newWalletNickname
  newWalletContractId <- use _newWalletContractId
  remoteDataPubKey <- use _remoteDataPubKey
  for_ (mkNewWallet newWalletNickname newWalletContractId remoteDataPubKey)
    $ \walletDetails ->
        when (not $ member newWalletNickname oldWallets) do
          modify_
            $ over _wallets (insert newWalletNickname walletDetails)
            <<< set _newWalletNickname mempty
            <<< set _newWalletContractId mempty
            <<< set _remoteDataPubKey NotAsked
            <<< set (_playState <<< _card) Nothing
          newWallets <- use _wallets
          liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWallets

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PickupAction (Pickup.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractId contractId

handleAction (PickupAction Pickup.PickupNewWallet) = do
  newWalletNickname <- use _newWalletNickname
  newWalletContractId <- use _newWalletContractId
  remoteDataPubKey <- use _remoteDataPubKey
  for_ (mkNewWallet newWalletNickname newWalletContractId remoteDataPubKey)
    $ \walletDetails -> do
        handleAction AddNewWallet
        handleAction $ PickupAction $ Pickup.PickupWallet walletDetails

handleAction (PickupAction (Pickup.PickupWallet walletDetails)) = do
  -- we need the local timezoneOffset in play state in order to convert datetimeLocal
  -- values to UTC (and vice versa), so we can manage date-to-slot conversions
  timezoneOffset <- liftEffect getTimezoneOffset
  -- FIXME: Remove this, only for debugging. Replace with actually loading existing contracts
  --        from the PAB.
  contracts <- liftEffect $ loadExistingContracts
  currentSlot' <- liftEffect currentSlot
  modify_
    $ set (_playState <<< _allContracts) contracts
    <<< set _subState (Right $ Play.mkInitialState walletDetails currentSlot' timezoneOffset)
    <<< set (_pickupState <<< _card) Nothing
  -- TODO: fetch current balance of the wallet from PAB
  -- TODO: open up websocket to this wallet's companion contract from PAB
  liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON walletDetails

handleAction (PickupAction Pickup.GenerateNewWallet) = do
  -- TODO: ask PAB to generate a new wallet and get the wallet's companion contract ID in return
  randomNumber <- liftEffect random
  let
    contractId = show $ randomNumber
  handleAction $ SetNewWalletContractId contractId
  assign (_pickupState <<< _card) (Just Pickup.PickupNewWalletCard)

handleAction (PickupAction (Pickup.LookupWallet string)) = do
  wallets <- use _wallets
  -- check for a matching nickname in the wallet library first
  case lookup string wallets of
    Just walletDetails -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard walletDetails
    -- failing that, check for a matching pubkey in the wallet library
    Nothing -> case findMin $ filter (\walletDetails -> walletDetails.contractId == string) wallets of
      Just { key, value } -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard value
      -- TODO: and failing that, lookup the wallet contractId from PAB
      Nothing -> pure unit

-- other pickup actions
handleAction (PickupAction pickupAction) = Pickup.handleAction pickupAction

-- play actions that need to be handled here
handleAction (PlayAction Play.PutdownWallet) = do
  assign _subState $ Left Pickup.initialState
  liftEffect $ removeItem walletDetailsLocalStorageKey

handleAction (PlayAction (Play.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PlayAction (Play.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractId contractId

handleAction (PlayAction (Play.AddNewWallet mTokenName)) = do
  walletNickname <- use _newWalletNickname
  handleAction AddNewWallet
  for_ mTokenName \tokenName ->
    Template.handleAction $ Template.SetRoleWallet tokenName walletNickname

-- other play actions
handleAction (PlayAction playAction) = Play.handleAction playAction

------------------------------------------------------------
mkNewWallet :: Nickname -> String -> RemoteData AjaxError PubKey -> Maybe WalletDetails
mkNewWallet nickname contractId remoteDataPubKey = case remoteDataPubKey of
  Success pubKey -> Just { nickname, contractId, pubKey, balance: Nothing }
  _ -> Nothing
