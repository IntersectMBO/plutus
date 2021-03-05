module MainFrame.State (mkMainFrame) where

import Prelude
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, over, set, use)
import Data.Map (empty, insert, member)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Effect.Aff.Class (class MonadAff)
import Effect.Random (random)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_)
import Halogen.HTML (HTML)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _newWalletNicknameKey, _pickupState, _subState, _playState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Pickup.State (handleAction, initialState) as Pickup
import Pickup.Types (Action(..), Card(..)) as Pickup
import Play.State (handleAction, mkInitialState) as Play
import Play.Types (Action(..)) as Play
import Plutus.PAB.Webserver.Types (StreamToClient(..))
import StaticData (walletLocalStorageKey, walletsLocalStorageKey)
import WalletData.Lenses (_key, _nickname)
import WalletData.Types (WalletDetails)
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
  , newWalletNicknameKey: mempty
  , templates: contractTemplates
  , subState: Left Pickup.initialState
  , webSocketStatus: WebSocketClosed Nothing
  }

defaultWalletDetails :: WalletDetails
defaultWalletDetails = { userHasPickedUp: false }

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
  mCachedWalletsJson <- liftEffect $ getItem walletsLocalStorageKey
  for_ mCachedWalletsJson \json ->
    for_ (runExcept $ decodeJSON json) \cachedWallets ->
      assign _wallets cachedWallets
  mCachedWalletJson <- liftEffect $ getItem walletLocalStorageKey
  for_ mCachedWalletJson \json ->
    for_ (runExcept $ decodeJSON json) \cachedWallet ->
      assign _subState $ Right $ Play.mkInitialState cachedWallet

handleAction (SetNewWalletNickname nickname) = assign (_newWalletNicknameKey <<< _nickname) nickname

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletNicknameKey <- use _newWalletNicknameKey
  when (not $ member newWalletNicknameKey oldWallets) do
    modify_
      $ (over _wallets) (insert newWalletNicknameKey defaultWalletDetails)
      <<< set _newWalletNicknameKey mempty
      <<< set (_playState <<< _card) Nothing
    newWallets <- use _wallets
    liftEffect $ setItem walletsLocalStorageKey $ encodeJSON newWallets

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PickupAction Pickup.PickupNewWallet) = do
  newPubKey <- use (_newWalletNicknameKey <<< _key)
  handleAction AddNewWallet
  handleAction $ PickupAction $ Pickup.PickupWallet newPubKey

handleAction (PickupAction (Pickup.PickupWallet pubKey)) = do
  modify_
    $ set _subState (Right $ Play.mkInitialState pubKey)
    <<< set (_pickupState <<< _card) Nothing
  liftEffect $ setItem walletLocalStorageKey $ encodeJSON pubKey

-- TODO: generate wallet on the backend; for now just create a random number
handleAction (PickupAction Pickup.GenerateNewWallet) = do
  randomNumber <- liftEffect random
  let
    key = show $ randomNumber
  modify_
    $ set (_newWalletNicknameKey <<< _key) key
    <<< set (_pickupState <<< _card) (Just Pickup.PickupNewWalletCard)

handleAction (PickupAction (Pickup.LookupWallet string)) = do
  wallets <- use _wallets
  -- check for a matching nickname in the wallet library first
  case findIndex (\key -> fst key == string) wallets of
    Just key -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard key
    -- failing that, check for a matching pubkey in the wallet library
    Nothing -> case findIndex (\key -> snd key == string) wallets of
      Just key -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard key
      -- TODO: lookup pubkey on the blockchain
      Nothing -> pure unit

-- other pickup actions
handleAction (PickupAction pickupAction) = Pickup.handleAction pickupAction

-- play actions that need to be handled here
handleAction (PlayAction Play.PutdownWallet) = do
  assign _subState $ Left Pickup.initialState
  liftEffect $ removeItem walletLocalStorageKey

handleAction (PlayAction (Play.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PlayAction (Play.SetNewWalletKey key)) = assign (_newWalletNicknameKey <<< _key) key

handleAction (PlayAction Play.AddNewWallet) = handleAction AddNewWallet

-- other play actions
handleAction (PlayAction playAction) = Play.handleAction playAction
