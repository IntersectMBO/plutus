module MainFrame.State (mkMainFrame) where

import Prelude

import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, over, set, use, view)
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
import MainFrame.Lenses (_card, _newWalletDetails, _newWalletPubKey, _pickupState, _subState, _templates, _playState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Network.RemoteData (RemoteData(..))
import Pickup.State (handleAction, initialState) as Pickup
import Pickup.Types (Action(..), Card(..)) as Pickup
import Play.State (handleAction, mkInitialState) as Play
import Play.Types (Action(..)) as Play
import Plutus.PAB.Webserver.Types (StreamToClient(..))
import StaticData (walletLocalStorageKey, walletsLocalStorageKey)
import WalletData.Lenses (_contractId, _nickname)
import WalletData.Types (WalletDetails)
import WebSocket.Support as WS
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)

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
  , newWalletDetails: defaultWalletDetails
  , newWalletPubKey: NotAsked
  , templates: contractTemplates
  , subState: Left Pickup.initialState
  , webSocketStatus: WebSocketClosed Nothing
  }

defaultWalletDetails :: WalletDetails
defaultWalletDetails = { nickname: mempty, contractID: mempty, pubKey: mempty, balance: NotAsked }

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
  mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
  for_ mWalletLibraryJson \json ->
    for_ (runExcept $ decodeJSON json) \wallets ->
      assign _wallets wallets
  mWalletDetailsJson <- liftEffect $ getItem walletDetailsLocalStorageKey
  for_ mWalletDetailsJson \json ->
    for_ (runExcept $ decodeJSON json) \walletDetails ->
      assign _subState $ Right $ Play.mkInitialState walletDetails

handleAction (AddWallet walletDetails) = do
  oldWallets <- use _wallets
  let
    newWalletNickname = view _nickname walletDetails
  when (not $ member newWalletNickname oldWallets) do
    modify_
      $ (over _wallets) (insert newWalletNickname walletDetails)
      <<< set _newWalletDetails { nickname: mempty, contractId: mempty, pubKey: mempty, balance: NotAsked }
      <<< set (_playState <<< _card) Nothing
    newWallets <- use _wallets
    liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWallets

handleAction (SetNewWalletNickname nickname) = assign (_newWalletDetails <<< _nickname) nickname

handleAction (SetNewWalletContractId contractId) = assign (_newWalletDetails <<< _contractId) contractId

handleAction FetchNewWalletPubKey = do
  contractId <- use (_newWalletDetails <<< _contractId)
  -- TODO: lookup wallet pubKey from the PAB using the wallet's companion contract ID
  randomNumber <- liftEffect random
  let
    pubKey = show randomNumber
  assign _newWalletPubKey $ Success pubKey

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PickupAction (Pickup.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractId contractId

handleAction (PickupAction Pickup.PickupNewWallet) = do
  nickname <- use (_newWalletDetails <<< _nickname)
  contractId <- use (_newWalletDetails <<< _contractId)
  --TODO: use the contract ID to lookup the wallet's public key from PAB
  randomNumber <- liftEffect random
  let
    pubKey = show randomNumber

    walletDetails = { nickname, contractId, pubKey, balance: NotAsked }
  handleAction $ AddWallet walletDetails
  handleAction $ PickupAction $ Pickup.PickupWallet walletDetails

handleAction (PickupAction (Pickup.PickupWallet walletDetails)) = do
  -- TODO: fetch current balance of the wallet from PAB
  -- TODO: open up websocket to this wallet's companion contract from PAB
  modify_
    $ set _subState (Right $ Play.mkInitialState walletDetails)
    <<< set (_pickupState <<< _card) Nothing
  liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON walletDetails

handleAction (PickupAction Pickup.GenerateNewWallet) = do
  -- TODO: ask PAB to generate a new wallet and get the wallet's companion contract ID in return
  randomNumber <- liftEffect random
  let
    contractId = show $ randomNumber
  modify_
    $ set (_newWalletDetails <<< _contractId) contractId
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
  liftEffect $ removeItem walletDetailsLocalStorageKey

handleAction (PlayAction (Play.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNickname nickname

handleAction (PlayAction (Play.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractId contractId

handleAction (PlayAction (Play.AddWallet walletDetails)) = handleAction $ AddWallet walletDetails

-- other play actions
handleAction (PlayAction playAction) = Play.handleAction playAction
