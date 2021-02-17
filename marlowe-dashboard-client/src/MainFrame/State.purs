module MainFrame.State (mkMainFrame) where

import Prelude
import Contract.State (handleAction, initialState) as Contract
import Contract.Types (Action(..)) as Contract
import Contract.Types (_executionState)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, over, set, use)
import Data.Lens.Extra (peruse)
import Data.Map (empty, insert, member)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Effect.Aff.Class (class MonadAff)
import Effect.Random (random)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, raise)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _contractState, _walletState, _menuOpen, _newWalletNicknameKey, _on, _pickupState, _screen, _subState, _wallets)
import MainFrame.Types (Action(..), ChildSlots, ContractStatus(..), WalletState, Msg(..), PickupCard(..), PickupScreen(..), PickupState, Query(..), Screen(..), State)
import MainFrame.View (render)
import Marlowe.Execution (_contract)
import Marlowe.Semantics (Contract(..), PubKey)
import StaticData (walletLocalStorageKey, walletsLocalStorageKey)
import Wallet.Lenses (_key, _nickname)
import Wallet.Types (WalletDetails)
import WebSocket (StreamToClient(..), StreamToServer(..))
import WebSocket.Support as WS

mkMainFrame :: forall m. MonadAff m => Component HTML Query Action Msg m
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
  , subState: Left initialPickupState
  , contractState: Contract.initialState zero Close
  }

initialPickupState :: PickupState
initialPickupState =
  { screen: GenerateWalletScreen
  , card: Nothing
  }

mkWalletState :: PubKey -> WalletState
mkWalletState pubKeyHash =
  { wallet: pubKeyHash
  , menuOpen: false
  , screen: ContractsScreen Running
  , card: Nothing
  , on: true
  }

defaultWalletDetails :: WalletDetails
defaultWalletDetails = { userHasPickedUp: false }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    (WS.ReceiveMessage (Right (ClientMsg on))) -> assign (_walletState <<< _on) on
    -- TODO: other matches such as update current slot or apply transaction
    _ -> pure unit
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = do
  mCachedWalletsJson <- liftEffect $ getItem walletsLocalStorageKey
  for_ mCachedWalletsJson
    \json -> for_ (runExcept $ decodeJSON json)
      \cachedWallets -> assign _wallets cachedWallets
  mCachedWalletJson <- liftEffect $ getItem walletLocalStorageKey
  for_ mCachedWalletJson
    \json -> for_ (runExcept $ decodeJSON json)
      \cachedWallet -> assign _subState $ Right $ mkWalletState cachedWallet

-- pickup actions
handleAction (SetPickupCard pickupCard) = assign (_pickupState <<< _card) pickupCard

-- TODO: generate wallet on the backend; for now just create a random number
handleAction GenerateNewWallet = do
  randomNumber <- liftEffect random
  let
    key = show $ randomNumber
  modify_
    $ (_newWalletNicknameKey <<< set _key) key
    <<< (_pickupState <<< set _card) (Just PickupNewWalletCard)

handleAction PickupNewWallet = do
  newPubKey <- use (_newWalletNicknameKey <<< _key)
  handleAction AddNewWallet
  handleAction $ PickupWallet newPubKey

handleAction (LookupWallet string) = do
  wallets <- use _wallets
  -- check for a matching nickname in the wallet library first
  case findIndex (\key -> fst key == string) wallets of
    Just key -> assign (_pickupState <<< _card) $ Just $ PickupWalletCard key
    Nothing ->
      -- failing that, check for a matching pubkey in the wallet library
      case findIndex (\key -> snd key == string) wallets of
        Just key -> assign (_pickupState <<< _card) $ Just $ PickupWalletCard key
        Nothing ->
          -- TODO: lookup pubkey on the blockchain
          pure unit

handleAction (PickupWallet pubKeyHash) = do
  modify_
    $ (set _subState) (Right $ mkWalletState pubKeyHash)
    <<< (_pickupState <<< set _card) Nothing
  liftEffect $ setItem walletLocalStorageKey $ encodeJSON pubKeyHash

-- wallet actions
handleAction PutdownWallet = do
  assign _subState $ Left initialPickupState
  liftEffect $ removeItem walletLocalStorageKey

handleAction ToggleMenu = modifying (_walletState <<< _menuOpen) not

handleAction (SetScreen screen) =
  modify_
    $ (_walletState <<< set _menuOpen) false
    <<< (_walletState <<< set _card) Nothing
    <<< (_walletState <<< set _screen) screen

handleAction (SetCard card) = do
  previousCard <- peruse (_walletState <<< _card)
  assign (_walletState <<< _card) card
  for_ previousCard $ const $ assign (_walletState <<< _menuOpen) false

handleAction (ToggleCard card) = do
  mCurrentCard <- peruse (_walletState <<< _card)
  case mCurrentCard of
    Just currentCard
      | currentCard == Just card -> handleAction $ SetCard Nothing
    _ -> handleAction $ SetCard $ Just card

handleAction (SetNewWalletNickname nickname) = assign (_newWalletNicknameKey <<< _nickname) nickname

handleAction (SetNewWalletKey key) = assign (_newWalletNicknameKey <<< _key) key

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletNicknameKey <- use _newWalletNicknameKey
  when (not $ member newWalletNicknameKey oldWallets) do
    modify_
      $ (over _wallets) (insert newWalletNicknameKey defaultWalletDetails)
      <<< (set _newWalletNicknameKey) mempty
      <<< (_walletState <<< set _card) Nothing
    newWallets <- use _wallets
    liftEffect $ setItem walletsLocalStorageKey $ encodeJSON newWallets

handleAction ClickedButton = do
  mCurrent <- peruse (_walletState <<< _on)
  for_ mCurrent $ \current -> raise (SendWebSocketMessage (ServerMsg current))

-- contract actions
handleAction (ContractAction contractAction) = do
  case contractAction of
    Contract.ClosePanel -> pure unit
    action -> mapSubmodule _contractState ContractAction $ Contract.handleAction action

handleAction (StartContract contract) = assign (_contractState <<< _executionState <<< _contract) contract
