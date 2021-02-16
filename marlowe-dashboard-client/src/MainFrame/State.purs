module MainFrame.State (mkMainFrame) where

import Prelude
import Contract.State (handleAction, initialState) as Contract
import Contract.Types (Action(..)) as Contract
import Contract.Types (_executionState)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, set, use)
import Data.Lens.Extra (peruse)
import Data.Map (empty, insert, member)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
import Effect.Aff.Class (class MonadAff)
import Effect.Random (random)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_, raise)
import Halogen.Extra (mapSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _contractState, _insideState, _menuOpen, _newWalletNicknameKey, _on, _outsideState, _screen, _subState, _wallets)
import MainFrame.Types (Action(..), ChildSlots, ContractStatus(..), InsideState, Msg(..), OutsideCard(..), OutsideScreen(..), OutsideState, Query(..), Screen(..), State)
import MainFrame.View (render)
import Marlowe.Execution (_contract)
import Marlowe.Semantics (Contract(..))
import StaticData (walletLocalStorageKey, walletsLocalStorageKey)
import Wallet.Lenses (_key, _nickname)
import Wallet.Types (PubKeyHash, WalletDetails(..), WalletNicknameKey)
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
  , newWalletNicknameKey: emptyWalletNicknameKey
  , subState: Left initialOutsideState
  , contractState: Contract.initialState zero Close
  }

initialOutsideState :: OutsideState
initialOutsideState =
  { screen: GenerateWalletScreen
  , card: Nothing
  }

mkInsideState :: PubKeyHash -> InsideState
mkInsideState pubKeyHash =
  { wallet: pubKeyHash
  , menuOpen: false
  , screen: ContractsScreen Running
  , card: Nothing
  , on: true
  }

emptyWalletNicknameKey :: WalletNicknameKey
emptyWalletNicknameKey = Tuple "" ""

defaultWalletDetails :: WalletDetails
defaultWalletDetails = WalletDetails { userHasPickedUp: false }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  case msg of
    (WS.ReceiveMessage (Right (ClientMsg on))) -> assign (_insideState <<< _on) on
    -- TODO: other matches such as update current slot or apply transaction
    _ -> pure unit
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = do
  mCachedWalletsJson <- liftEffect $ getItem walletsLocalStorageKey
  for_ mCachedWalletsJson
    $ \json -> do
        let
          wallets =
            runExcept do
              decodeJSON json
        case wallets of
          Right cachedWallets -> assign _wallets cachedWallets
          _ -> pure unit
  mCachedWalletJson <- liftEffect $ getItem walletLocalStorageKey
  for_ mCachedWalletJson
    $ \json -> do
        let
          wallet =
            runExcept do
              decodeJSON json
        case wallet of
          Right cachedWallet -> assign _subState $ Right $ mkInsideState cachedWallet
          _ -> pure unit

-- outside actions
handleAction (SetOutsideCard outsideCard) = assign (_outsideState <<< _card) outsideCard

-- TODO: generate wallet on the backend; for now just create a random number
handleAction GenerateNewWallet = do
  randomNumber <- liftEffect random
  let
    key = show $ randomNumber
  modify_
    $ (_newWalletNicknameKey <<< set _key) key
    <<< (_outsideState <<< set _card) (Just PickupNewWalletCard)

handleAction PickupNewWallet = do
  newPubKeyHash <- use (_newWalletNicknameKey <<< _key)
  handleAction AddNewWallet
  handleAction $ PickupWallet newPubKeyHash

handleAction (LookupWallet string) = do
  wallets <- use _wallets
  for_ (findIndex (\key -> fst key == string) wallets) $ \key -> assign (_outsideState <<< _card) $ Just $ PickupWalletCard key

handleAction (PickupWallet pubKeyHash) = do
  modify_
    $ (set _subState) (Right $ mkInsideState pubKeyHash)
    <<< (_outsideState <<< set _card) Nothing
  liftEffect $ setItem walletLocalStorageKey $ encodeJSON pubKeyHash

-- inside actions
handleAction PutdownWallet = do
  assign _subState $ Left initialOutsideState
  liftEffect $ removeItem walletLocalStorageKey

handleAction ToggleMenu = modifying (_insideState <<< _menuOpen) not

handleAction (SetScreen screen) =
  modify_
    $ (_insideState <<< set _menuOpen) false
    <<< (_insideState <<< set _card) Nothing
    <<< (_insideState <<< set _screen) screen

handleAction (SetCard card) = do
  previousCard <- peruse (_insideState <<< _card)
  assign (_insideState <<< _card) card
  for_ previousCard $ const $ assign (_insideState <<< _menuOpen) false

handleAction (ToggleCard card) = do
  mCurrentCard <- peruse (_insideState <<< _card)
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
    modifying _wallets $ insert newWalletNicknameKey defaultWalletDetails
    assign _newWalletNicknameKey emptyWalletNicknameKey
    newWallets <- use _wallets
    liftEffect $ setItem walletsLocalStorageKey $ encodeJSON newWallets
    assign (_insideState <<< _card) Nothing

handleAction ClickedButton = do
  mCurrent <- peruse (_insideState <<< _on)
  for_ mCurrent $ \current -> raise (SendWebSocketMessage (ServerMsg current))

-- contract actions
handleAction (ContractAction contractAction) = do
  case contractAction of
    Contract.ClosePanel -> pure unit
    action -> mapSubmodule _contractState ContractAction $ Contract.handleAction action

handleAction (StartContract contract) = assign (_contractState <<< _executionState <<< _contract) contract
