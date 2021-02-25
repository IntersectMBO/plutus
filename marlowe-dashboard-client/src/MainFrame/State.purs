module MainFrame.State (mkMainFrame) where

import Prelude
import Contract.State (handleAction, defaultState) as Contract
import Contract.Types (_executionState)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (Traversal', assign, modifying, over, set, use, view)
import Data.Lens.Extra (peruse)
import Data.Map (empty, insert, member)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Effect.Aff.Class (class MonadAff)
import Effect.Random (random)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_)
import Halogen.Extra (mapMaybeSubmodule)
import Halogen.HTML (HTML)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _contractState, _menuOpen, _newWalletNicknameKey, _pickupState, _screen, _templateState, _subState, _templates, _walletState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), Card(..), ChildSlots, ContractStatus(..), Msg, PickupCard(..), PickupScreen(..), PickupState, Query(..), Screen(..), State, WalletState, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Execution (_contract)
import Marlowe.Extended (fillTemplate, toCore)
import Marlowe.Semantics (PubKey)
import Plutus.PAB.Webserver.Types (StreamToClient(..))
import StaticData (walletLocalStorageKey, walletsLocalStorageKey)
import Template.Lenses (_extendedContract, _template, _templateContent)
import Template.Library (templates)
import Template.State (defaultState, handleAction, mkInitialState) as Template
import Template.Types (ContractSetupScreen(..))
import WalletData.Lenses (_key, _nickname)
import WalletData.Types (WalletDetails)
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
  , templates: mempty
  , subState: Left initialPickupState
  , webSocketStatus: WebSocketClosed Nothing
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
  , templateState: Template.defaultState
  , contractState: Contract.defaultState
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

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction Init = do
  mCachedWalletsJson <- liftEffect $ getItem walletsLocalStorageKey
  for_ mCachedWalletsJson \json ->
    for_ (runExcept $ decodeJSON json) \cachedWallets ->
      assign _wallets cachedWallets
  mCachedWalletJson <- liftEffect $ getItem walletLocalStorageKey
  for_ mCachedWalletJson \json ->
    for_ (runExcept $ decodeJSON json) \cachedWallet ->
      assign _subState $ Right $ mkWalletState cachedWallet
  -- TODO: fetch contract templates from the library ??
  assign _templates templates

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
    -- failing that, check for a matching pubkey in the wallet library
    Nothing -> case findIndex (\key -> snd key == string) wallets of
      Just key -> assign (_pickupState <<< _card) $ Just $ PickupWalletCard key
      -- TODO: lookup pubkey on the blockchain
      Nothing -> pure unit

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

-- template actions
handleAction (SetTemplate template) = do
  mCurrentTemplate <- peruse (_walletState <<< _templateState <<< _template)
  when (mCurrentTemplate /= Just template) $ assign (_walletState <<< _templateState) $ Template.mkInitialState template
  handleAction $ SetScreen $ ContractSetupScreen ContractRolesScreen

handleAction (TemplateAction templateAction) = Template.handleAction templateAction

-- contract actions
handleAction StartContract = do
  mTemplateState <- peruse (_walletState <<< _templateState)
  for_ mTemplateState \templateState ->
    let
      extendedContract = view (_template <<< _extendedContract) templateState

      templateContent = view _templateContent templateState

      mContract = toCore $ fillTemplate templateContent extendedContract
    in
      for_ mContract \contract -> do
        assign (_walletState <<< _contractState <<< _executionState <<< _contract) contract
        handleAction $ SetScreen $ ContractsScreen Running
        handleAction $ ToggleCard ContractCard

handleAction (ContractAction contractAction) = handleSubAction (_walletState <<< _contractState) ContractAction Contract.defaultState (Contract.handleAction contractAction)

-- there must be a nicer way to get the current state than by manually
-- piecing together each of its properties, but I haven't found it :(
handleSubAction ::
  forall m state' action'.
  MonadAff m =>
  Traversal' State state' ->
  (action' -> Action) ->
  state' ->
  HalogenM state' action' ChildSlots Msg m Unit ->
  HalogenM State Action ChildSlots Msg m Unit
handleSubAction traversal wrapper submoduleInitialState submoduleHandleAction = do
  wallets <- use _wallets
  newWalletNicknameKey <- use _newWalletNicknameKey
  templates <- use _templates
  subState <- use _subState
  webSocketStatus <- use _webSocketStatus
  let
    state = { wallets, newWalletNicknameKey, templates, subState, webSocketStatus }
  mapMaybeSubmodule state traversal wrapper submoduleInitialState submoduleHandleAction
