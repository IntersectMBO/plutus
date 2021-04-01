module MainFrame.State (mkMainFrame) where

import Prelude
import Bridge (contractInstanceIdFromString)
import Capability.Contract (class MonadContract)
import Capability.Wallet (class MonadWallet, createWallet, getWalletPubKey, getWalletTotalFunds)
import Control.Monad.Except (runExcept)
import Control.Monad.Reader (class MonadAsk)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, over, set, use, view)
import Data.Map (empty, filter, findMin, insert, lookup, member)
import Data.Maybe (Maybe(..))
import Data.UUID (emptyUUID)
import Effect.Aff.Class (class MonadAff)
import Effect.Now (getTimezoneOffset)
import Env (Env)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (Component, HalogenM, liftEffect, mkComponent, mkEval, modify_)
import Halogen.HTML (HTML)
import LocalStorage (getItem, removeItem, setItem)
import MainFrame.Lenses (_card, _newWalletDetails, _pickupState, _subState, _playState, _wallets, _webSocketStatus)
import MainFrame.Types (Action(..), ChildSlots, Msg, Query(..), State, WebSocketStatus(..))
import MainFrame.View (render)
import Marlowe.Market (contractTemplates)
import Network.RemoteData (RemoteData(..))
import Pickup.State (handleAction, initialState) as Pickup
import Pickup.Types (Action(..), Card(..)) as Pickup
import Play.State (handleAction, handleQuery, mkInitialState) as Play
import Play.Types (Action(..)) as Play
import StaticData (walletDetailsLocalStorageKey, walletLibraryLocalStorageKey)
import Template.State (handleAction) as Template
import Template.Types (Action(..)) as Template
import Wallet.Emulator.Wallet (Wallet(..))
import WalletData.Lenses (_contractInstanceId, _contractInstanceIdAsString, _contractInstanceIdString, _remoteDataPubKey, _remoteDataWallet, _remoteDataValue, _walletNicknameString)
import WalletData.Types (WalletDetails, NewWalletDetails)
import WebSocket.Support as WS

mkMainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MonadContract m =>
  MonadWallet m =>
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
  , newWalletDetails: emptyNewWalletDetails
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
    (WS.ReceiveMessage (Right streamToClient)) -> Play.handleQuery streamToClient
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
  MonadContract m =>
  MonadWallet m =>
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

handleAction (SetNewWalletNicknameString walletNicknameString) = assign (_newWalletDetails <<< _walletNicknameString) walletNicknameString

handleAction (SetNewWalletContractIdString contractInstanceIdString) = do
  assign (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
  --TODO: use the contract ID to lookup the wallet's ID from PAB
  assign (_newWalletDetails <<< _remoteDataWallet) $ Success (Wallet { getWallet: fromInt 1 })

handleAction AddNewWallet = do
  oldWallets <- use _wallets
  newWalletDetails <- use _newWalletDetails
  newWalletNickname <- use (_newWalletDetails <<< _walletNicknameString)
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails ->
        when (not $ member newWalletNickname oldWallets) do
          modify_
            $ over _wallets (insert newWalletNickname walletDetails)
            <<< set _newWalletDetails emptyNewWalletDetails
            <<< set (_playState <<< _card) Nothing
          newWallets <- use _wallets
          liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON newWallets

-- pickup actions that need to be handled here
handleAction (PickupAction (Pickup.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNicknameString nickname

handleAction (PickupAction (Pickup.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractIdString contractId

handleAction (PickupAction Pickup.PickupNewWallet) = do
  newWalletDetails <- use _newWalletDetails
  for_ (mkNewWallet newWalletDetails)
    $ \walletDetails -> do
        handleAction AddNewWallet
        handleAction $ PickupAction $ Pickup.PickupWallet walletDetails

handleAction (PickupAction (Pickup.PickupWallet walletDetails)) = do
  -- we need the local timezoneOffset in play state in order to convert datetimeLocal
  -- values to UTC (and vice versa), so we can manage date-to-slot conversions
  timezoneOffset <- liftEffect getTimezoneOffset
  modify_
    $ set _subState (Right $ Play.mkInitialState walletDetails timezoneOffset)
    <<< set (_pickupState <<< _card) Nothing
  -- TODO: fetch current balance of the wallet from PAB
  -- TODO: open up websocket to this wallet's companion contract from PAB
  liftEffect $ setItem walletDetailsLocalStorageKey $ encodeJSON walletDetails

handleAction (PickupAction Pickup.GenerateNewWallet) = do
  remoteDataWallet <- createWallet
  assign (_newWalletDetails <<< _remoteDataWallet) remoteDataWallet
  case remoteDataWallet of
    Success wallet -> do
      remoteDataPubKey <- getWalletPubKey wallet
      remoteDataValue <- getWalletTotalFunds wallet
      assign (_newWalletDetails <<< _remoteDataPubKey) remoteDataPubKey
      assign (_newWalletDetails <<< _remoteDataValue) remoteDataValue
      -- TODO: create a wallet companion contract and get its instanceId
      let
        contractInstanceIdString = "9a72e336-2766-423e-a9c7-10c3b6c5ebb2"
      assign (_newWalletDetails <<< _contractInstanceIdString) contractInstanceIdString
      assign (_pickupState <<< _card) (Just Pickup.PickupNewWalletCard)
    -- TODO: show errors to the user
    _ -> pure unit

handleAction (PickupAction (Pickup.LookupWallet string)) = do
  wallets <- use _wallets
  -- check for a matching nickname in the wallet library first
  case lookup string wallets of
    Just walletDetails -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard walletDetails
    -- failing that, check for a matching ID in the wallet library
    Nothing -> case findMin $ filter (\walletDetails -> view (_contractInstanceId <<< _contractInstanceIdAsString) walletDetails == string) wallets of
      Just { key, value } -> assign (_pickupState <<< _card) $ Just $ Pickup.PickupWalletCard value
      -- TODO: and failing that, lookup the wallet contractId from PAB
      Nothing -> pure unit

-- other pickup actions
handleAction (PickupAction pickupAction) = Pickup.handleAction pickupAction

-- play actions that need to be handled here
handleAction (PlayAction Play.PutdownWallet) = do
  assign _subState $ Left Pickup.initialState
  liftEffect $ removeItem walletDetailsLocalStorageKey

handleAction (PlayAction (Play.SetNewWalletNickname nickname)) = handleAction $ SetNewWalletNicknameString nickname

handleAction (PlayAction (Play.SetNewWalletContractId contractId)) = handleAction $ SetNewWalletContractIdString contractId

handleAction (PlayAction (Play.AddNewWallet mTokenName)) = do
  walletNickname <- use (_newWalletDetails <<< _walletNicknameString)
  handleAction AddNewWallet
  for_ mTokenName \tokenName ->
    Template.handleAction $ Template.SetRoleWallet tokenName walletNickname

-- other play actions
handleAction (PlayAction playAction) = Play.handleAction playAction

------------------------------------------------------------
emptyNewWalletDetails :: NewWalletDetails
emptyNewWalletDetails =
  { walletNicknameString: mempty
  , contractInstanceIdString: mempty
  , remoteDataWallet: NotAsked
  , remoteDataPubKey: NotAsked
  , remoteDataValue: NotAsked
  }

mkNewWallet :: NewWalletDetails -> Maybe WalletDetails
mkNewWallet newWalletDetails =
  let
    walletNickname = view _walletNicknameString newWalletDetails

    contractInstanceIdString = view _contractInstanceIdString newWalletDetails

    mContractInstanceId = contractInstanceIdFromString contractInstanceIdString

    remoteDataWallet = view _remoteDataWallet newWalletDetails

    remoteDataPubKey = view _remoteDataPubKey newWalletDetails

    remoteDataValue = view _remoteDataValue newWalletDetails
  in
    case mContractInstanceId, remoteDataWallet, remoteDataPubKey, remoteDataValue of
      Just contractInstanceId, Success wallet, Success pubKey, Success value -> Just { walletNickname, contractInstanceId, wallet, pubKey, value }
      _, _, _, _ -> Nothing
