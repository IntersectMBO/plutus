module Capability.Marlowe.Dummy
  ( class ManageMarlowe
  , createWallet
  , followContract
  , createContract
  , applyTransactionInput
  , redeem
  , lookupWalletInfo
  , lookupWalletDetails
  , getRoleContracts
  , getFollowerApps
  , subscribeToWallet
  , unsubscribeFromWallet
  , subscribeToPlutusApp
  , unsubscribeFromPlutusApp
  ) where

import Prelude
import Affjax (defaultRequest)
import AppM (AppM)
import Capability.Contract (class ManageContract)
import Capability.Contract (activateContract, getContractInstanceObservableState, invokeEndpoint) as Contract
import Capability.Wallet (class ManageWallet)
import Capability.Websocket (class ManageWebsocket)
import Control.Monad.Except (ExceptT(..), lift, mapExceptT, runExcept, runExceptT, withExceptT)
import Data.Bifunctor (lmap)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Int (floor)
import Data.Lens (view)
import Data.Map (Map, filter, findMin, singleton)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (genUUID)
import Effect.Class (liftEffect)
import Effect.Random (random)
import Foreign.Generic (decodeJSON)
import Halogen (HalogenM)
import LocalStorage (getItem)
import MainFrame.Types (Msg)
import Marlowe.PAB (ContractHistory(..), PlutusAppId(..), PlutusApp(..), MarloweData, MarloweParams, plutusAppPath)
import Marlowe.Semantics (Assets(..), Contract, TokenName, TransactionInput(..))
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import StaticData (walletLibraryLocalStorageKey)
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_companionAppId, _wallet, _walletInfo)
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails, WalletInfo(..), WalletLibrary)

-- Until everything in the PAB is working as it should be, we can use this "dummy" version of the
-- Marlowe capability. It is simpler and cleaner to do this once and for all here, than to track
-- down each place where these functions are used and write some dummy code there.
class
  (ManageContract m, ManageWallet m, ManageWebsocket m) <= ManageMarlowe m where
  createWallet :: m (AjaxResponse WalletDetails)
  followContract :: WalletDetails -> MarloweParams -> m (DecodedAjaxResponse (Tuple PlutusAppId ContractHistory))
  createContract :: WalletDetails -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  applyTransactionInput :: WalletDetails -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  redeem :: WalletDetails -> MarloweParams -> TokenName -> m (AjaxResponse Unit)
  lookupWalletInfo :: PlutusAppId -> m (AjaxResponse WalletInfo)
  lookupWalletDetails :: PlutusAppId -> m (AjaxResponse WalletDetails)
  getRoleContracts :: WalletDetails -> m (DecodedAjaxResponse (Map MarloweParams MarloweData))
  getFollowerApps :: WalletDetails -> m (DecodedAjaxResponse (Map PlutusAppId ContractHistory))
  subscribeToPlutusApp :: PlutusAppId -> m Unit
  subscribeToWallet :: Wallet -> m Unit
  unsubscribeFromPlutusApp :: PlutusAppId -> m Unit
  unsubscribeFromWallet :: Wallet -> m Unit

instance monadMarloweAppM :: ManageMarlowe AppM where
  -- create a Wallet, together with a WalletCompanionApp and a MarloweApp, and return the WalletDetails
  createWallet = do
    uuid1 <- liftEffect genUUID
    uuid2 <- liftEffect genUUID
    number <- liftEffect random
    let
      integer = floor $ number * 1000000000000000000.0

      walletInfo =
        WalletInfo
          { wallet: Wallet $ fromInt integer
          , pubKey: mempty -- we don't need this for anything
          , pubKeyHash: PubKeyHash $ show integer
          }

      assets = Assets $ singleton "" $ singleton "" (fromInt 1000000 * fromInt 10000)

      walletDetails =
        { walletNickname: ""
        , companionAppId: PlutusAppId uuid1
        , marloweAppId: PlutusAppId uuid2
        , walletInfo
        , assets
        }
    pure $ Right walletDetails
  -- create a WalletFollowerApp to follow a Marlowe contract on the blockchain, and return its instance ID and initial state
  followContract walletDetails marloweParams = do
    uuid <- liftEffect genUUID
    let
      followAppId = PlutusAppId uuid

      observableState = None
    pure $ Right $ followAppId /\ observableState
  -- "create" a Marlowe contract on the blockchain
  createContract walletDetails roles contract = pure $ Right unit
  -- "apply-inputs" to a Marlowe contract on the blockchain
  applyTransactionInput walletDetails marloweParams (TransactionInput { interval, inputs }) = pure $ Right unit
  -- "redeem" payments from a Marlowe contract on the blockchain
  redeem walletDetails marloweParams tokenName = pure $ Right unit
  -- get the WalletInfo of a wallet given the PlutusAppId of its WalletCompanionApp
  lookupWalletInfo companionAppId =
    runExceptT do
      walletDetails <- ExceptT $ lookupWalletDetails companionAppId
      pure $ view _walletInfo walletDetails
  -- get the WalletDetails of a wallet given the PlutusAppId of its WalletCompanionApp
  -- note: this returns an empty walletNickname (because these are only saved locally)
  lookupWalletDetails companionAppId = do
    mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
    let
      walletLibrary :: WalletLibrary
      walletLibrary = case mWalletLibraryJson of
        Just json -> case runExcept $ decodeJSON json of
          Right wallets -> wallets
          Left _ -> mempty
        Nothing -> mempty

      mWalletDetails = findMin $ filter (\details -> view _companionAppId details == companionAppId) walletLibrary
    case mWalletDetails of
      Just { key, value } -> pure $ Right value
      Nothing -> pure $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the observable state of a wallet's WalletCompanionApp
  getRoleContracts walletDetails = pure $ Right $ mempty
  -- get all WalletFollowerApps for a given wallet
  getFollowerApps walletDetails = pure $ Right $ mempty
  subscribeToPlutusApp plutusAppId = pure unit
  subscribeToWallet wallet = pure unit
  unsubscribeFromPlutusApp plutusAppId = pure unit
  unsubscribeFromWallet wallet = pure unit

instance monadMarloweHalogenM :: (ManageMarlowe m, ManageWebsocket m) => ManageMarlowe (HalogenM state action slots Msg m) where
  createWallet = lift createWallet
  followContract walletDetails marloweParams = lift $ followContract walletDetails marloweParams
  createContract walletDetails roles contract = lift $ createContract walletDetails roles contract
  applyTransactionInput walletDetails marloweParams transactionInput = lift $ applyTransactionInput walletDetails marloweParams transactionInput
  redeem walletDetails marloweParams tokenName = lift $ redeem walletDetails marloweParams tokenName
  lookupWalletInfo = lift <<< lookupWalletInfo
  lookupWalletDetails = lift <<< lookupWalletDetails
  getRoleContracts = lift <<< getRoleContracts
  getFollowerApps = lift <<< getFollowerApps
  subscribeToPlutusApp plutusAppId = pure unit
  subscribeToWallet wallet = pure unit
  unsubscribeFromPlutusApp plutusAppId = pure unit
  unsubscribeFromWallet wallet = pure unit
