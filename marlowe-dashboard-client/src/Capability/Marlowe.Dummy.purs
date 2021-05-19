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
import Capability.LocalStorage (class ManageLocalStorage, addAssets, getContracts, getWalletLibrary, getWalletRoleContracts, insertContract, insertWalletRoleContracts)
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Wallet (class ManageWallet)
import Capability.Websocket (class ManageWebsocket)
import Control.Monad.Except (ExceptT(..), lift, runExceptT)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Int (floor)
import Data.Lens (view)
import Data.Map (Map, filter, findMin, fromFoldable, lookup, mapMaybeWithKey, singleton, toUnfoldable, values)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Traversable (for)
import Data.Tuple (Tuple, snd)
import Data.Tuple.Nested ((/\))
import Data.UUID (genUUID, parseUUID, toString)
import Effect.Class (liftEffect)
import Effect.Random (random)
import Halogen (HalogenM)
import MainFrame.Types (Action(..), Msg)
import Marlowe.PAB (ContractHistory(..), PlutusAppId(..), MarloweData, MarloweParams)
import Marlowe.Semantics (Assets(..), Contract, TransactionInput, TokenName, asset, emptyState)
import Play.Types (Action(..)) as Play
import Plutus.V1.Ledger.Value (CurrencySymbol(..))
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_companionAppId, _pubKey, _walletInfo)
import WalletData.Types (PubKeyHash(..), Wallet(..), WalletDetails, WalletInfo(..))

-- Until everything in the PAB is working as it should be, we can use this "dummy" version of the
-- Marlowe capability. It is simpler and cleaner to do this once and for all here, than to track
-- down each place where these functions are used and write some dummy code there.
class
  (MainFrameLoop m, ManageContract m, ManageWallet m, ManageWebsocket m, ManageLocalStorage m) <= ManageMarlowe m where
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
    uuid <- liftEffect genUUID
    number <- liftEffect random
    let
      integer = floor $ number * 1000000000000000000.0

      walletInfo =
        WalletInfo
          { wallet: Wallet $ fromInt integer
          , pubKey: toString uuid
          , pubKeyHash: PubKeyHash $ toString uuid
          }

      assets = Assets $ singleton "" $ singleton "" (fromInt 1000000 * fromInt 10000)

      walletDetails =
        { walletNickname: ""
        , companionAppId: PlutusAppId uuid
        , marloweAppId: PlutusAppId uuid
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
  createContract walletDetails roles contract = do
    walletLibrary <- getWalletLibrary
    uuid <- liftEffect genUUID
    let
      marloweParams =
        { rolePayoutValidatorHash: toString uuid
        , rolesCurrency: CurrencySymbol { unCurrencySymbol: toString uuid }
        }

      marloweData =
        { marloweContract: contract
        , marloweState: emptyState zero
        }
    void $ insertContract marloweParams (marloweData /\ mempty)
    void $ insertWalletRoleContracts (view (_walletInfo <<< _pubKey) walletDetails) marloweParams marloweData
    let
      unfoldableRoles :: Array (Tuple TokenName PubKeyHash)
      unfoldableRoles = toUnfoldable roles
    void
      $ for unfoldableRoles \(tokenName /\ pubKeyHash) -> do
          void $ addAssets pubKeyHash $ asset (toString uuid) tokenName (fromInt 1)
          void $ insertWalletRoleContracts (unwrap pubKeyHash) marloweParams marloweData
    pure $ Right unit
  -- "apply-inputs" to a Marlowe contract on the blockchain
  applyTransactionInput walletDetails marloweParams transactionInput = do
    existingContracts <- getContracts
    case lookup marloweParams existingContracts of
      Just (marloweData /\ transactionInputs) -> do
        void $ insertContract marloweParams (marloweData /\ (transactionInputs <> [ transactionInput ]))
        pure $ Right unit
      Nothing -> pure $ Left $ AjaxError { request: defaultRequest, description: NotFound }
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
    walletLibrary <- getWalletLibrary
    let
      mWalletDetails = findMin $ filter (\walletDetails -> view _companionAppId walletDetails == companionAppId) walletLibrary
    case mWalletDetails of
      Just { key, value } -> pure $ Right value
      Nothing -> pure $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the observable state of a wallet's WalletCompanionApp
  getRoleContracts walletDetails = do
    roleContracts <- getWalletRoleContracts $ view (_walletInfo <<< _pubKey) walletDetails
    pure $ Right roleContracts
  -- get all WalletFollowerApps for a given wallet
  getFollowerApps walletDetails = do
    roleContracts <- getWalletRoleContracts $ view (_walletInfo <<< _pubKey) walletDetails
    allContracts <- getContracts
    let
      roleContractsToHistory :: MarloweParams -> MarloweData -> Maybe (Tuple PlutusAppId ContractHistory)
      roleContractsToHistory marloweParams marloweData =
        let
          mUuid = parseUUID marloweParams.rolePayoutValidatorHash

          mTransactionInputs = map snd $ lookup marloweParams allContracts
        in
          case mUuid, mTransactionInputs of
            Just uuid, Just transactionInputs -> Just $ PlutusAppId uuid /\ History marloweParams marloweData transactionInputs
            _, _ -> Nothing
    pure $ Right $ fromFoldable $ values $ mapMaybeWithKey roleContractsToHistory roleContracts
  subscribeToPlutusApp plutusAppId = pure unit
  subscribeToWallet wallet = pure unit
  unsubscribeFromPlutusApp plutusAppId = pure unit
  unsubscribeFromWallet wallet = pure unit

instance monadMarloweHalogenM :: ManageMarlowe m => ManageMarlowe (HalogenM state action slots Msg m) where
  createWallet = lift createWallet
  followContract walletDetails marloweParams = lift $ followContract walletDetails marloweParams
  createContract walletDetails roles contract = do
    result <- lift $ createContract walletDetails roles contract
    callMainFrameAction $ PlayAction $ Play.UpdateFromStorage
    pure result
  applyTransactionInput walletDetails marloweParams transactionInput = do
    result <- lift $ applyTransactionInput walletDetails marloweParams transactionInput
    callMainFrameAction $ PlayAction $ Play.UpdateFromStorage
    pure result
  redeem walletDetails marloweParams tokenName = do
    result <- lift $ redeem walletDetails marloweParams tokenName
    callMainFrameAction $ PlayAction $ Play.UpdateFromStorage
    pure result
  lookupWalletInfo = lift <<< lookupWalletInfo
  lookupWalletDetails = lift <<< lookupWalletDetails
  getRoleContracts = lift <<< getRoleContracts
  getFollowerApps = lift <<< getFollowerApps
  subscribeToPlutusApp plutusAppId = pure unit
  subscribeToWallet wallet = pure unit
  unsubscribeFromPlutusApp plutusAppId = pure unit
  unsubscribeFromWallet wallet = pure unit
