module Capability.Marlowe
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
import API.Lenses (_cicContract, _cicCurrentState, _cicDefinition, _cicWallet, _observableState)
import Affjax (defaultRequest)
import AppM (AppM)
import Bridge (toBack, toFront)
import Capability.Contract (class ManageContract)
import Capability.Contract (activateContract, getContractInstanceClientState, getContractInstanceObservableState, getWalletContractInstances, invokeEndpoint) as Contract
import Capability.Wallet (class ManageWallet)
import Capability.Wallet (createWallet, getWalletInfo, getWalletTotalFunds) as Wallet
import Capability.Websocket (class ManageWebsocket)
import Capability.Websocket (subscribeToContract, subscribeToWallet, unsubscribeFromContract, unsubscribeFromWallet) as Websocket
import Control.Monad.Except (ExceptT(..), except, lift, mapExceptT, runExcept, runExceptT, withExceptT)
import Data.Array (filter, find)
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Lens (view)
import Data.Map (Map, fromFoldable)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Foreign (MultipleErrors)
import Foreign.Generic (decodeJSON)
import Halogen (HalogenM)
import MainFrame.Types (Msg)
import Marlowe.PAB (PlutusAppId, PlutusApp(..), History, MarloweData, MarloweParams, plutusAppPath, plutusAppType)
import Marlowe.Semantics (Contract, TokenName, TransactionInput(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver.Types (ContractInstanceClientState)
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_companionAppId, _marloweAppId, _pubKeyHash, _wallet, _walletInfo)
import WalletData.Types (PubKeyHash, Wallet, WalletDetails, WalletInfo)

-- The `ManageMarlowe` class provides a window on the `ManageContract`, `ManageWallet`, and
-- `ManageWebsocket` capabilities with functions specific to Marlowe.
-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  (ManageContract m, ManageWallet m, ManageWebsocket m) <= ManageMarlowe m where
  createWallet :: m (AjaxResponse WalletDetails)
  followContract :: WalletDetails -> MarloweParams -> m (DecodedAjaxResponse (Tuple PlutusAppId History))
  createContract :: WalletDetails -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  applyTransactionInput :: WalletDetails -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  redeem :: WalletDetails -> MarloweParams -> TokenName -> m (AjaxResponse Unit)
  lookupWalletInfo :: PlutusAppId -> m (AjaxResponse WalletInfo)
  lookupWalletDetails :: PlutusAppId -> m (AjaxResponse WalletDetails)
  getRoleContracts :: WalletDetails -> m (DecodedAjaxResponse (Map MarloweParams MarloweData))
  getFollowerApps :: WalletDetails -> m (DecodedAjaxResponse (Map PlutusAppId History))
  subscribeToWallet :: Wallet -> m Unit
  unsubscribeFromWallet :: Wallet -> m Unit
  subscribeToPlutusApp :: PlutusAppId -> m Unit
  unsubscribeFromPlutusApp :: PlutusAppId -> m Unit

instance monadMarloweAppM :: ManageMarlowe AppM where
  -- create a Wallet, together with a WalletCompanionApp and a MarloweApp, and return the WalletDetails
  createWallet = do
    ajaxWalletInfo <- Wallet.createWallet
    case ajaxWalletInfo of
      Left ajaxError -> pure $ Left ajaxError
      Right walletInfo -> do
        let
          wallet = view _wallet walletInfo
        ajaxCompanionAppId <- Contract.activateContract (plutusAppPath WalletCompanionApp) wallet
        ajaxMarloweAppId <- Contract.activateContract (plutusAppPath MarloweApp) wallet
        ajaxAssets <- Wallet.getWalletTotalFunds wallet
        let
          createWalletDetails companionAppId marloweAppId assets =
            { walletNickname: ""
            , companionAppId
            , marloweAppId
            , walletInfo
            , assets
            }
        pure $ createWalletDetails <$> ajaxCompanionAppId <*> ajaxMarloweAppId <*> ajaxAssets
  -- create a WalletFollowerApp to follow a Marlowe contract on the blockchain, and return its instance ID and initial state
  followContract walletDetails marloweParams = do
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      followAppId <- withExceptT Left $ ExceptT $ Contract.activateContract (plutusAppPath WalletFollowerApp) wallet
      void $ withExceptT Left $ ExceptT $ Contract.invokeEndpoint followAppId "follow" marloweParams
      observableStateJson <- withExceptT Left $ ExceptT $ Contract.getContractInstanceObservableState followAppId
      observableState <- mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
      pure $ followAppId /\ observableState
  -- "create" a Marlowe contract on the blockchain
  -- FIXME: if we want users to be able to follow contracts that they don't have roles in, we need this function
  -- to return the MarloweParams of the created contract - but this isn't currently possible in the PAB
  -- UPDATE to this FIXME: it is possible this won't be a problem, as it seems role tokens are first paid into
  -- the wallet that created the contract, and distributed to other wallets from there - but this remains to be
  -- seen when all the parts are working together as they should be...
  createContract walletDetails roles contract =
    let
      marloweAppId = view _marloweAppId walletDetails

      bRoles :: Back.Map Back.TokenName Back.PubKeyHash
      bRoles = toBack roles
    in
      Contract.invokeEndpoint marloweAppId "create" (bRoles /\ contract)
  -- "apply-inputs" to a Marlowe contract on the blockchain
  applyTransactionInput walletDetails marloweParams (TransactionInput { interval, inputs }) =
    let
      marloweAppId = view _marloweAppId walletDetails
    in
      Contract.invokeEndpoint marloweAppId "apply-inputs" (marloweParams /\ Just interval /\ inputs)
  -- "redeem" payments from a Marlowe contract on the blockchain
  redeem walletDetails marloweParams tokenName =
    let
      marloweAppId = view _marloweAppId walletDetails

      pubKeyHash = view (_walletInfo <<< _pubKeyHash) walletDetails
    in
      Contract.invokeEndpoint marloweAppId "redeem" (marloweParams /\ tokenName /\ pubKeyHash)
  -- get the WalletInfo of a wallet given the PlutusAppId of its WalletCompanionApp
  lookupWalletInfo companionAppId =
    runExceptT do
      clientState <- ExceptT $ Contract.getContractInstanceClientState companionAppId
      let
        appPath = view _cicDefinition clientState
      case plutusAppType appPath of
        Just WalletCompanionApp -> do
          let
            wallet = toFront $ view _cicWallet clientState
          ExceptT $ Wallet.getWalletInfo wallet
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the WalletDetails of a wallet given the PlutusAppId of its WalletCompanionApp
  -- note: this returns an empty walletNickname (because these are only saved locally)
  lookupWalletDetails companionAppId =
    runExceptT do
      clientState <- ExceptT $ Contract.getContractInstanceClientState companionAppId
      let
        appPath = view _cicDefinition clientState
      case plutusAppType appPath of
        Just WalletCompanionApp -> do
          let
            wallet = toFront $ view _cicWallet clientState
          walletContracts <- ExceptT $ Contract.getWalletContractInstances wallet
          walletInfo <- ExceptT $ Wallet.getWalletInfo wallet
          assets <- ExceptT $ Wallet.getWalletTotalFunds wallet
          case find (\state -> plutusAppType (view _cicDefinition state) == Just MarloweApp) walletContracts of
            Just marloweApp ->
              ExceptT $ pure
                $ Right
                    { walletNickname: mempty
                    , companionAppId
                    , marloweAppId: toFront $ view _cicContract marloweApp
                    , walletInfo
                    , assets
                    }
            Nothing -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the observable state of a wallet's WalletCompanionApp
  getRoleContracts walletDetails =
    runExceptT do
      let
        companionAppId = view _companionAppId walletDetails
      observableStateJson <- withExceptT Left $ ExceptT $ Contract.getContractInstanceObservableState companionAppId
      mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
  -- get all WalletFollowerApps for a given wallet
  getFollowerApps walletDetails =
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      runningApps <- withExceptT Left $ ExceptT $ Contract.getWalletContractInstances wallet
      let
        followerApps = filter (\cic -> view _cicDefinition cic == plutusAppPath WalletFollowerApp) runningApps
      case traverse decodeFollowerAppState followerApps of
        Left decodingError -> except $ Left $ Right decodingError
        Right decodedFollowerApps -> ExceptT $ pure $ Right $ fromFoldable decodedFollowerApps
    where
    decodeFollowerAppState :: ContractInstanceClientState ContractExe -> Either MultipleErrors (Tuple PlutusAppId History)
    decodeFollowerAppState contractInstanceClientState =
      let
        plutusAppId = toFront $ view _cicContract contractInstanceClientState

        rawJson = view (_cicCurrentState <<< _observableState) contractInstanceClientState
      in
        case runExcept $ decodeJSON $ unwrap rawJson of
          Left decodingErrors -> Left decodingErrors
          Right observableState -> Right (plutusAppId /\ observableState)
  subscribeToPlutusApp = Websocket.subscribeToContract <<< toBack
  subscribeToWallet = Websocket.subscribeToWallet <<< toBack
  unsubscribeFromPlutusApp = Websocket.unsubscribeFromContract <<< toBack
  unsubscribeFromWallet = Websocket.unsubscribeFromWallet <<< toBack

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
  subscribeToPlutusApp = Websocket.subscribeToContract <<< toBack
  subscribeToWallet = Websocket.subscribeToWallet <<< toBack
  unsubscribeFromPlutusApp = Websocket.unsubscribeFromContract <<< toBack
  unsubscribeFromWallet = Websocket.unsubscribeFromWallet <<< toBack
