module Capability.Marlowe
  ( class ManageMarlowe
  , marloweCreateWallet
  , marloweFollowContract
  , marloweCreateContract
  , marloweInvokeEndpoint
  , marloweApplyTransactionInput
  , marloweRedeem
  , marloweLookupWalletInfo
  , marloweLookupWalletDetails
  , marloweGetRoleContracts
  , marloweGetFollowerApps
  ) where

import Prelude
import API.Lenses (_cicContract, _cicCurrentState, _cicDefinition, _cicWallet, _observableState)
import Affjax (defaultRequest)
import AppM (AppM)
import Bridge (toBack, toFront)
import Capability.Contract (class ManageContract, activateContract, deactivateContract, getContractInstanceClientState, getContractInstanceObservableState, getWalletContractInstances, invokeEndpoint)
import Capability.Wallet (class ManageWallet, createWallet, getWalletInfo, getWalletTotalFunds)
import Control.Monad.Except (ExceptT(..), except, lift, mapExceptT, runExcept, runExceptT, withExceptT)
import Data.Array (filter)
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
import Foreign.Generic (class Encode, decodeJSON)
import Halogen (HalogenM)
import Marlowe.PAB (PlutusAppId, PlutusApp(..), History, MarloweData, MarloweParams, plutusAppPath, plutusAppType)
import Marlowe.Semantics (Contract, TokenName, TransactionInput(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver.Types (ContractInstanceClientState)
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_companionAppId, _pubKeyHash, _wallet, _walletInfo)
import WalletData.Types (PubKeyHash, WalletDetails, WalletInfo)

-- The `ManageMarlowe` class provides a window on the `ManageContract` and `ManageWallet` capabilities
-- with functions specific to Marlowe.
-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  (ManageContract m, ManageWallet m) <= ManageMarlowe m where
  marloweCreateWallet :: m (AjaxResponse WalletDetails)
  marloweFollowContract :: WalletDetails -> MarloweParams -> m (DecodedAjaxResponse (Tuple PlutusAppId History))
  marloweInvokeEndpoint :: forall d. Encode d => WalletDetails -> String -> d -> m (AjaxResponse Unit)
  marloweCreateContract :: WalletDetails -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  marloweApplyTransactionInput :: WalletDetails -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  marloweRedeem :: WalletDetails -> MarloweParams -> TokenName -> m (AjaxResponse Unit)
  marloweLookupWalletInfo :: PlutusAppId -> m (AjaxResponse WalletInfo)
  marloweLookupWalletDetails :: PlutusAppId -> m (AjaxResponse WalletDetails)
  marloweGetRoleContracts :: WalletDetails -> m (DecodedAjaxResponse (Map MarloweParams MarloweData))
  marloweGetFollowerApps :: WalletDetails -> m (DecodedAjaxResponse (Map PlutusAppId History))

instance monadMarloweAppM :: ManageMarlowe AppM where
  -- create a Wallet and a WalletCompanionApp, and return the WalletDetails
  marloweCreateWallet = do
    ajaxWalletInfo <- createWallet
    case ajaxWalletInfo of
      Left ajaxError -> pure $ Left ajaxError
      Right walletInfo -> do
        let
          wallet = view _wallet walletInfo
        ajaxCompanionAppId <- activateContract (plutusAppPath WalletCompanionApp) wallet
        ajaxAssets <- getWalletTotalFunds wallet
        let
          createWalletDetails companionAppId assets =
            { walletNickname: ""
            , companionAppId
            , walletInfo
            , assets
            }
        pure $ createWalletDetails <$> ajaxCompanionAppId <*> ajaxAssets
  -- create a WalletFollowerApp to follow a Marlowe contract on the blockchain
  marloweFollowContract walletDetails marloweParams = do
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      followAppId <- withExceptT Left $ ExceptT $ activateContract (plutusAppPath WalletFollowerApp) wallet
      void $ withExceptT Left $ ExceptT $ invokeEndpoint followAppId "follow" marloweParams
      observableStateJson <- withExceptT Left $ ExceptT $ getContractInstanceObservableState followAppId
      observableState <- mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
      pure $ followAppId /\ observableState
  -- create a MarloweApp, invoke one of its endpoints, and then immediately deactivate it
  -- Note: We have no need to keep MarloweApp instances around, so it is simpler to just activate one whenever
  -- we need to. Also this avoids the problem of having to check whether the endpoint is available - MarloweApps
  -- that have been used before may become unusable if there is any error.
  marloweInvokeEndpoint walletDetails endpoint payload =
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      contractInstanceId <- ExceptT $ activateContract (plutusAppPath MarloweApp) wallet
      result <- ExceptT $ invokeEndpoint contractInstanceId endpoint payload
      void $ ExceptT $ deactivateContract contractInstanceId
      pure result
  -- "create" a Marlowe contract on the blockchain
  -- FIXME: if we want users to be able to follow contracts that they don't have roles in, we need this function
  -- to return the MarloweParams of the created contract - but this isn't currently possible in the PAB
  -- UPDATE to this FIXME: it is possible this won't be a problem, as it seems role tokens are first paid into
  -- the wallet that created the contract, and distributed to other wallets from there - but this remains to be
  -- seen when all the parts are working together as they should be...
  marloweCreateContract walletDetails roles contract =
    let
      bRoles :: Back.Map Back.TokenName Back.PubKeyHash
      bRoles = toBack roles
    in
      marloweInvokeEndpoint walletDetails "create" (bRoles /\ contract)
  -- "apply-inputs" to a Marlowe contract on the blockchain
  marloweApplyTransactionInput walletDetails marloweParams (TransactionInput { interval, inputs }) = marloweInvokeEndpoint walletDetails "apply-inputs" (marloweParams /\ Just interval /\ inputs)
  -- "redeem" payments from a Marlowe contract on the blockchain
  marloweRedeem walletDetails marloweParams tokenName =
    let
      pubKeyHash = view (_walletInfo <<< _pubKeyHash) walletDetails
    in
      marloweInvokeEndpoint walletDetails "redeem" (marloweParams /\ tokenName /\ pubKeyHash)
  -- get the WalletInfo of a wallet given the PlutusAppId of its WalletCompanionApp
  marloweLookupWalletInfo companionContractId =
    runExceptT do
      clientState <- ExceptT $ getContractInstanceClientState companionContractId
      let
        appPath = view _cicDefinition clientState
      case plutusAppType appPath of
        Just WalletCompanionApp -> do
          let
            wallet = toFront $ view _cicWallet clientState
          ExceptT $ getWalletInfo wallet
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the WalletDetails of a wallet given the PlutusAppId of its WalletCompanionApp
  -- note: this returns an empty walletNickname (because these are only saved locally)
  marloweLookupWalletDetails companionAppId =
    runExceptT do
      clientState <- ExceptT $ getContractInstanceClientState companionAppId
      let
        appPath = view _cicDefinition clientState
      case plutusAppType appPath of
        Just WalletCompanionApp -> do
          let
            wallet = toFront $ view _cicWallet clientState
          walletInfo <- ExceptT $ getWalletInfo wallet
          assets <- ExceptT $ getWalletTotalFunds wallet
          ExceptT $ pure
            $ Right
                { walletNickname: ""
                , companionAppId
                , walletInfo
                , assets
                }
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  -- get the observable state of a wallet's WalletCompanionApp
  marloweGetRoleContracts walletDetails =
    runExceptT do
      let
        companionAppId = view _companionAppId walletDetails
      observableStateJson <- withExceptT Left $ ExceptT $ getContractInstanceObservableState companionAppId
      mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
  -- get all WalletFollowerApps for a given wallet
  marloweGetFollowerApps walletDetails =
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      runningApps <- withExceptT Left $ ExceptT $ getWalletContractInstances wallet
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

instance monadMarloweHalogenM :: ManageMarlowe m => ManageMarlowe (HalogenM state action slots msg m) where
  marloweCreateWallet = lift marloweCreateWallet
  marloweFollowContract walletDetails marloweParams = lift $ marloweFollowContract walletDetails marloweParams
  marloweCreateContract walletDetails roles contract = lift $ marloweCreateContract walletDetails roles contract
  marloweInvokeEndpoint walletDetails endpoint payload = lift $ marloweInvokeEndpoint walletDetails endpoint payload
  marloweApplyTransactionInput walletDetails marloweParams transactionInput = lift $ marloweApplyTransactionInput walletDetails marloweParams transactionInput
  marloweRedeem walletDetails marloweParams tokenName = lift $ marloweRedeem walletDetails marloweParams tokenName
  marloweLookupWalletInfo = lift <<< marloweLookupWalletInfo
  marloweLookupWalletDetails = lift <<< marloweLookupWalletDetails
  marloweGetRoleContracts = lift <<< marloweGetRoleContracts
  marloweGetFollowerApps = lift <<< marloweGetFollowerApps
