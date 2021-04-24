module Capability.Marlowe
  ( class ManageMarlowe
  , marloweCreateWallet
  , marloweCreateContract
  , marloweFollowContract
  , marloweCloseContract
  , marloweApplyTransactionInput
  , marloweRedeem
  , marloweGetRoleContracts
  , marloweLookupWalletInfo
  , marloweLookupWallet
  , marloweGetFollowerContracts
  ) where

import Prelude
import Affjax (defaultRequest)
import API.Lenses (_cicDefinition, _cicWallet)
import AppM (AppM)
import Bridge (toBack, toFront)
import Capability.Contract (class ManageContract, activateContract, getContractInstanceClientState, getContractInstanceObservableState, invokeEndpoint)
import Capability.Wallet (class ManageWallet, createWallet, getWalletInfo, getWalletTotalFunds)
import Control.Monad.Except (lift, runExcept)
import Data.Either (Either(..))
import Data.Lens (view)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (emptyUUID)
import Foreign.Generic (decodeJSON)
import Halogen (HalogenM)
import Marlowe.PAB (ContractInstanceId(..), ContractType(..), History, MarloweData, MarloweParams, contractExe, contractType)
import Marlowe.Semantics (Contract, TokenName, TransactionInput(..))
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_marloweContractId, _pubKeyHash, _wallet, _walletInfo)
import WalletData.Types (PubKeyHash, WalletDetails, WalletInfo)

-- The `ManageMarlowe` class provides a window on the `ManageContract` and `ManageWallet` capabilities
-- with functions specific to Marlowe.
class
  (ManageContract m, ManageWallet m) <= ManageMarlowe m where
  marloweCreateWallet :: m (AjaxResponse WalletDetails)
  marloweCreateContract :: WalletDetails -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  marloweFollowContract :: WalletDetails -> MarloweParams -> m (DecodedAjaxResponse (Tuple ContractInstanceId History))
  marloweApplyTransactionInput :: WalletDetails -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  marloweCloseContract :: WalletDetails -> MarloweParams -> m (AjaxResponse Unit)
  marloweRedeem :: WalletDetails -> MarloweParams -> TokenName -> m (AjaxResponse Unit)
  marloweLookupWalletInfo :: ContractInstanceId -> m (AjaxResponse WalletInfo)
  marloweLookupWallet :: ContractInstanceId -> m (AjaxResponse WalletDetails)
  marloweGetRoleContracts :: WalletDetails -> m (DecodedAjaxResponse (Array (Tuple MarloweParams MarloweData)))
  marloweGetFollowerContracts :: WalletDetails -> m (DecodedAjaxResponse (Array (Tuple ContractInstanceId History)))

instance monadMarloweAppM :: ManageMarlowe AppM where
  marloweCreateWallet = do
    ajaxWalletInfo <- createWallet
    case ajaxWalletInfo of
      Left ajaxError -> pure $ Left ajaxError
      Right walletInfo -> do
        let
          wallet = view _wallet walletInfo
        ajaxMarloweContractId <- activateContract (contractExe MarloweContract) wallet
        ajaxCompanionContractId <- activateContract (contractExe WalletCompanionContract) wallet
        ajaxAssets <- getWalletTotalFunds wallet
        case ajaxMarloweContractId, ajaxCompanionContractId, ajaxAssets of
          Left ajaxError, _, _ -> pure $ Left ajaxError
          _, Left ajaxError, _ -> pure $ Left ajaxError
          _, _, Left ajaxError -> pure $ Left ajaxError
          Right marloweContractId, Right companionContractId, Right assets ->
            pure
              $ Right
                  { walletNickname: ""
                  , marloweContractId: marloweContractId
                  , companionContractId: companionContractId
                  , walletInfo: walletInfo
                  , assets
                  }
  marloweCreateContract walletDetails roles contract =
    let
      contractInstanceId = view _marloweContractId walletDetails

      bRoles :: Back.Map Back.TokenName Back.PubKeyHash
      bRoles = toBack roles
    in
      invokeEndpoint contractInstanceId "create" (bRoles /\ contract)
  marloweFollowContract walletDetails marloweParams = do
    let
      wallet = view (_walletInfo <<< _wallet) walletDetails
    ajaxFollowContractId <- activateContract (contractExe WalletFollowerContract) wallet
    case ajaxFollowContractId of
      Left ajaxError -> pure $ Left $ Left ajaxError
      Right followContractId -> do
        _ <- invokeEndpoint followContractId "follow" marloweParams
        ajaxObservableState <- getContractInstanceObservableState followContractId
        case ajaxObservableState of
          Left ajaxError -> pure $ Left $ Left ajaxError
          Right rawJson -> case runExcept $ decodeJSON $ unwrap rawJson of
            Left decodingError -> pure $ Left $ Right decodingError
            Right observableState -> pure $ Right $ followContractId /\ observableState
  marloweCloseContract walletDetails marloweParams =
    let
      contractInstanceId = view _marloweContractId walletDetails
    in
      invokeEndpoint contractInstanceId "close" marloweParams
  marloweApplyTransactionInput walletDetails marloweParams (TransactionInput { interval, inputs }) =
    let
      contractInstanceId = view _marloweContractId walletDetails
    in
      invokeEndpoint contractInstanceId "apply-inputs" (marloweParams /\ Just interval /\ inputs)
  marloweRedeem walletDetails marloweParams tokenName =
    let
      contractInstanceId = view _marloweContractId walletDetails

      pubKeyHash = view (_walletInfo <<< _pubKeyHash) walletDetails
    in
      invokeEndpoint contractInstanceId "redeem" (marloweParams /\ tokenName /\ pubKeyHash)
  marloweGetRoleContracts walletDetails = do
    let
      contractInstanceId = view _marloweContractId walletDetails
    ajaxObservableState <- getContractInstanceObservableState contractInstanceId
    case ajaxObservableState of
      Left ajaxError -> pure $ Left $ Left ajaxError
      Right rawJson -> case runExcept $ decodeJSON $ unwrap rawJson of
        Left decodingError -> pure $ Left $ Right decodingError
        Right observableState -> pure $ Right observableState
  marloweLookupWalletInfo companionContractId = do
    ajaxClientState <- getContractInstanceClientState companionContractId
    case ajaxClientState of
      Left ajaxError -> pure $ Left ajaxError
      Right clientState -> do
        let
          contractExe = view _cicDefinition clientState
        case contractType contractExe of
          Just WalletCompanionContract -> do
            let
              wallet = toFront $ view _cicWallet clientState
            getWalletInfo wallet
          _ -> pure $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  marloweLookupWallet companionContractId = do
    ajaxClientState <- getContractInstanceClientState companionContractId
    case ajaxClientState of
      Left ajaxError -> pure $ Left ajaxError
      Right clientState -> do
        let
          contractExe = view _cicDefinition clientState
        case contractType contractExe of
          Just WalletCompanionContract -> do
            let
              wallet = toFront $ view _cicWallet clientState
            ajaxWalletInfo <- getWalletInfo wallet
            ajaxAssets <- getWalletTotalFunds wallet
            case ajaxWalletInfo, ajaxAssets of
              Left ajaxError, _ -> pure $ Left ajaxError
              _, Left ajaxError -> pure $ Left ajaxError
              Right walletInfo, Right assets ->
                pure
                  $ Right
                      { walletNickname: ""
                      , marloweContractId: ContractInstanceId emptyUUID
                      , companionContractId
                      , walletInfo
                      , assets
                      }
          _ -> pure $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  marloweGetFollowerContracts walletDetails = do
    

instance monadMarloweHalogenM :: ManageMarlowe m => ManageMarlowe (HalogenM state action slots msg m) where
  marloweCreateWallet = lift marloweCreateWallet
  marloweCreateContract walletDetails roles contract = lift $ marloweCreateContract walletDetails roles contract
  marloweFollowContract walletDetails marloweParams = lift $ marloweFollowContract walletDetails marloweParams
  marloweCloseContract walletDetails marloweParams = lift $ marloweCloseContract walletDetails marloweParams
  marloweApplyTransactionInput walletDetails marloweParams transactionInput = lift $ marloweApplyTransactionInput walletDetails marloweParams transactionInput
  marloweRedeem walletDetails marloweParams tokenName = lift $ marloweRedeem walletDetails marloweParams tokenName
  marloweGetRoleContracts = lift <<< marloweGetRoleContracts
  marloweLookupWalletInfo = lift <<< marloweLookupWalletInfo
  marloweLookupWallet = lift <<< marloweLookupWallet
  marloweGetFollowerContracts = lift <<< marloweGetFollowerContracts
