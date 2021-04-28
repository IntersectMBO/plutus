module Capability.Marlowe
  ( class ManageMarlowe
  , marloweCreateWallet
  , marloweFollowContract
  , marloweCreateContract
  , marloweApplyTransactionInput
  , marloweRedeem
  , marloweCloseContract
  , marloweLookupWalletInfo
  , marloweLookupWalletDetails
  , marloweGetRoleContracts
  , marloweGetContracts
  ) where

import Prelude
import API.Lenses (_cicContract, _cicCurrentState, _cicDefinition, _cicWallet, _observableState)
import Affjax (defaultRequest)
import AppM (AppM)
import Bridge (toBack, toFront)
import Capability.Contract (class ManageContract, activateContract, getContractInstanceClientState, getContractInstanceObservableState, getWalletContractInstances, invokeEndpoint)
import Capability.Wallet (class ManageWallet, createWallet, getWalletInfo, getWalletTotalFunds)
import Control.Monad.Except (ExceptT(..), except, lift, mapExceptT, runExcept, runExceptT, withExceptT)
import Data.Array (filter, find)
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Lens (set, view)
import Data.Map (Map, fromFoldable)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (emptyUUID)
import Foreign (MultipleErrors)
import Foreign.Generic (decodeJSON)
import Halogen (HalogenM)
import Marlowe.PAB (ContractInstanceId(..), ContractType(..), History, MarloweData, MarloweParams, contractExe, contractType)
import Marlowe.Semantics (Contract, TokenName, TransactionInput(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver.Types (ContractInstanceClientState)
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Lenses (_assets, _marloweContractId, _pubKeyHash, _wallet, _walletInfo)
import WalletData.Types (PubKeyHash, WalletDetails, WalletInfo)

-- The `ManageMarlowe` class provides a window on the `ManageContract` and `ManageWallet` capabilities
-- with functions specific to Marlowe.
-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  (ManageContract m, ManageWallet m) <= ManageMarlowe m where
  -- create a Wallet, a WalletCompanionWontract, a MarloweContract, and return the WalletDetails
  marloweCreateWallet :: m (AjaxResponse WalletDetails)
  -- create a WalletFollowerContract to follow a Marlowe contract on the blockchain
  marloweFollowContract :: WalletDetails -> MarloweParams -> m (DecodedAjaxResponse (Tuple ContractInstanceId History))
  -- "create" a Marlowe contract on the blockchain
  marloweCreateContract :: WalletDetails -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  -- "apply-inputs" to a Marlowe contract on the blockchain
  marloweApplyTransactionInput :: WalletDetails -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  -- "redeem" payments from a Marlowe contract on the blockchain
  marloweRedeem :: WalletDetails -> MarloweParams -> TokenName -> m (AjaxResponse Unit)
  -- "close" a Marlowe contract on the blockchain
  marloweCloseContract :: WalletDetails -> MarloweParams -> m (AjaxResponse Unit)
  -- get the WalletInfo of a wallet given the contractInstanceId of its WalletCompanionContract
  marloweLookupWalletInfo :: ContractInstanceId -> m (AjaxResponse WalletInfo)
  -- get the WalletDetails of a wallet given the contractInstanceId of its WalletCompanionContract
  -- note: this returns an empty walletNickname (because these are only saved locally) and an empty
  -- marloweContractId (because this would take a while to lookup - to get the marloweContractId we
  -- call `marloweGetContracts`)
  marloweLookupWalletDetails :: ContractInstanceId -> m (AjaxResponse WalletDetails)
  -- get the observable state of a wallet's WalletCompanionContract
  marloweGetRoleContracts :: WalletDetails -> m (DecodedAjaxResponse (Map MarloweParams MarloweData))
  -- get all contracts related to a wallet
  marloweGetContracts :: WalletDetails -> m (DecodedAjaxResponse (Tuple WalletDetails (Map ContractInstanceId History)))

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
        let
          createWalletDetails marloweContractId companionContractId assets =
            { walletNickname: ""
            , marloweContractId
            , companionContractId
            , walletInfo
            , assets
            }
        pure $ createWalletDetails <$> ajaxMarloweContractId <*> ajaxCompanionContractId <*> ajaxAssets
  marloweFollowContract walletDetails marloweParams = do
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      followContractId <- withExceptT Left $ ExceptT $ activateContract (contractExe WalletFollowerContract) wallet
      void $ withExceptT Left $ ExceptT $ invokeEndpoint followContractId "follow" marloweParams
      observableStateJson <- withExceptT Left $ ExceptT $ getContractInstanceObservableState followContractId
      observableState <- mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
      pure $ followContractId /\ observableState
  -- FIXME: if we want users to be able to follow contracts that they don't have roles in, we need
  -- this function to return the MarloweParams of the created contract - but this isn't currently
  -- possible in the PAB
  marloweCreateContract walletDetails roles contract =
    let
      contractInstanceId = view _marloweContractId walletDetails

      bRoles :: Back.Map Back.TokenName Back.PubKeyHash
      bRoles = toBack roles
    in
      invokeEndpoint contractInstanceId "create" (bRoles /\ contract)
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
  marloweCloseContract walletDetails marloweParams =
    let
      contractInstanceId = view _marloweContractId walletDetails
    in
      invokeEndpoint contractInstanceId "close" marloweParams
  marloweLookupWalletInfo companionContractId =
    runExceptT do
      clientState <- ExceptT $ getContractInstanceClientState companionContractId
      let
        contractExe = view _cicDefinition clientState
      case contractType contractExe of
        Just WalletCompanionContract -> do
          let
            wallet = toFront $ view _cicWallet clientState
          ExceptT $ getWalletInfo wallet
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  marloweLookupWalletDetails companionContractId =
    runExceptT do
      clientState <- ExceptT $ getContractInstanceClientState companionContractId
      let
        contractExe = view _cicDefinition clientState
      case contractType contractExe of
        Just WalletCompanionContract -> do
          let
            wallet = toFront $ view _cicWallet clientState
          walletInfo <- ExceptT $ getWalletInfo wallet
          assets <- ExceptT $ getWalletTotalFunds wallet
          ExceptT $ pure
            $ Right
                { walletNickname: ""
                , marloweContractId: ContractInstanceId emptyUUID
                , companionContractId
                , walletInfo
                , assets
                }
        _ -> except $ Left $ AjaxError { request: defaultRequest, description: NotFound }
  marloweGetRoleContracts walletDetails =
    runExceptT do
      let
        contractInstanceId = view _marloweContractId walletDetails
      observableStateJson <- withExceptT Left $ ExceptT $ getContractInstanceObservableState contractInstanceId
      mapExceptT (pure <<< lmap Right <<< unwrap) $ decodeJSON $ unwrap observableStateJson
  marloweGetContracts walletDetails =
    runExceptT do
      let
        wallet = view (_walletInfo <<< _wallet) walletDetails
      runningContracts <- withExceptT Left $ ExceptT $ getWalletContractInstances wallet
      assets <- withExceptT Left $ ExceptT $ getWalletTotalFunds wallet
      let
        mMarloweContract = find (\cic -> view _cicDefinition cic == contractExe MarloweContract) runningContracts

        followerContracts = filter (\cic -> view _cicDefinition cic == contractExe WalletFollowerContract) runningContracts
      case mMarloweContract of
        Nothing -> except $ Left $ Left $ AjaxError { request: defaultRequest, description: NotFound }
        Just marloweContract -> do
          let
            marloweContractId = view _marloweContractId walletDetails

            updatedWalletDetails = set _marloweContractId marloweContractId $ set _assets assets walletDetails
          case traverse decodeFollowerContract followerContracts of
            Left decodingError -> except $ Left $ Right decodingError
            Right decodedFollowerContracts -> ExceptT $ pure $ Right $ updatedWalletDetails /\ fromFoldable decodedFollowerContracts
    where
    decodeFollowerContract :: ContractInstanceClientState ContractExe -> Either MultipleErrors (Tuple ContractInstanceId History)
    decodeFollowerContract contractInstanceClientState =
      let
        contractInstanceId = toFront $ view _cicContract contractInstanceClientState

        rawJson = view (_cicCurrentState <<< _observableState) contractInstanceClientState
      in
        case runExcept $ decodeJSON $ unwrap rawJson of
          Left decodingErrors -> Left decodingErrors
          Right observableState -> Right (contractInstanceId /\ observableState)

instance monadMarloweHalogenM :: ManageMarlowe m => ManageMarlowe (HalogenM state action slots msg m) where
  marloweCreateWallet = lift marloweCreateWallet
  marloweFollowContract walletDetails marloweParams = lift $ marloweFollowContract walletDetails marloweParams
  marloweCreateContract walletDetails roles contract = lift $ marloweCreateContract walletDetails roles contract
  marloweApplyTransactionInput walletDetails marloweParams transactionInput = lift $ marloweApplyTransactionInput walletDetails marloweParams transactionInput
  marloweRedeem walletDetails marloweParams tokenName = lift $ marloweRedeem walletDetails marloweParams tokenName
  marloweCloseContract walletDetails marloweParams = lift $ marloweCloseContract walletDetails marloweParams
  marloweLookupWalletInfo = lift <<< marloweLookupWalletInfo
  marloweLookupWalletDetails = lift <<< marloweLookupWalletDetails
  marloweGetRoleContracts = lift <<< marloweGetRoleContracts
  marloweGetContracts = lift <<< marloweGetContracts
