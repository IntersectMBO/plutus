module Capability.Marlowe
  ( class ManageMarloweContract
  , marloweCreateWalletCompanionContract
  , marloweGetWalletCompanionContractObservableState
  , marloweCreateContract
  , marloweApplyInputs
  , marloweWait
  , marloweAuto
  , marloweRedeem
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (class ManageContract, activateContract, getContractInstanceObservableState, invokeEndpoint)
import Capability.ContractExe (marloweContractExe, walletCompanionContractExe)
import Contract.Types (MarloweParams, MarloweData)
import Control.Monad.Except (lift, runExcept)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Newtype (unwrap)
import Data.RawJson (RawJson(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Foreign.Generic (decodeJSON, encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM)
import Marlowe.Semantics (Contract, Input, Party, Slot, TokenName)
import Network.RemoteData (RemoteData(..))
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Types (DecodedWebData, ContractInstanceId, WebData)
import WalletData.Types (PubKeyHash, Wallet)

-- The `ManageMarloweContract` class provides a window on the `ManageContract` class with function
-- calls specific to the Marlowe Plutus contract.
class
  ManageContract m <= ManageMarloweContract m where
  marloweCreateWalletCompanionContract :: Wallet -> m (WebData ContractInstanceId)
  marloweGetWalletCompanionContractObservableState :: ContractInstanceId -> m (DecodedWebData (Array (Tuple MarloweParams MarloweData)))
  marloweCreateContract :: Wallet -> Map TokenName PubKeyHash -> Contract -> m (WebData ContractInstanceId)
  marloweApplyInputs :: ContractInstanceId -> MarloweParams -> Array Input -> m (WebData Unit)
  marloweWait :: ContractInstanceId -> MarloweParams -> m (WebData Unit)
  marloweAuto :: ContractInstanceId -> MarloweParams -> Party -> Slot -> m (WebData Unit)
  marloweRedeem :: ContractInstanceId -> MarloweParams -> TokenName -> PubKeyHash -> m (WebData Unit)

instance monadMarloweAppM :: ManageMarloweContract AppM where
  marloweCreateWalletCompanionContract wallet = activateContract $ ContractActivationArgs { caID: walletCompanionContractExe, caWallet: toBack wallet }
  marloweGetWalletCompanionContractObservableState contractInstanceId = do
    remoteDataObservableState <- getContractInstanceObservableState contractInstanceId
    case remoteDataObservableState of
      Success rawJson -> case runExcept $ decodeJSON $ unwrap rawJson of
        Left decodingError -> pure $ Failure $ Right decodingError
        Right observableState -> pure $ Success observableState
      Failure ajaxError -> pure $ Failure $ Left ajaxError
      NotAsked -> pure NotAsked
      Loading -> pure Loading
  marloweCreateContract wallet roles contract = do
    webContractInstanceId <- activateContract $ ContractActivationArgs { caID: marloweContractExe, caWallet: toBack wallet }
    case webContractInstanceId of
      Success contractInstanceId -> do
        let
          bRoles :: Back.Map Back.TokenName Back.PubKeyHash
          bRoles = toBack roles

          rawJson = RawJson <<< unsafeStringify <<< encode $ (bRoles /\ contract)
        _ <- invokeEndpoint rawJson contractInstanceId "create"
        pure webContractInstanceId
      _ -> pure webContractInstanceId
  marloweApplyInputs contractInstanceId params inputs =
    let
      rawJson = RawJson <<< unsafeStringify <<< encode $ (params /\ inputs)
    in
      invokeEndpoint rawJson contractInstanceId "apply-inputs"
  marloweWait contractInstanceId params =
    let
      rawJson = RawJson <<< unsafeStringify <<< encode $ params
    in
      invokeEndpoint rawJson contractInstanceId "wait"
  marloweAuto contractInstanceId params party slot =
    let
      rawJson = RawJson <<< unsafeStringify <<< encode $ (params /\ party /\ slot)
    in
      invokeEndpoint rawJson contractInstanceId "auto"
  marloweRedeem contractInstanceId params tokenName pubKey =
    let
      rawJson = RawJson <<< unsafeStringify <<< encode $ (params /\ tokenName /\ pubKey)
    in
      invokeEndpoint rawJson contractInstanceId "redeem"

instance monadMarloweHalogenM :: ManageMarloweContract m => ManageMarloweContract (HalogenM state action slots msg m) where
  marloweCreateWalletCompanionContract = lift <<< marloweCreateWalletCompanionContract
  marloweGetWalletCompanionContractObservableState = lift <<< marloweGetWalletCompanionContractObservableState
  marloweCreateContract wallet roles contract = lift $ marloweCreateContract wallet roles contract
  marloweApplyInputs contractInstanceId params inputs = lift $ marloweApplyInputs contractInstanceId params inputs
  marloweWait contractInstanceId params = lift $ marloweWait contractInstanceId params
  marloweAuto contractInstanceId params party slot = lift $ marloweAuto contractInstanceId params party slot
  marloweRedeem contractInstanceId params tokenName pubKeyHash = lift $ marloweRedeem contractInstanceId params tokenName pubKeyHash
