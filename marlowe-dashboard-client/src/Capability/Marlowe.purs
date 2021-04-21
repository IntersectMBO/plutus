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
import Capability.ContractExe (ContractType(..), contractExe)
import Control.Monad.Except (lift, runExcept)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Foreign.Generic (decodeJSON)
import Halogen (HalogenM)
import Marlowe.PAB (ContractInstanceId, MarloweParams, MarloweData)
import Marlowe.Semantics (Contract, Input, Party, Slot, TokenName)
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Types (AjaxResponse, DecodedAjaxResponse)
import WalletData.Types (PubKeyHash, Wallet)

-- The `ManageMarloweContract` class provides a window on the `ManageContract` class with function
-- calls specific to the Marlowe Plutus contract.
class
  ManageContract m <= ManageMarloweContract m where
  marloweCreateWalletCompanionContract :: Wallet -> m (AjaxResponse ContractInstanceId)
  marloweGetWalletCompanionContractObservableState :: ContractInstanceId -> m (DecodedAjaxResponse (Array (Tuple MarloweParams MarloweData)))
  marloweCreateContract :: Wallet -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse ContractInstanceId)
  marloweApplyInputs :: ContractInstanceId -> MarloweParams -> Array Input -> m (AjaxResponse Unit)
  marloweWait :: ContractInstanceId -> MarloweParams -> m (AjaxResponse Unit)
  marloweAuto :: ContractInstanceId -> MarloweParams -> Party -> Slot -> m (AjaxResponse Unit)
  marloweRedeem :: ContractInstanceId -> MarloweParams -> TokenName -> PubKeyHash -> m (AjaxResponse Unit)

instance monadMarloweAppM :: ManageMarloweContract AppM where
  marloweCreateWalletCompanionContract wallet = activateContract $ ContractActivationArgs { caID: contractExe WalletCompanionContract, caWallet: toBack wallet }
  marloweGetWalletCompanionContractObservableState contractInstanceId = do
    ajaxObservableState <- getContractInstanceObservableState contractInstanceId
    case ajaxObservableState of
      Left ajaxError -> pure $ Left $ Left ajaxError
      Right rawJson -> case runExcept $ decodeJSON $ unwrap rawJson of
        Left decodingError -> pure $ Left $ Right decodingError
        Right observableState -> pure $ Right observableState
  marloweCreateContract wallet roles contract = do
    webContractInstanceId <- activateContract $ ContractActivationArgs { caID: contractExe ControlContract, caWallet: toBack wallet }
    case webContractInstanceId of
      Left _ -> pure webContractInstanceId
      Right contractInstanceId -> do
        let
          bRoles :: Back.Map Back.TokenName Back.PubKeyHash
          bRoles = toBack roles
        _ <- invokeEndpoint contractInstanceId "create" (bRoles /\ contract)
        pure webContractInstanceId
  marloweApplyInputs contractInstanceId params inputs = invokeEndpoint contractInstanceId "apply-inputs" (params /\ inputs)
  marloweWait contractInstanceId params = invokeEndpoint contractInstanceId "wait" params
  marloweAuto contractInstanceId params party slot = invokeEndpoint contractInstanceId "auto" (params /\ party /\ slot)
  marloweRedeem contractInstanceId params tokenName pubKey = invokeEndpoint contractInstanceId "redeem" (params /\ tokenName /\ pubKey)

instance monadMarloweHalogenM :: ManageMarloweContract m => ManageMarloweContract (HalogenM state action slots msg m) where
  marloweCreateWalletCompanionContract = lift <<< marloweCreateWalletCompanionContract
  marloweGetWalletCompanionContractObservableState = lift <<< marloweGetWalletCompanionContractObservableState
  marloweCreateContract wallet roles contract = lift $ marloweCreateContract wallet roles contract
  marloweApplyInputs contractInstanceId params inputs = lift $ marloweApplyInputs contractInstanceId params inputs
  marloweWait contractInstanceId params = lift $ marloweWait contractInstanceId params
  marloweAuto contractInstanceId params party slot = lift $ marloweAuto contractInstanceId params party slot
  marloweRedeem contractInstanceId params tokenName pubKeyHash = lift $ marloweRedeem contractInstanceId params tokenName pubKeyHash
