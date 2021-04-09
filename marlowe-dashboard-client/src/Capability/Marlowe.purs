module Capability.Marlowe
  ( class ManageMarloweContract
  , marloweCreateWalletCompanionContract
  , marloweCreateContract
  , marloweApplyInputs
  , marloweWait
  , marloweAuto
  , marloweRedeem
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (class ManageContract, activateContract, invokeEndpoint)
import Capability.ContractExe (marloweContractExe, walletCompanionContractExe)
import Control.Monad.Except (lift)
import Data.Map (Map)
import Data.RawJson (RawJson(..))
import Data.Tuple.Nested ((/\))
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM)
import MainFrame.Types (WebData)
import Marlowe.Semantics (Contract, Input, Party, PubKey, Slot, TokenName)
import Network.RemoteData (RemoteData(..))
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Types (ContractInstanceId, MarloweParams)
import WalletData.Types (Wallet)

-- The `ManageMarloweContract` class provides a window on the `ManageContract` class with function
-- calls specific to the Marlowe Plutus contract.
class
  ManageContract m <= ManageMarloweContract m where
  marloweCreateWalletCompanionContract :: Wallet -> m (WebData ContractInstanceId)
  marloweCreateContract :: Wallet -> Map TokenName PubKey -> Contract -> m (WebData ContractInstanceId)
  marloweApplyInputs :: ContractInstanceId -> MarloweParams -> Array Input -> m (WebData Unit)
  marloweWait :: ContractInstanceId -> MarloweParams -> m (WebData Unit)
  marloweAuto :: ContractInstanceId -> MarloweParams -> Party -> Slot -> m (WebData Unit)
  marloweRedeem :: ContractInstanceId -> MarloweParams -> TokenName -> PubKey -> m (WebData Unit)

instance monadMarloweAppM :: ManageMarloweContract AppM where
  marloweCreateWalletCompanionContract wallet = activateContract $ ContractActivationArgs { caID: walletCompanionContractExe, caWallet: toBack wallet }
  marloweCreateContract wallet roles contract = do
    webContractInstanceId <- activateContract $ ContractActivationArgs { caID: marloweContractExe, caWallet: toBack wallet }
    case webContractInstanceId of
      Success contractInstanceId -> do
        let
          rawJson = RawJson <<< unsafeStringify <<< encode $ (roles /\ contract)
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
  marloweCreateContract wallet roles contract = lift $ marloweCreateContract wallet roles contract
  marloweApplyInputs contractInstanceId params inputs = lift $ marloweApplyInputs contractInstanceId params inputs
  marloweWait contractInstanceId params = lift $ marloweWait contractInstanceId params
  marloweAuto contractInstanceId params party slot = lift $ marloweAuto contractInstanceId params party slot
  marloweRedeem contractInstanceId params tokenName pubKeyHash = lift $ marloweRedeem contractInstanceId params tokenName pubKeyHash
