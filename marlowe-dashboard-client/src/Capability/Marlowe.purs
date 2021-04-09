module Capability.Marlowe
  ( class MonadMarlowe
  , marloweCreateWalletCompanionContract
  --, marloweCreateContract
  , marloweApplyInputs
  , marloweWait
  , marloweAuto
  , marloweRedeem
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (class MonadContract, activateContract, invokeEndpoint)
import Capability.ContractExe (marloweContractExe, walletCompanionContractExe)
import Control.Monad.Except (lift)
import Data.Map (Map)
import Data.RawJson (RawJson(..))
import Data.Tuple.Nested ((/\))
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM)
import MainFrame.Types (WebData)
import Marlowe.Semantics (Contract, Input, Party, Slot)
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Plutus.V1.Ledger.Crypto (PubKeyHash)
import Plutus.V1.Ledger.Value (TokenName)
import Types (ContractInstanceId, MarloweParams)
import WalletData.Types (Wallet)

-- The `MonadMarlowe` class provides a window on the `MonadContract` class with function
-- calls specific to the Marlowe Plutus contract.
class
  MonadContract m <= MonadMarlowe m where
  marloweCreateWalletCompanionContract :: Wallet -> m (WebData ContractInstanceId)
  --marloweCreateContract :: Wallet -> Map TokenName PubKeyHash -> Contract -> m (WebData ContractInstanceId)
  marloweApplyInputs :: ContractInstanceId -> MarloweParams -> Array Input -> m (WebData Unit)
  marloweWait :: ContractInstanceId -> MarloweParams -> m (WebData Unit)
  marloweAuto :: ContractInstanceId -> MarloweParams -> Party -> Slot -> m (WebData Unit)
  marloweRedeem :: ContractInstanceId -> MarloweParams -> TokenName -> PubKeyHash -> m (WebData Unit)

instance monadMarloweAppM :: MonadMarlowe AppM where
  marloweCreateWalletCompanionContract wallet = activateContract $ ContractActivationArgs { caID: marloweContractExe, caWallet: toBack wallet }
  --marloweCreateContract wallet roles contract = do
  --  webContractInstanceId <- activateContract $ ContractActivationArgs { caID: marloweContractExe, caWallet: toBack wallet }
  --  case webContractInstanceId of
  --    Success contractInstanceId ->
  --      invokeEndpoint ?(encodeJSON wallet roles) contractInstanceId "create"
  --      pure webContractInstanceId
  --    _ -> pure $ Failure ""
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
  marloweRedeem contractInstanceId params tokenName pubKeyHash =
    let
      rawJson = RawJson <<< unsafeStringify <<< encode $ (params /\ tokenName /\ pubKeyHash)
    in
      invokeEndpoint rawJson contractInstanceId "redeem"

instance monadMarloweHalogenM :: MonadMarlowe m => MonadMarlowe (HalogenM state action slots msg m) where
  marloweCreateWalletCompanionContract = lift <<< marloweCreateWalletCompanionContract
  --marloweCreateContract wallet roles contract = lift $ marloweCreateContract wallet roles contract
  marloweApplyInputs contractInstanceId params inputs = lift $ marloweApplyInputs contractInstanceId params inputs
  marloweWait contractInstanceId params = lift $ marloweWait contractInstanceId params
  marloweAuto contractInstanceId params party slot = lift $ marloweAuto contractInstanceId params party slot
  marloweRedeem contractInstanceId params tokenName pubKeyHash = lift $ marloweRedeem contractInstanceId params tokenName pubKeyHash
