module Capability.Marlowe
  ( class MonadMarlowe
  , dummy
  --, marloweCreateWalletCompanionContract
  --, marloweCreateContract
  --, marloweApplyInputs
  --, marloweWait
  --, marloweAuto
  --, marloweRedeem
  ) where

import Prelude
import AppM (AppM(..))
import Capability.Ajax (WebData, runAjax)
import Capability.Contract (class MonadContract)
import Control.Monad.Except (lift)
import Data.Map (Map)
import Data.RawJson (RawJson)
import Halogen (HalogenM)
import Marlowe.Semantics (Contract, Input, Party, Slot)
import Network.RemoteData (RemoteData(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver (postApiNewContractActivate, getApiNewContractInstanceByContractinstanceidStatus, postApiNewContractInstanceByContractinstanceidEndpointByEndpointname, getApiNewContractInstances, getApiNewContractDefinitions)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse)
import Plutus.V1.Ledger.Crypto (PubKeyHash(..))
import Plutus.V1.Ledger.Value (TokenName(..))
import Wallet.Types (ContractInstanceId)

-- The `MonadMarlowe` class provides a window on the `MonadContract` class with function
-- calls specific to the Marlowe Plutus contract.
class
  MonadContract m <= MonadMarlowe m where
  dummy :: m Unit
  --marloweCreateWalletCompanionContract :: Wallet -> m (WebData Unit)
  --marloweCreateContract :: Wallet -> Map TokenName PubKeyHash -> Contract -> m (WebData ContractInstanceId)
  --marloweApplyInputs :: ?MarloweParams -> Array Input -> m (WebData Unit)
  --marloweWait :: ?MarloweParams -> m (WebData Unit)
  --marloweAuto :: ?MarloweParams -> Party -> Slot -> m (WebData Unit)
  --marloweRedeem :: ?MarloweParams -> TokenName -> PubKeyHash -> m (WebData Unit)

instance monadMarloweAppM :: MonadMarlowe AppM where
  dummy = AppM $ pure unit
  --marloweCreateWalletCompanionContract wallet = activateContract $ ContractActivationArgs { caID: WalletCompanion, caWallet: wallet }

  --marloweCreateContract wallet roles contract = do
  --  webContractInstanceId <- activateContract $ ContractActivationArgs { caID: MarloweApp, caWallet: wallet }
  --  case webContractInstanceId of
  --    Success contractInstanceId ->
  --      invokeEndpoint ?(encodeJSON wallet roles) contractInstanceId "create"
  --      pure webContractInstanceId
  --    _ -> pure $ Failure ""

  --marloweApplyInputs params inputs = invokeEndpoint ?(encodeJSON params inputs) ?contractInstanceId "apply-inputs"

  --marloweWait params = invokeEndpoint ?(encodeJSON params) ?contractInstanceId "wait"

  --marloweAuto params party slot = invokeEndpoint ?(encodeJSON params party slot) ?contractInstanceId "auto"

  --marloweRedeem params tokenName pubKeyHash = invokeEndpoint ?(encodeJSON params tokenName pubKeyHash) ?contractInstanceId "wait"

instance monadMarloweHalogenM :: MonadMarlowe m => MonadMarlowe (HalogenM state action slots msg m) where
  dummy = lift dummy
  --marloweCreateWalletCompanionContract = lift <<< marloweCreateWalletCompanionContract

  --marloweCreateContract wallet roles contract = lift $ marloweCreateContract wallet roles contract

  --marloweApplyInputs params inputs = lift $ marloweApplyInputs params inputs

  --marloweWait = lift <<< marloweWait

  --marloweAuto params party slot = lift $ marloweAuto params party slot

  --marloweRedeem params tokenName pubKeyHash = lift $ marloweRedeem params tokenName pubKeyHash
