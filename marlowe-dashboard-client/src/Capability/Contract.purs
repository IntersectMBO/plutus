module Capability.Contract
  ( class ManageContract
  , activateContract
  , deactivateContract
  , getContractInstanceClientState
  , getContractInstanceCurrentState
  , getContractInstanceObservableState
  , getContractInstanceHooks
  , invokeEndpoint
  , getWalletContractInstances
  , getAllContractInstances
  , getContractDefinitions
  ) where

import Prelude
import API.Contract (class ContractActivationId)
import API.Lenses (_cicCurrentState, _hooks, _observableState)
import AppM (AppM)
import Bridge (toBack, toFront)
import API.Contract as API
import Control.Monad.Except (lift, runExceptT)
import Data.Lens (view)
import Data.RawJson (RawJson)
import Foreign.Generic (class Decode, class Encode)
import Halogen (HalogenM)
import Marlowe.PAB (PlutusAppId)
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Plutus.Contract.Resumable (Request)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..), ContractInstanceClientState, ContractSignatureResponse)
import Types (AjaxResponse)
import WalletData.Types (Wallet)

-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  Monad m <= ManageContract m where
  activateContract :: forall a. ContractActivationId a => a -> Wallet -> m (AjaxResponse PlutusAppId)
  deactivateContract :: PlutusAppId -> m (AjaxResponse Unit)
  getContractInstanceClientState :: forall a. ContractActivationId a => PlutusAppId -> m (AjaxResponse (ContractInstanceClientState a))
  getContractInstanceCurrentState :: PlutusAppId -> m (AjaxResponse (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: PlutusAppId -> m (AjaxResponse RawJson)
  getContractInstanceHooks :: PlutusAppId -> m (AjaxResponse (Array (Request ActiveEndpoint)))
  invokeEndpoint :: forall d. Encode d => PlutusAppId -> String -> d -> m (AjaxResponse Unit)
  getWalletContractInstances :: forall a. ContractActivationId a => Wallet -> m (AjaxResponse (Array (ContractInstanceClientState a)))
  getAllContractInstances :: forall a. ContractActivationId a => m (AjaxResponse (Array (ContractInstanceClientState a)))
  getContractDefinitions :: forall a. ContractActivationId a => m (AjaxResponse (Array (ContractSignatureResponse a)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractExe wallet = map toFront $ runExceptT $ API.activateContract $ ContractActivationArgs { caID: contractExe, caWallet: toBack wallet }
  deactivateContract plutusAppId = runExceptT $ API.deactivateContract (toBack plutusAppId)
  getContractInstanceClientState plutusAppId = runExceptT $ API.getContractInstanceClientState $ toBack plutusAppId
  getContractInstanceCurrentState plutusAppId = do
    clientState <- getContractInstanceClientState plutusAppId
    pure $ map (view _cicCurrentState) clientState
  getContractInstanceObservableState plutusAppId = do
    currentState <- getContractInstanceCurrentState plutusAppId
    pure $ map (view _observableState) currentState
  getContractInstanceHooks plutusAppId = do
    currentState <- getContractInstanceCurrentState plutusAppId
    pure $ map (view _hooks) currentState
  invokeEndpoint plutusAppId endpoint payload = runExceptT $ API.invokeEndpoint (toBack plutusAppId) endpoint payload
  getWalletContractInstances wallet = runExceptT $ API.getWalletContractInstances $ toBack wallet
  getAllContractInstances = runExceptT API.getAllContractInstances
  getContractDefinitions = runExceptT API.getContractDefinitions

instance monadContractHalogenM :: ManageContract m => ManageContract (HalogenM state action slots msg m) where
  activateContract contractExe wallet = lift $ activateContract contractExe wallet
  deactivateContract = lift <<< deactivateContract
  getContractInstanceClientState = lift <<< getContractInstanceClientState
  getContractInstanceCurrentState = lift <<< getContractInstanceCurrentState
  getContractInstanceObservableState = lift <<< getContractInstanceObservableState
  getContractInstanceHooks = lift <<< getContractInstanceHooks
  invokeEndpoint plutusAppId endpointDescription payload = lift $ invokeEndpoint plutusAppId endpointDescription payload
  getWalletContractInstances = lift <<< getWalletContractInstances
  getAllContractInstances = lift getAllContractInstances
  getContractDefinitions = lift getContractDefinitions
