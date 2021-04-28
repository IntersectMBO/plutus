module Capability.Contract
  ( class ManageContract
  , activateContract
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
import API.Lenses (_cicCurrentState, _hooks, _observableState)
import AppM (AppM)
import Bridge (toBack, toFront)
import API.Contract as API
import Control.Monad.Except (lift, runExceptT)
import Data.Lens (view)
import Data.RawJson (RawJson)
import Foreign.Generic (class Encode)
import Halogen (HalogenM)
import Marlowe.PAB (ContractInstanceId)
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
  activateContract :: ContractExe -> Wallet -> m (AjaxResponse ContractInstanceId)
  getContractInstanceClientState :: ContractInstanceId -> m (AjaxResponse (ContractInstanceClientState ContractExe))
  getContractInstanceCurrentState :: ContractInstanceId -> m (AjaxResponse (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: ContractInstanceId -> m (AjaxResponse RawJson)
  getContractInstanceHooks :: ContractInstanceId -> m (AjaxResponse (Array (Request ActiveEndpoint)))
  invokeEndpoint :: forall d. Encode d => ContractInstanceId -> String -> d -> m (AjaxResponse Unit)
  getWalletContractInstances :: Wallet -> m (AjaxResponse (Array (ContractInstanceClientState ContractExe)))
  getAllContractInstances :: m (AjaxResponse (Array (ContractInstanceClientState ContractExe)))
  getContractDefinitions :: m (AjaxResponse (Array (ContractSignatureResponse ContractExe)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractExe wallet = map toFront $ runExceptT $ API.activateContract $ ContractActivationArgs { caID: contractExe, caWallet: toBack wallet }
  getContractInstanceClientState contractInstanceId = runExceptT $ API.getContractInstanceClientState $ toBack contractInstanceId
  getContractInstanceCurrentState contractInstanceId = do
    clientState <- getContractInstanceClientState contractInstanceId
    pure $ map (view _cicCurrentState) clientState
  getContractInstanceObservableState contractInstanceId = do
    currentState <- getContractInstanceCurrentState contractInstanceId
    pure $ map (view _observableState) currentState
  getContractInstanceHooks contractInstanceId = do
    currentState <- getContractInstanceCurrentState contractInstanceId
    pure $ map (view _hooks) currentState
  invokeEndpoint contractInstanceId endpoint payload = runExceptT $ API.invokeEndpoint (toBack contractInstanceId) endpoint payload
  getWalletContractInstances wallet = runExceptT $ API.getWalletContractInstances $ toBack wallet
  getAllContractInstances = runExceptT API.getAllContractInstances
  getContractDefinitions = runExceptT API.getContractDefinitions

instance monadContractHalogenM :: ManageContract m => ManageContract (HalogenM state action slots msg m) where
  activateContract contractExe wallet = lift $ activateContract contractExe wallet
  getContractInstanceClientState = lift <<< getContractInstanceClientState
  getContractInstanceCurrentState = lift <<< getContractInstanceCurrentState
  getContractInstanceObservableState = lift <<< getContractInstanceObservableState
  getContractInstanceHooks = lift <<< getContractInstanceHooks
  invokeEndpoint contractInstanceId endpointDescription payload = lift $ invokeEndpoint contractInstanceId endpointDescription payload
  getWalletContractInstances = lift <<< getWalletContractInstances
  getAllContractInstances = lift getAllContractInstances
  getContractDefinitions = lift getContractDefinitions
