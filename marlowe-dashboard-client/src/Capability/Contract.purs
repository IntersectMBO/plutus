module Capability.Contract
  ( class ManageContract
  , activateContract
  , getContractInstanceClientState
  , getContractInstanceCurrentState
  , getContractInstanceObservableState
  , invokeEndpoint
  , getWalletContractInstances
  , getAllContractInstances
  , getContractDefinitions
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack, toFront)
import API.Contract as API
import Control.Monad.Except (lift, runExceptT)
import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Foreign.Generic (class Encode)
import Halogen (HalogenM)
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse, _PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse, _ContractInstanceClientState)
import Types (AjaxResponse, ContractInstanceId)
import WalletData.Types (Wallet)

class
  Monad m <= ManageContract m where
  activateContract :: ContractActivationArgs ContractExe -> m (AjaxResponse ContractInstanceId)
  getContractInstanceClientState :: ContractInstanceId -> m (AjaxResponse (ContractInstanceClientState ContractExe))
  getContractInstanceCurrentState :: ContractInstanceId -> m (AjaxResponse (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: ContractInstanceId -> m (AjaxResponse RawJson)
  invokeEndpoint :: forall d. Encode d => ContractInstanceId -> String -> d -> m (AjaxResponse Unit)
  getWalletContractInstances :: Wallet -> m (AjaxResponse (Array (ContractInstanceClientState ContractExe)))
  getAllContractInstances :: m (AjaxResponse (Array (ContractInstanceClientState ContractExe)))
  getContractDefinitions :: m (AjaxResponse (Array (ContractSignatureResponse ContractExe)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractActivationArgs = map toFront $ runExceptT $ API.activateContract contractActivationArgs
  getContractInstanceClientState contractInstanceId = runExceptT $ API.getContractInstanceClientState $ toBack contractInstanceId
  getContractInstanceCurrentState contractInstanceId = do
    clientState <- getContractInstanceClientState contractInstanceId
    pure $ map (view _cicCurrentState) clientState
    where
    _cicCurrentState :: Lens' (ContractInstanceClientState ContractExe) (PartiallyDecodedResponse ActiveEndpoint)
    _cicCurrentState = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicCurrentState")
  getContractInstanceObservableState contractInstanceId = do
    currentState <- getContractInstanceCurrentState contractInstanceId
    pure $ map (view _observableState) currentState
    where
    _observableState :: Lens' (PartiallyDecodedResponse ActiveEndpoint) RawJson
    _observableState = _PartiallyDecodedResponse <<< prop (SProxy :: SProxy "observableState")
  invokeEndpoint contractInstanceId endpoint payload = runExceptT $ API.invokeEndpoint (toBack contractInstanceId) endpoint payload
  getWalletContractInstances wallet = runExceptT $ API.getWalletContractInstances $ toBack wallet
  getAllContractInstances = runExceptT API.getAllContractInstances
  getContractDefinitions = runExceptT API.getContractDefinitions

instance monadContractHalogenM :: ManageContract m => ManageContract (HalogenM state action slots msg m) where
  activateContract = lift <<< activateContract
  getContractInstanceClientState = lift <<< getContractInstanceClientState
  getContractInstanceCurrentState = lift <<< getContractInstanceCurrentState
  getContractInstanceObservableState = lift <<< getContractInstanceObservableState
  invokeEndpoint contractInstanceId endpointDescription payload = lift $ invokeEndpoint contractInstanceId endpointDescription payload
  getWalletContractInstances = lift <<< getWalletContractInstances
  getAllContractInstances = lift getAllContractInstances
  getContractDefinitions = lift getContractDefinitions
