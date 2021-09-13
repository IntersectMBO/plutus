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
import API.Lenses (_cicCurrentState, _hooks, _observableState)
import AppM (AppM)
import Bridge (toBack, toFront)
import API.Contract as API
import Control.Monad.Except (lift, runExceptT)
import Data.Lens (view)
import Data.Maybe
import Data.RawJson (RawJson)
import Foreign.Generic (class Encode)
import Halogen (HalogenM)
import Marlowe.PAB (PlutusAppId)
import MarloweContract (MarloweContract)
import Plutus.Contract.Effects (ActiveEndpoint)
import Plutus.Contract.Resumable (Request)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..), ContractInstanceClientState, ContractSignatureResponse)
import Types (AjaxResponse)
import WalletData.Types (Wallet)

-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  Monad m <= ManageContract m where
  activateContract :: MarloweContract -> Wallet -> m (AjaxResponse PlutusAppId)
  deactivateContract :: PlutusAppId -> m (AjaxResponse Unit)
  getContractInstanceClientState :: PlutusAppId -> m (AjaxResponse (ContractInstanceClientState MarloweContract))
  getContractInstanceCurrentState :: PlutusAppId -> m (AjaxResponse (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: PlutusAppId -> m (AjaxResponse RawJson)
  getContractInstanceHooks :: PlutusAppId -> m (AjaxResponse (Array (Request ActiveEndpoint)))
  invokeEndpoint :: forall d. Encode d => PlutusAppId -> String -> d -> m (AjaxResponse Unit)
  getWalletContractInstances :: Wallet -> m (AjaxResponse (Array (ContractInstanceClientState MarloweContract)))
  getAllContractInstances :: m (AjaxResponse (Array (ContractInstanceClientState MarloweContract)))
  getContractDefinitions :: m (AjaxResponse (Array (ContractSignatureResponse MarloweContract)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractActivationId wallet = map toFront $ runExceptT $ API.activateContract $ ContractActivationArgs { caID: contractActivationId, caWallet: Just (toBack wallet) }
  deactivateContract plutusAppId = runExceptT $ API.deactivateContract $ toBack plutusAppId
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
  activateContract contractActivationId wallet = lift $ activateContract contractActivationId wallet
  deactivateContract = lift <<< deactivateContract
  getContractInstanceClientState = lift <<< getContractInstanceClientState
  getContractInstanceCurrentState = lift <<< getContractInstanceCurrentState
  getContractInstanceObservableState = lift <<< getContractInstanceObservableState
  getContractInstanceHooks = lift <<< getContractInstanceHooks
  invokeEndpoint plutusAppId endpointDescription payload = lift $ invokeEndpoint plutusAppId endpointDescription payload
  getWalletContractInstances = lift <<< getWalletContractInstances
  getAllContractInstances = lift getAllContractInstances
  getContractDefinitions = lift getContractDefinitions
