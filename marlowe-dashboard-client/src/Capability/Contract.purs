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
import Foreign.Generic (class Encode)
import Halogen (HalogenM)
import Marlowe.PAB (PlutusAppId)
import Plutus.Contract.Effects (ActiveEndpoint)
import Plutus.Contract.Resumable (Request)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..), ContractInstanceClientState, ContractSignatureResponse)
import Types (AjaxResponse)
import WalletData.Types (Wallet)

-- TODO (possibly): make `AppM` a `MonadError` and remove all the `runExceptT`s
class
  Monad m <= ManageContract m where
  activateContract :: forall a. ContractActivationId a => a -> Wallet -> m (AjaxResponse PlutusAppId)
  deactivateContract :: forall a. ContractActivationId a => a -> PlutusAppId -> m (AjaxResponse Unit)
  getContractInstanceClientState :: forall a. ContractActivationId a => a -> PlutusAppId -> m (AjaxResponse (ContractInstanceClientState a))
  getContractInstanceCurrentState :: forall a. ContractActivationId a => a -> PlutusAppId -> m (AjaxResponse (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: forall a. ContractActivationId a => a -> PlutusAppId -> m (AjaxResponse RawJson)
  getContractInstanceHooks :: forall a. ContractActivationId a => a -> PlutusAppId -> m (AjaxResponse (Array (Request ActiveEndpoint)))
  invokeEndpoint :: forall a d. ContractActivationId a => Encode d => a -> PlutusAppId -> String -> d -> m (AjaxResponse Unit)
  getWalletContractInstances :: forall a. ContractActivationId a => a -> Wallet -> m (AjaxResponse (Array (ContractInstanceClientState a)))
  getAllContractInstances :: forall a. ContractActivationId a => a -> m (AjaxResponse (Array (ContractInstanceClientState a)))
  getContractDefinitions :: forall a. ContractActivationId a => a -> m (AjaxResponse (Array (ContractSignatureResponse a)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractActivationId wallet = map toFront $ runExceptT $ API.activateContract $ ContractActivationArgs { caID: contractActivationId, caWallet: toBack wallet }
  deactivateContract contractActivationId plutusAppId = runExceptT $ API.deactivateContract contractActivationId (toBack plutusAppId)
  getContractInstanceClientState contractActivationId plutusAppId = runExceptT $ API.getContractInstanceClientState contractActivationId $ toBack plutusAppId
  getContractInstanceCurrentState contractActivationId plutusAppId = do
    clientState <- getContractInstanceClientState contractActivationId plutusAppId
    pure $ map (view _cicCurrentState) clientState
  getContractInstanceObservableState contractActivationId plutusAppId = do
    currentState <- getContractInstanceCurrentState contractActivationId plutusAppId
    pure $ map (view _observableState) currentState
  getContractInstanceHooks contractActivationId plutusAppId = do
    currentState <- getContractInstanceCurrentState contractActivationId plutusAppId
    pure $ map (view _hooks) currentState
  invokeEndpoint contractActivationId plutusAppId endpoint payload = runExceptT $ API.invokeEndpoint contractActivationId (toBack plutusAppId) endpoint payload
  getWalletContractInstances contractActivationId wallet = runExceptT $ API.getWalletContractInstances contractActivationId $ toBack wallet
  getAllContractInstances contractActivationId = runExceptT $ API.getAllContractInstances contractActivationId
  getContractDefinitions contractActivationId = runExceptT $ API.getContractDefinitions contractActivationId

instance monadContractHalogenM :: ManageContract m => ManageContract (HalogenM state action slots msg m) where
  activateContract contractActivationId wallet = lift $ activateContract contractActivationId wallet
  deactivateContract contractActivationId plutusAppId = lift $ deactivateContract contractActivationId plutusAppId
  getContractInstanceClientState contractActivationId plutusAppId = lift $ getContractInstanceClientState contractActivationId plutusAppId
  getContractInstanceCurrentState contractActivationId plutusAppId = lift $ getContractInstanceCurrentState contractActivationId plutusAppId
  getContractInstanceObservableState contractActivationId plutusAppId = lift $ getContractInstanceObservableState contractActivationId plutusAppId
  getContractInstanceHooks contractActivationId plutusAppId = lift $ getContractInstanceHooks contractActivationId plutusAppId
  invokeEndpoint contractActivationId plutusAppId endpointDescription payload = lift $ invokeEndpoint contractActivationId plutusAppId endpointDescription payload
  getWalletContractInstances contractActivationId wallet = lift $ getWalletContractInstances contractActivationId wallet
  getAllContractInstances = lift <<< getAllContractInstances
  getContractDefinitions = lift <<< getContractDefinitions
