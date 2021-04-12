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
import Bridge (toFront)
import Capability.Ajax (runAjax)
import Control.Monad.Except (lift)
import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Data.Newtype (unwrap)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Data.UUID (toString) as UUID
import Halogen (HalogenM)
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse, _PartiallyDecodedResponse)
import Plutus.PAB.Webserver (getApiNewContractDefinitions, getApiNewContractInstanceByContractinstanceidStatus, getApiNewContractInstances, getApiNewContractInstancesWalletByWalletid, postApiNewContractActivate, postApiNewContractInstanceByContractinstanceidEndpointByEndpointname)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse, _ContractInstanceClientState)
import Types (ContractInstanceId, WebData)
import WalletData.Types (Wallet)

-- The PAB PSGenerator (using Servant.PureScript) automatically generates a PureScript module with
-- functions for calling all PAB API endpoints. This `ManageContract` class wraps these up in a
-- 'capability' monad (https://thomashoneyman.com/guides/real-world-halogen/push-effects-to-the-edges/)
-- with some nicer names, and mapping the result to RemoteData.
class
  Monad m <= ManageContract m where
  activateContract :: ContractActivationArgs ContractExe -> m (WebData ContractInstanceId)
  getContractInstanceClientState :: ContractInstanceId -> m (WebData ContractInstanceClientState)
  getContractInstanceCurrentState :: ContractInstanceId -> m (WebData (PartiallyDecodedResponse ActiveEndpoint))
  getContractInstanceObservableState :: ContractInstanceId -> m (WebData RawJson)
  invokeEndpoint :: RawJson -> ContractInstanceId -> String -> m (WebData Unit)
  getWalletContractInstances :: Wallet -> m (WebData (Array ContractInstanceClientState))
  getAllContractInstances :: m (WebData (Array ContractInstanceClientState))
  getContractDefinitions :: m (WebData (Array (ContractSignatureResponse ContractExe)))

instance monadContractAppM :: ManageContract AppM where
  activateContract contractActivationArgs =
    runAjax
      $ map toFront
      $ postApiNewContractActivate contractActivationArgs
  getContractInstanceClientState contractInstanceId =
    runAjax
      $ getApiNewContractInstanceByContractinstanceidStatus (UUID.toString $ unwrap contractInstanceId)
  getContractInstanceCurrentState contractInstanceId = do
    clientState <- getContractInstanceClientState contractInstanceId
    pure $ map (view _cicCurrentState) clientState
    where
    _cicCurrentState :: Lens' ContractInstanceClientState (PartiallyDecodedResponse ActiveEndpoint)
    _cicCurrentState = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicCurrentState")
  getContractInstanceObservableState contractInstanceId = do
    currentState <- getContractInstanceCurrentState contractInstanceId
    pure $ map (view _observableState) currentState
    where
    _observableState :: Lens' (PartiallyDecodedResponse ActiveEndpoint) RawJson
    _observableState = _PartiallyDecodedResponse <<< prop (SProxy :: SProxy "observableState")
  invokeEndpoint rawJson contractInstanceId endpointDescriptionString =
    runAjax
      $ postApiNewContractInstanceByContractinstanceidEndpointByEndpointname rawJson (UUID.toString $ unwrap contractInstanceId) endpointDescriptionString
  getWalletContractInstances wallet =
    runAjax
      $ getApiNewContractInstancesWalletByWalletid (show $ unwrap wallet)
  getAllContractInstances =
    runAjax
      $ getApiNewContractInstances
  getContractDefinitions =
    runAjax
      $ getApiNewContractDefinitions

instance monadContractHalogenM :: ManageContract m => ManageContract (HalogenM state action slots msg m) where
  activateContract = lift <<< activateContract
  getContractInstanceClientState = lift <<< getContractInstanceClientState
  getContractInstanceCurrentState = lift <<< getContractInstanceCurrentState
  getContractInstanceObservableState = lift <<< getContractInstanceObservableState
  invokeEndpoint payload contractInstanceId endpointDescription = lift $ invokeEndpoint payload contractInstanceId endpointDescription
  getWalletContractInstances = lift <<< getWalletContractInstances
  getAllContractInstances = lift getAllContractInstances
  getContractDefinitions = lift getContractDefinitions
