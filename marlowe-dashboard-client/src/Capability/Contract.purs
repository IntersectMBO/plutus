module Capability.Contract
  ( class MonadContract
  , activateContract
  , getContractInstance
  , invokeEndpoint
  , getContractInstances
  , getContractDefinitions
  ) where

import Prelude
import AppM (AppM)
import Capability.Ajax (WebData, runAjax)
import Control.Monad.Except (lift)
import Data.RawJson (RawJson)
import Halogen (HalogenM)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver (postApiNewContractActivate, getApiNewContractInstanceByContractinstanceidStatus, postApiNewContractInstanceByContractinstanceidEndpointByEndpointname, getApiNewContractInstances, getApiNewContractDefinitions)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse)
import Wallet.Types (ContractInstanceId)

-- The PAB PSGenerator (using Servant.PureScript) automatically generates a PureScript module with
-- functions for calling all PAB API endpoints. This `MonadContract` class wraps these up in a
-- 'capability' monad (https://thomashoneyman.com/guides/real-world-halogen/push-effects-to-the-edges/)
-- with some nicer names, and mapping the result to RemoteData.
class
  Monad m <= MonadContract m where
  activateContract :: ContractActivationArgs ContractExe -> m (WebData ContractInstanceId)
  getContractInstance :: ContractInstanceId -> m (WebData ContractInstanceClientState)
  invokeEndpoint :: RawJson -> ContractInstanceId -> String -> m (WebData Unit)
  getContractInstances :: m (WebData (Array ContractInstanceClientState))
  getContractDefinitions :: m (WebData (Array (ContractSignatureResponse ContractExe)))

instance monadContractAppM :: MonadContract AppM where
  activateContract contractActivationArgs =
    runAjax
      $ postApiNewContractActivate contractActivationArgs
  getContractInstance contractInstanceId =
    runAjax
      $ getApiNewContractInstanceByContractinstanceidStatus contractInstanceId
  invokeEndpoint rawJson contractInstanceId endpointDescriptionString =
    runAjax
      $ postApiNewContractInstanceByContractinstanceidEndpointByEndpointname rawJson contractInstanceId endpointDescriptionString
  getContractInstances =
    runAjax
      $ getApiNewContractInstances
  getContractDefinitions =
    runAjax
      $ getApiNewContractDefinitions

instance monadContractHalogenM :: MonadContract m => MonadContract (HalogenM state action slots msg m) where
  activateContract = lift <<< activateContract
  getContractInstance = lift <<< getContractInstance
  invokeEndpoint payload contractInstanceId endpointDescription = lift $ invokeEndpoint payload contractInstanceId endpointDescription
  getContractInstances = lift getContractInstances
  getContractDefinitions = lift getContractDefinitions
