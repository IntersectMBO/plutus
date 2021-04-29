module API.Contract
  ( activateContract
  , getContractInstanceClientState
  , invokeEndpoint
  , getWalletContractInstances
  , getAllContractInstances
  , getContractDefinitions
  ) where

import Prelude
import API.Request (doGetRequest, doPostRequest, doPutRequest)
import API.Url (toUrlPiece)
import Control.Monad.Error.Class (class MonadError)
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (class Encode)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)

activateContract ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractActivationArgs ContractExe -> m ContractInstanceId
activateContract contractActivationArgs = doPostRequest "/api/new/contract/activate" contractActivationArgs

deactivateContract ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m Unit
deactivateContract contractInstanceId = doPutRequest $ "api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/stop"

getContractInstanceClientState ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m (ContractInstanceClientState ContractExe)
getContractInstanceClientState contractInstanceId = doGetRequest $ "/api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/status"

invokeEndpoint ::
  forall d m.
  MonadError AjaxError m =>
  MonadAff m =>
  Encode d =>
  ContractInstanceId -> String -> d -> m Unit
invokeEndpoint contractInstanceId endpoint payload = doPostRequest ("/api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/endpoint/" <> endpoint) payload

getWalletContractInstances ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m (Array (ContractInstanceClientState ContractExe))
getWalletContractInstances wallet = doGetRequest $ "/api/new/contract/instances/wallet/" <> toUrlPiece wallet

getAllContractInstances ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractInstanceClientState ContractExe))
getAllContractInstances = doGetRequest "/api/new/contract/instances"

getContractDefinitions ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractSignatureResponse ContractExe))
getContractDefinitions = doGetRequest "/api/new/contract/definitions"
