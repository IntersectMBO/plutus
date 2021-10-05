module API.Contract
  ( activateContract
  , deactivateContract
  , getContractInstanceClientState
  , invokeEndpoint
  , getWalletContractInstances
  , getAllContractInstances
  , getContractDefinitions
  ) where

import Prologue
import API.Request (doGetRequest, doPostRequest, doPutRequest)
import API.Url (toUrlPiece)
import Control.Monad.Error.Class (class MonadError)
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (class Encode)
import MarloweContract (MarloweContract)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)

activateContract ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractActivationArgs MarloweContract -> m ContractInstanceId
activateContract contractActivationArgs = doPostRequest "/api/contract/activate" contractActivationArgs

deactivateContract ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m Unit
deactivateContract contractInstanceId = doPutRequest $ "/api/contract/instance/" <> toUrlPiece contractInstanceId <> "/stop"

getContractInstanceClientState ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m (ContractInstanceClientState MarloweContract)
getContractInstanceClientState contractInstanceId = doGetRequest $ "/api/contract/instance/" <> toUrlPiece contractInstanceId <> "/status"

invokeEndpoint ::
  forall d m.
  Encode d =>
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> String -> d -> m Unit
invokeEndpoint contractInstanceId endpoint payload = doPostRequest ("/api/contract/instance/" <> toUrlPiece contractInstanceId <> "/endpoint/" <> endpoint) payload

getWalletContractInstances ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m (Array (ContractInstanceClientState MarloweContract))
getWalletContractInstances wallet = doGetRequest $ "/api/contract/instances/wallet/" <> toUrlPiece wallet

getAllContractInstances ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractInstanceClientState MarloweContract))
getAllContractInstances = doGetRequest "/api/contract/instances"

getContractDefinitions ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractSignatureResponse MarloweContract))
getContractDefinitions = doGetRequest "/api/contract/definitions"
