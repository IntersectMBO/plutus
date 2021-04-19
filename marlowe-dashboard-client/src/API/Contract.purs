module API.Contract
  ( activateContract
  , getContractInstanceClientState
  , invokeEndpoint
  , getWalletContractInstances
  , getAllContractInstances
  , getContractDefinitions
  ) where

import Prelude
import API.Request (doPostRequest, doGetRequest)
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

getContractInstanceClientState ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m ContractInstanceClientState
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
  Wallet -> m (Array ContractInstanceClientState)
getWalletContractInstances wallet = doGetRequest $ "/api/new/contract/instances/wallet/" <> toUrlPiece wallet

getAllContractInstances ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array ContractInstanceClientState)
getAllContractInstances = doGetRequest "/api/new/contract/instances"

getContractDefinitions ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractSignatureResponse ContractExe))
getContractDefinitions = doGetRequest "/api/new/contract/definitions"
