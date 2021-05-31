module API.Contract
  ( class ContractActivationId
  , activateContract
  , deactivateContract
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
import Foreign.Generic (class Decode, class Encode)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState, ContractSignatureResponse)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)

-- PAB contracts can be activated either with a ContractExe (a wrapper around a path the the exe on disk), or
-- some custom data type that identifies the contract (for versions of the plutus-pab that are bundled up with
-- contracts). We provide an empty class and instances for greater type safety, but the class requires no
-- custom functions.
class (Decode a, Encode a) <= ContractActivationId a

instance contractExeContractActivationId :: ContractActivationId ContractExe

activateContract ::
  forall a m.
  ContractActivationId a =>
  MonadError AjaxError m =>
  MonadAff m =>
  ContractActivationArgs a -> m ContractInstanceId
activateContract contractActivationArgs = doPostRequest "/api/new/contract/activate" contractActivationArgs

deactivateContract ::
  forall m.
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m Unit
deactivateContract contractInstanceId = doPutRequest $ "api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/stop"

getContractInstanceClientState ::
  forall a m.
  ContractActivationId a =>
  MonadError AjaxError m =>
  MonadAff m =>
  ContractInstanceId -> m (ContractInstanceClientState a)
getContractInstanceClientState contractInstanceId = doGetRequest $ "/api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/status"

invokeEndpoint ::
  forall d m.
  MonadError AjaxError m =>
  MonadAff m =>
  Encode d =>
  ContractInstanceId -> String -> d -> m Unit
invokeEndpoint contractInstanceId endpoint payload = doPostRequest ("/api/new/contract/instance/" <> toUrlPiece contractInstanceId <> "/endpoint/" <> endpoint) payload

getWalletContractInstances ::
  forall a m.
  ContractActivationId a =>
  MonadError AjaxError m =>
  MonadAff m =>
  Wallet -> m (Array (ContractInstanceClientState a))
getWalletContractInstances wallet = doGetRequest $ "/api/new/contract/instances/wallet/" <> toUrlPiece wallet

getAllContractInstances ::
  forall a m.
  ContractActivationId a =>
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractInstanceClientState a))
getAllContractInstances = doGetRequest "/api/new/contract/instances"

getContractDefinitions ::
  forall a m.
  Decode a =>
  Encode a =>
  MonadError AjaxError m =>
  MonadAff m =>
  m (Array (ContractSignatureResponse a))
getContractDefinitions = doGetRequest "/api/new/contract/definitions"
