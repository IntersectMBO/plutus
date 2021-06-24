module API.Lenses
  ( _cicContract
  , _cicCurrentState
  , _cicDefinition
  , _cicWallet
  , _observableState
  , _hooks
  , _rqRequest
  , _endpointDescription
  , _endpointDescriptionString
  ) where

import Prelude
import API.Contract (class ContractActivationId)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Plutus.Contract.Effects (ActiveEndpoint, _ActiveEndpoint)
import Plutus.Contract.Resumable (Request, _Request)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse, _PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractInstanceClientState, _ContractInstanceClientState)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId, EndpointDescription, _EndpointDescription)

_cicContract :: forall a. ContractActivationId a => Lens' (ContractInstanceClientState a) ContractInstanceId
_cicContract = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicContract")

_cicCurrentState :: forall a. ContractActivationId a => Lens' (ContractInstanceClientState a) (PartiallyDecodedResponse ActiveEndpoint)
_cicCurrentState = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicCurrentState")

-- TODO: fix Haskell typo ("cicDefintion" instead of "cicDefinition")
_cicDefinition :: forall a. ContractActivationId a => Lens' (ContractInstanceClientState a) a
_cicDefinition = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicDefintion")

_cicWallet :: forall a. ContractActivationId a => Lens' (ContractInstanceClientState a) Wallet
_cicWallet = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicWallet")

----------
_observableState :: Lens' (PartiallyDecodedResponse ActiveEndpoint) RawJson
_observableState = _PartiallyDecodedResponse <<< prop (SProxy :: SProxy "observableState")

_hooks :: Lens' (PartiallyDecodedResponse ActiveEndpoint) (Array (Request ActiveEndpoint))
_hooks = _PartiallyDecodedResponse <<< prop (SProxy :: SProxy "hooks")

_rqRequest :: Lens' (Request ActiveEndpoint) ActiveEndpoint
_rqRequest = _Request <<< prop (SProxy :: SProxy "rqRequest")

_endpointDescription :: Lens' ActiveEndpoint EndpointDescription
_endpointDescription = _ActiveEndpoint <<< prop (SProxy :: SProxy "aeDescription")

_endpointDescriptionString :: Lens' EndpointDescription String
_endpointDescriptionString = _EndpointDescription <<< prop (SProxy :: SProxy "getEndpointDescription")
