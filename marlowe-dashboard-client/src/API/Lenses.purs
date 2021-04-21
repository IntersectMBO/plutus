module API.Lenses
  ( _cicCurrentState
  , _observableState
  , _hooks
  , _rqRequest
  , _endpointDescription
  , _endpointDescriptionString
  ) where

import Prelude
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint, _ActiveEndpoint)
import Plutus.Contract.Resumable (Request, _Request)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse, _PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ContractInstanceClientState, _ContractInstanceClientState)
import Wallet.Types (EndpointDescription, _EndpointDescription)

_cicCurrentState :: Lens' ContractInstanceClientState (PartiallyDecodedResponse ActiveEndpoint)
_cicCurrentState = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicCurrentState")

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
