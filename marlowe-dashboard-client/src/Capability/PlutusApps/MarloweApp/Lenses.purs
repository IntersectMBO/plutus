module Capability.PlutusApps.MarloweApp.Lenses where

import Prologue
import Capability.PlutusApps.MarloweApp.Types (EndpointMutex, LastResult, MarloweAppEndpointMutexEnv)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Data.UUID (UUID)
import Effect.AVar (AVar)

_marloweAppEndpointMutex :: forall a. Lens' (MarloweAppEndpointMutexEnv a) EndpointMutex
_marloweAppEndpointMutex = prop (SProxy :: SProxy "marloweAppEndpointMutex")

_redeem :: Lens' EndpointMutex (AVar Unit)
_redeem = prop (SProxy :: SProxy "redeem")

_create :: Lens' EndpointMutex (AVar Unit)
_create = prop (SProxy :: SProxy "create")

_applyInputs :: Lens' EndpointMutex (AVar Unit)
_applyInputs = prop (SProxy :: SProxy "applyInputs")

_requests :: Lens' EndpointMutex (AVar (Array (UUID /\ AVar LastResult)))
_requests = prop (SProxy :: SProxy "requests")
