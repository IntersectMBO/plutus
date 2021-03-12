{-

Experimental webserver implementing the new PAB API.

-}
module Plutus.PAB.Simulator.Server(startServer) where

import           Control.Lens                            (preview)
import           Data.Maybe                              (mapMaybe)
import           Plutus.PAB.Events.Contract              (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse (hooks))
import           Plutus.PAB.Simulator                    (Simulation)
import           Plutus.PAB.Webserver.API                (ContractInstanceClientState (..), NewAPI)
import           Wallet.Types                            (ContractInstanceId)

fromInternalState ::
    ContractInstanceId
    -> PartiallyDecodedResponse ContractPABRequest
    -> ContractInstanceClientState
fromInternalState i resp =
    ContractInstanceClientState
        { cicContract = i
        , cicCurrentState =
            let hks' = mapMaybe (traverse (preview _UserEndpointRequest)) (hooks resp)
            in resp { hooks = hks' }
        }

-- | Start the server. Returns an action that shuts it down again.
startServer :: Simulation (Simulation ())
startServer = pure $ pure ()
