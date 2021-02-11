{-

Types and functions for contract instances that communicate with the outside
world via STM. See note [Contract instance thread model].

-}
module Plutus.PAB.Core.ContractInstance.STM(
    OpenEndpoint(..)
    , BlockchainEnv(..)
    , InstanceState(..)
    ) where

import           Control.Concurrent.STM (TMVar, TVar)
import           Data.Aeson             (Value)
import           Data.Map               (Map)
import           Ledger.Slot            (Slot)
import           Ledger.Tx              (Tx)

{- Note [Contract instance thread model]

In the PAB we run each contract instance in its own thread, following the
design principles for concurrency described in [1].

As a result
* We use STM for concurrency
* We try to avoid queues and use TVars where possible

Contract instances can make requests to services that are managed by the PAB,
such as the wallet backend, the chain index and the node. From the contract's
POV we assume that these requests are responded to instantaneously. To handle these requests the PAB uses the
'Wallet.Emulator.MultiAgent.EmulatedWalletEffects' list of effects.

In addition to making requests to PAB services, contract instances can wait for
events to happen. The events that can be waited upon are produced by the
blockchain (transactions added to the ledger, new slots starting) and by
external clients of the PAB including end-users (calling contract endpoints).
To handle this kind of waiting the PAB uses STM and the types defined in this
module.

# QoS degradation

One of the main goals of the queueless STM design is to avoid a degradation
of the quality of service (QoS) when the system is operating at capacity. This
comes at a price: When the system is under pressure, some updates may be
dropped. In practice this a result of the behaviour of STM's 'retry' primitive,
which only guarantees to retry at some point (not immediately) after a variable
has changed. So if the variable changes again before the retry happens, the
intermediate state is not visible.

What does this imply for the PAB? We could miss out on two things:
1. Crossing slot boundaries
2. Transactions modifying an address that the contract is interested in

It does not mean we drop endpoint calls.

[1] Keynote by Duncan Coutts at the Haskell Symposium 2020. https://vimeo.com/452222780.

-}

-- | An open endpoint that can be responded to.
data OpenEndpoint =
        OpenEndpoint
            { oepName     :: String -- ^ Name of the endpoint
            , oepMeta     :: Maybe Value -- ^ Metadata that was provided by the contract
            , oepResponse :: TMVar Value -- ^ A place to write the response to.
            }

-- | Data about the blockchain that contract instances
--   may be interested in.
data BlockchainEnv =
    BlockchainEnv
        { envLastSlot  :: TVar Slot -- ^ The current slot.
        , envLastBlock :: TVar [Tx] -- ^ Last block that was validated
        -- TODO: Add rollbacks when we get them from
        --       the mock node
        }

-- | The state of an active contract instance.
data InstanceState =
    InstanceState
        { issEndpoints :: TVar (Map String OpenEndpoint) -- ^ Open endpoints that can be responded to.
        , issState     :: TVar Value -- ^ The state of the instance.
        }
