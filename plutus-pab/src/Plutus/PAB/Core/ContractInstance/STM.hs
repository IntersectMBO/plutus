{-

Types and functions for contract instances that communicate with the outside
world via STM. See note [Contract instance thread model].

-}
module Plutus.PAB.Core.ContractInstance.STM(
    OpenEndpoint(..)
    , BlockchainEnv(..)
    , InstanceState(..)
    , Activity(..)
    , TxStatus(..)
    ) where

import           Control.Concurrent.STM (TMVar, TVar)
import           Data.Aeson             (Value)
import           Data.Map               (Map)
import           Data.Set               (Set)
import           Ledger                 (Address, Slot, TxId)
import           Ledger.AddressMap      (AddressMap)

{- Note [Contract instance thread model]

In the PAB we run each contract instance in its own thread, following the
design principles for concurrency described in [1].

As a result
* We use STM for concurrency
* We try to avoid queues and use TVars where possible

Contract instances can make requests to services that are managed by the PAB,
such as the wallet backend, the chain index and the node. From the contract's
POV we assume that these requests are responded to instantaneously. To handle
these requests the PAB uses the
'Wallet.Emulator.MultiAgent.EmulatedWalletEffects' list of effects.

In addition to making requests to PAB services, contract instances can wait for
events to happen. The events that can be waited upon are produced by the
blockchain (transactions added to the ledger, new slots starting) and by
external clients of the PAB including end-users (calling contract endpoints).
To handle this kind of waiting the PAB uses STM and the types defined in this
module.

# QoS

One of the main goals of the queueless STM design is to avoid a degradation
of the quality of service (QoS) when the system is operating at capacity. This
comes at a price: When the system is under pressure, some updates may be
dropped. In practice this a result of the behaviour of STM's 'retry' primitive,
which only guarantees to retry at some point (not immediately) after a variable
has changed. So if the variable changes again before the retry happens, the
intermediate state is not visible.

# Event types

What does this imply for the PAB? Rather than being notified of changes, we want
to be notified of new states. Therefore we choose the following types for the
events that we want to know about.

* Time: TVar with current time
* Modifications to an address: TVar with current UTXO set of that address
* Transactions & rollbacks: TVar with current status of transactions
* Endpoints: For each endpoint a TMVar that changes from empty to full if & when
  the endpoint gets called.

All other requests of the contract are handled using the wallet effects (chain index,
tx construction and signing).

[1] Keynote by Duncan Coutts at the Haskell Symposium 2020. https://vimeo.com/452222780.

-}

-- | An open endpoint that can be responded to.
data OpenEndpoint =
        OpenEndpoint
            { oepName     :: String -- ^ Name of the endpoint
            , oepMeta     :: Maybe Value -- ^ Metadata that was provided by the contract
            , oepResponse :: TMVar Value -- ^ A place to write the response to.
            }

{- Note [TxStatus state machine]

The status of a transaction is described by the following state machine.

Current state        | New state(s)
-----------------------------------------------------
InMemPool            | Invalid, TentativelyConfirmed
Invalid              | -
TentativelyConfirmed | InMemPool, DefinitelyConfirmed
DefinitelyConfirmed  | -

The initial state after submitting the transaction is InMemPool.

-}

-- | Status of a transaction from the perspective of the contract.
--   See note [TxStatus state machine]
data TxStatus =
    InMemPool -- ^ Not on chain yet
    | Invalid -- ^ Invalid (its inputs were spent or its validation range has passed)
    | TentativelyConfirmed -- ^ On chain, can still be rolled back
    | DefinitelyConfirmed -- ^ Cannot be rolled back

-- | Data about the blockchain that contract instances
--   may be interested in.
data BlockchainEnv =
    BlockchainEnv
        { beCurrentSlot :: TVar Slot
        , beAddressMap  :: TVar AddressMap
        , beTxChanges   :: TVar (Map TxId TxStatus)
        }

data Activity = Active | Done

-- | The state of an active contract instance.
data InstanceState =
    InstanceState
        { issEndpoints    :: TVar (Map String OpenEndpoint) -- ^ Open endpoints that can be responded to.
        , issAddresses    :: TVar (Set Address) -- ^ Addresses that the contract wants to watch
        , issTransactions :: TVar (Set TxId) -- ^ Transactions whose status the contract is interested in
        , issStatus       :: TVar Activity -- ^ Whether the instance is still running.
        }
