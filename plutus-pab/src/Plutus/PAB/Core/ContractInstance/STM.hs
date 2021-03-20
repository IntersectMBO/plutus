{-# LANGUAGE NamedFieldPuns #-}
{-

Types and functions for contract instances that communicate with the outside
world via STM. See note [Contract instance thread model].

-}
module Plutus.PAB.Core.ContractInstance.STM(
    BlockchainEnv(..)
    , emptyBlockchainEnv
    , awaitSlot
    , awaitEndpointResponse
    , waitForAddressChange
    , waitForTxConfirmed
    , valueAt
    , currentSlot
    -- * State of a contract instance
    , InstanceState(..)
    , emptyInstanceState
    , OpenEndpoint(..)
    , clearEndpoints
    , addEndpoint
    , addAddress
    , addTransaction
    , setActivity
    , setObservableState
    , openEndpoints
    , callEndpoint
    , finalResult
    , Activity(..)
    , TxStatus(..)
    -- * State of all running contract instances
    , InstancesState
    , emptyInstancesState
    , insertInstance
    , watchedAddresses
    , watchedTransactions
    , callEndpointOnInstance
    , obervableContractState
    , instanceState
    , instanceIDs
    ) where

import           Control.Applicative                               (Alternative (..))
import           Control.Concurrent.STM                            (STM, TMVar, TVar)
import qualified Control.Concurrent.STM                            as STM
import           Control.Lens                                      (view)
import           Control.Monad                                     (guard)
import           Data.Aeson                                        (Value)
import           Data.Foldable                                     (fold)
import           Data.Map                                          (Map)
import qualified Data.Map                                          as Map
import           Data.Set                                          (Set)
import qualified Data.Set                                          as Set
import           Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..), EndpointValue (..))
import           Plutus.Contract.Resumable                (IterationID, Request (..), RequestID)
import           Ledger                                            (Address, Slot, TxId, txOutTxOut, txOutValue)
import           Ledger.AddressMap                                 (AddressMap)
import qualified Ledger.AddressMap                                 as AM
import qualified Ledger.Value                                      as Value
import           Wallet.Emulator.ChainIndex.Index                  (ChainIndex)
import qualified Wallet.Emulator.ChainIndex.Index                  as Index
import           Wallet.Types                                      (AddressChangeRequest (..),
                                                                    AddressChangeResponse (..), ContractInstanceId,
                                                                    EndpointDescription, NotificationError (..))

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
            { oepName     :: ActiveEndpoint -- ^ Name of the endpoint
            , oepResponse :: TMVar (EndpointValue Value) -- ^ A place to write the response to.
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
    deriving (Eq, Ord, Show)

isConfirmed :: TxStatus -> Bool
isConfirmed TentativelyConfirmed = True
isConfirmed DefinitelyConfirmed  = True
isConfirmed _                    = False

-- | Data about the blockchain that contract instances
--   may be interested in.
data BlockchainEnv =
    BlockchainEnv
        { beCurrentSlot :: TVar Slot -- ^ Current slot
        , beAddressMap  :: TVar AddressMap -- ^ Address map used for updating the chain index
        , beTxIndex     :: TVar ChainIndex -- ^ Local chain index (not persisted)
        , beTxChanges   :: TVar (Map TxId TxStatus) -- ^ Map of transaction IDs to statuses
        }

-- | Initialise an empty 'BlockchainEnv' value
emptyBlockchainEnv :: STM BlockchainEnv
emptyBlockchainEnv =
    BlockchainEnv
        <$> STM.newTVar 0
        <*> STM.newTVar mempty
        <*> STM.newTVar mempty
        <*> STM.newTVar mempty

-- | Wait until the current slot is greater than or equal to the
--   target slot, then return the current slot.
awaitSlot :: Slot -> BlockchainEnv -> STM Slot
awaitSlot targetSlot BlockchainEnv{beCurrentSlot} = do
    current <- STM.readTVar beCurrentSlot
    guard (current >= targetSlot)
    pure current

-- | Wait for an endpoint response.
awaitEndpointResponse :: Request ActiveEndpoint -> InstanceState -> STM (EndpointValue Value)
awaitEndpointResponse Request{rqID, itID} InstanceState{issEndpoints} = do
    currentEndpoints <- STM.readTVar issEndpoints
    let openEndpoint = Map.lookup (rqID, itID) currentEndpoints
    case openEndpoint of
        Nothing                        -> empty
        Just OpenEndpoint{oepResponse} -> STM.readTMVar oepResponse

-- | Whether the contract instance is still waiting for an event.
data Activity =
        Active
        | Done (Maybe Value) -- ^ Instance finished, possibly with an error

-- | The state of an active contract instance.
data InstanceState =
    InstanceState
        { issEndpoints       :: TVar (Map (RequestID, IterationID) OpenEndpoint) -- ^ Open endpoints that can be responded to.
        , issAddresses       :: TVar (Set Address) -- ^ Addresses that the contract wants to watch
        , issTransactions    :: TVar (Set TxId) -- ^ Transactions whose status the contract is interested in
        , issStatus          :: TVar Activity -- ^ Whether the instance is still running.
        , issObservableState :: TVar (Maybe Value) -- ^ Serialised observable state of the contract instance (if available)
        }

-- | An 'InstanceState' value with empty fields
emptyInstanceState :: STM InstanceState
emptyInstanceState =
    InstanceState
        <$> STM.newTVar mempty
        <*> STM.newTVar mempty
        <*> STM.newTVar mempty
        <*> STM.newTVar Active
        <*> STM.newTVar Nothing

-- | Add an address to the set of addresses that the instance is watching
addAddress :: Address -> InstanceState -> STM ()
addAddress addr InstanceState{issAddresses} = STM.modifyTVar issAddresses (Set.insert addr)

-- | Add a transaction hash to the set of transactions that the instance is
--   interested in
addTransaction :: TxId -> InstanceState -> STM ()
addTransaction txid InstanceState{issTransactions} = STM.modifyTVar issTransactions (Set.insert txid)

-- | Set the 'Activity' of the instance
setActivity :: Activity -> InstanceState -> STM ()
setActivity a InstanceState{issStatus} = STM.writeTVar issStatus a

-- | Empty the list of open enpoints that can be called on the instance
clearEndpoints :: InstanceState -> STM ()
clearEndpoints InstanceState{issEndpoints} = STM.writeTVar issEndpoints Map.empty

-- | Add an active endpoint to the instance's list of active endpoints.
addEndpoint :: Request ActiveEndpoint -> InstanceState -> STM ()
addEndpoint Request{rqID, itID, rqRequest} InstanceState{issEndpoints} = do
    endpoint <- OpenEndpoint rqRequest <$> STM.newEmptyTMVar
    STM.modifyTVar issEndpoints (Map.insert (rqID, itID) endpoint)

-- | Write a new value into the contract instance's observable state.
setObservableState :: Value -> InstanceState -> STM ()
setObservableState vl InstanceState{issObservableState} =
    STM.writeTVar issObservableState (Just vl)

-- | The list of all endpoints that can be called on the instance
openEndpoints :: InstanceState -> STM (Map (RequestID, IterationID) OpenEndpoint)
openEndpoints = STM.readTVar . issEndpoints

-- | Call an endpoint with a JSON value.
callEndpoint :: OpenEndpoint -> EndpointValue Value -> STM ()
callEndpoint OpenEndpoint{oepResponse} = STM.putTMVar oepResponse

-- | Call an endpoint on a contract instance.
callEndpointOnInstance :: InstancesState -> EndpointDescription -> Value -> ContractInstanceId -> STM (Maybe NotificationError)
callEndpointOnInstance (InstancesState m) endpointDescription value instanceID = do
    instances <- STM.readTVar m
    case Map.lookup instanceID instances of
        Nothing -> pure $ Just $ InstanceDoesNotExist instanceID
        Just is -> do
            mp <- openEndpoints is
            let match OpenEndpoint{oepName=ActiveEndpoint{aeDescription=d}} = endpointDescription == d
            case filter match $ fmap snd $ Map.toList mp of
                []   -> pure $ Just $ EndpointNotAvailable instanceID endpointDescription
                [ep] -> callEndpoint ep (EndpointValue value) >> pure Nothing
                _    -> pure $ Just $ MoreThanOneEndpointAvailable instanceID endpointDescription

-- | State of all contract instances that are currently running
newtype InstancesState = InstancesState (TVar (Map ContractInstanceId InstanceState))

-- | Initialise the 'InstancesState' with an empty value
emptyInstancesState :: STM InstancesState
emptyInstancesState = InstancesState <$> STM.newTVar mempty

-- | The IDs of all contract instances
instanceIDs :: InstancesState -> STM (Set ContractInstanceId)
instanceIDs (InstancesState m) = Map.keysSet <$> STM.readTVar m

-- | The 'InstanceState' of the contract instance. Retries of the state can't
--   be found in the map.
instanceState :: ContractInstanceId -> InstancesState -> STM InstanceState
instanceState instanceId (InstancesState m) = do
    mp <- STM.readTVar m
    case Map.lookup instanceId mp of
        Nothing -> empty
        Just s  -> pure s

-- | Get the observable state of the contract instance. Blocks if the
--   state is not available yet.
obervableContractState :: ContractInstanceId -> InstancesState -> STM Value
obervableContractState instanceId m = do
    InstanceState{issObservableState} <- instanceState instanceId m
    v <- STM.readTVar issObservableState
    case v of
        Nothing -> empty
        Just k  -> pure k

-- | Return the final state of the contract when it is finished (possibly an
--   error)
finalResult :: ContractInstanceId -> InstancesState -> STM (Maybe Value)
finalResult instanceId m = do
    InstanceState{issStatus} <- instanceState instanceId m
    v <- STM.readTVar issStatus
    case v of
        Done r -> pure r
        _      -> empty

-- | Insert an 'InstanceState' value into the 'InstancesState'
insertInstance :: ContractInstanceId -> InstanceState -> InstancesState -> STM ()
insertInstance instanceID state (InstancesState m) = STM.modifyTVar m (Map.insert instanceID state)

-- | The addresses that are currently watched by the contract instances
watchedAddresses :: InstancesState -> STM (Set Address)
watchedAddresses (InstancesState m) = do
    mp <- STM.readTVar m
    allSets <- traverse (STM.readTVar . issAddresses) (snd <$> Map.toList mp)
    pure $ fold allSets

-- | The transactions that are currently watched by the contract instances
watchedTransactions :: InstancesState -> STM (Set TxId)
watchedTransactions (InstancesState m) = do
    mp <- STM.readTVar m
    allSets <- traverse (STM.readTVar . issTransactions) (snd <$> Map.toList mp)
    pure $ fold allSets

-- | Respond to an 'AddressChangeRequest' for a future slot.
waitForAddressChange :: AddressChangeRequest -> BlockchainEnv -> STM AddressChangeResponse
waitForAddressChange AddressChangeRequest{acreqSlot, acreqAddress} b@BlockchainEnv{beTxIndex} = do
    _ <- awaitSlot (succ acreqSlot) b
    idx <- STM.readTVar beTxIndex
    pure
        AddressChangeResponse
        { acrAddress = acreqAddress
        , acrSlot    = acreqSlot
        , acrTxns    = Index.ciTx <$> Index.transactionsAt idx acreqSlot acreqAddress
        }

-- | Wait for the status of a transaction to be confirmed. TODO: Should be "status changed", some txns may never get to confirmed status
waitForTxConfirmed :: TxId -> BlockchainEnv -> STM TxConfirmed
waitForTxConfirmed tx BlockchainEnv{beTxChanges} = do
    idx <- STM.readTVar beTxChanges
    guard $ maybe False isConfirmed (Map.lookup tx idx)
    pure (TxConfirmed tx)

-- | The value at an address
valueAt :: Address -> BlockchainEnv -> STM Value.Value
valueAt addr BlockchainEnv{beAddressMap} = do
    am <- STM.readTVar beAddressMap
    let utxos = view (AM.fundsAt addr) am
    return $ foldMap (txOutValue . txOutTxOut) utxos

-- | The current slot number
currentSlot :: BlockchainEnv -> STM Slot
currentSlot BlockchainEnv{beCurrentSlot} = STM.readTVar beCurrentSlot
