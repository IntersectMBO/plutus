{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-

Types and functions for contract instances that communicate with the outside
world via STM. See note [Contract instance thread model].

-}
module Plutus.PAB.Core.ContractInstance.STM(
    BlockchainEnv(..)
    , emptyBlockchainEnv
    , awaitSlot
    , awaitTime
    , awaitEndpointResponse
    , waitForTxStatusChange
    , valueAt
    , currentSlot
    -- * State of a contract instance
    , InstanceState(..)
    , emptyInstanceState
    , OpenEndpoint(..)
    , OpenTxOutProducedRequest(..)
    , OpenTxOutSpentRequest(..)
    , clearEndpoints
    , addEndpoint
    , addUtxoSpentReq
    , waitForUtxoSpent
    , addUtxoProducedReq
    , waitForUtxoProduced
    , addAddress
    , addTransaction
    , setActivity
    , setObservableState
    , openEndpoints
    , callEndpoint
    , finalResult
    , Activity(..)
    -- * State of all running contract instances
    , InstancesState
    , emptyInstancesState
    , insertInstance
    , watchedAddresses
    , watchedTransactions
    , callEndpointOnInstance
    , callEndpointOnInstanceTimeout
    , observableContractState
    , instanceState
    , instanceIDs
    , runningInstances
    , instancesClientEnv
    , InstanceClientEnv(..)
    ) where

import           Control.Applicative       (Alternative (..))
import           Control.Concurrent.STM    (STM, TMVar, TVar)
import qualified Control.Concurrent.STM    as STM
import           Control.Lens              (view)
import           Control.Monad             (guard, (<=<))
import           Data.Aeson                (Value)
import           Data.Default              (def)
import           Data.Foldable             (fold)
import           Data.List.NonEmpty        (NonEmpty)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Ledger                    (Address, Slot, TxId, TxOutRef, txOutTxOut, txOutValue)
import           Ledger.AddressMap         (AddressMap)
import qualified Ledger.AddressMap         as AM
import           Ledger.Time               (POSIXTime (..))
import qualified Ledger.TimeSlot           as TimeSlot
import qualified Ledger.Value              as Value
import           Plutus.ChainIndex         (ChainIndexTx, TxStatus (..))
import           Plutus.Contract.Effects   (ActiveEndpoint (..))
import           Plutus.Contract.Resumable (IterationID, Request (..), RequestID)
import           Wallet.Types              (ContractInstanceId, EndpointDescription, EndpointValue (..),
                                            NotificationError (..))

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

-- | A TxOutRef that a contract instance is watching
data OpenTxOutSpentRequest =
    OpenTxOutSpentRequest
        { osrOutRef     :: TxOutRef -- ^ The 'TxOutRef' that the instance is watching
        , osrSpendingTx :: TMVar ChainIndexTx -- ^ A place to write the spending transaction to
        }

data OpenTxOutProducedRequest =
    OpenTxOutProducedRequest
        { otxAddress       :: Address -- ^ 'Address' that the contract instance is watching (TODO: Should be ViewAddress -- SCP-2628)
        , otxProducingTxns :: TMVar (NonEmpty ChainIndexTx) -- ^ A place to write the producing transactions to
        }

-- | Data about the blockchain that contract instances
--   may be interested in.
data BlockchainEnv =
    BlockchainEnv
        { beCurrentSlot :: TVar Slot -- ^ Current slot
        , beAddressMap  :: TVar AddressMap -- ^ Address map used for updating the chain index. TODO: Should not be part of 'BlockchainEnv'
        , beTxChanges   :: TVar (Map TxId TxStatus) -- ^ Map of transaction IDs to statuses
        }

-- data TxStatusMap = TxStatusMap
--   { txmChainPoint :: ChainPoint
--   , txmState      :: TxIdState
--   }

-- | Initialise an empty 'BlockchainEnv' value
emptyBlockchainEnv :: STM BlockchainEnv
emptyBlockchainEnv =
    BlockchainEnv
        <$> STM.newTVar 0
        <*> STM.newTVar mempty
        <*> STM.newTVar mempty

-- | Wait until the current slot is greater than or equal to the
--   target slot, then return the current slot.
awaitSlot :: Slot -> BlockchainEnv -> STM Slot
awaitSlot targetSlot BlockchainEnv{beCurrentSlot} = do
    current <- STM.readTVar beCurrentSlot
    guard (current >= targetSlot)
    pure current

-- | Wait until the current time is greater than or equal to the
-- target time, then return the current time.
awaitTime :: POSIXTime -> BlockchainEnv -> STM POSIXTime
awaitTime targetTime be = do
    let targetSlot = TimeSlot.posixTimeToEnclosingSlot def targetTime
    TimeSlot.slotToEndPOSIXTime def <$> awaitSlot targetSlot be

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
        | Stopped -- ^ Instance was stopped before all requests were handled
        | Done (Maybe Value) -- ^ Instance finished, possibly with an error
        deriving (Eq, Show)

-- | The state of an active contract instance.
data InstanceState =
    InstanceState
        { issEndpoints       :: TVar (Map (RequestID, IterationID) OpenEndpoint) -- ^ Open endpoints that can be responded to.
        , issAddresses       :: TVar (Set Address) -- ^ Addresses that the contract wants to watch -- FIXME: Delete?
        , issTransactions    :: TVar (Set TxId) -- ^ Transactions whose status the contract is interested in
        , issStatus          :: TVar Activity -- ^ Whether the instance is still running.
        , issObservableState :: TVar (Maybe Value) -- ^ Serialised observable state of the contract instance (if available)
        , issStop            :: TMVar () -- ^ Stop the instance if a value is written into the TMVar.
        , issTxOutRefs       :: TVar (Map (RequestID, IterationID) OpenTxOutSpentRequest)
        , issAddressRefs     :: TVar (Map (RequestID, IterationID) OpenTxOutProducedRequest)
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
        <*> STM.newEmptyTMVar
        <*> STM.newTVar mempty
        <*> STM.newTVar mempty

-- | Events that the contract instances are waiting for, indexed by keys that are
--   readily available in the node client (ie. that can be produced from just a
--   block without any additional information)
data InstanceClientEnv = InstanceClientEnv
  { ceUtxoSpentRequests    :: Map TxOutRef [OpenTxOutSpentRequest]
  , ceUtxoProducedRequests :: Map Address [OpenTxOutProducedRequest] -- TODO: ViewAddress
  }

instance Semigroup InstanceClientEnv where
    l <> r =
        InstanceClientEnv
            { ceUtxoProducedRequests = Map.unionWith (<>) (ceUtxoProducedRequests l) (ceUtxoProducedRequests r)
            , ceUtxoSpentRequests = Map.unionWith (<>) (ceUtxoSpentRequests l) (ceUtxoSpentRequests r)
            }

instance Monoid InstanceClientEnv where
    mappend = (<>)
    mempty = InstanceClientEnv mempty mempty

instancesClientEnv :: InstancesState -> STM InstanceClientEnv
instancesClientEnv = fmap fold . traverse instanceClientEnv <=< STM.readTVar . getInstancesState

instanceClientEnv :: InstanceState -> STM InstanceClientEnv
instanceClientEnv InstanceState{issTxOutRefs, issAddressRefs} =
  InstanceClientEnv
    <$> (Map.fromList . fmap ((\r@OpenTxOutSpentRequest{osrOutRef} -> (osrOutRef, [r])) . snd) . Map.toList <$> STM.readTVar issTxOutRefs)
    <*> (Map.fromList . fmap ((\r@OpenTxOutProducedRequest{otxAddress} -> (otxAddress, [r])) . snd) . Map.toList  <$> STM.readTVar issAddressRefs)

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
clearEndpoints InstanceState{issEndpoints, issTxOutRefs, issAddressRefs} = do
    STM.writeTVar issEndpoints Map.empty
    STM.writeTVar issTxOutRefs Map.empty
    STM.writeTVar issAddressRefs Map.empty

-- | Add an active endpoint to the instance's list of active endpoints.
addEndpoint :: Request ActiveEndpoint -> InstanceState -> STM ()
addEndpoint Request{rqID, itID, rqRequest} InstanceState{issEndpoints} = do
    endpoint <- OpenEndpoint rqRequest <$> STM.newEmptyTMVar
    STM.modifyTVar issEndpoints (Map.insert (rqID, itID) endpoint)

-- | Add a new 'OpenTxOutSpentRequest' to the instance's list of
--   utxo spent requests
addUtxoSpentReq :: Request TxOutRef -> InstanceState -> STM ()
addUtxoSpentReq Request{rqID, itID, rqRequest} InstanceState{issTxOutRefs} = do
    request <- OpenTxOutSpentRequest rqRequest <$> STM.newEmptyTMVar
    STM.modifyTVar issTxOutRefs (Map.insert (rqID, itID) request)

waitForUtxoSpent :: Request TxOutRef -> InstanceState -> STM ChainIndexTx
waitForUtxoSpent Request{rqID, itID} InstanceState{issTxOutRefs} = do
    theMap <- STM.readTVar issTxOutRefs
    case Map.lookup (rqID, itID) theMap of
        Nothing                                   -> empty
        Just OpenTxOutSpentRequest{osrSpendingTx} -> STM.readTMVar osrSpendingTx

-- | Add a new 'OpenTxOutProducedRequest' to the instance's list of
--   utxo produced requests
addUtxoProducedReq :: Request Address -> InstanceState -> STM ()
addUtxoProducedReq Request{rqID, itID, rqRequest} InstanceState{issAddressRefs} = do
    request <- OpenTxOutProducedRequest rqRequest <$> STM.newEmptyTMVar
    STM.modifyTVar issAddressRefs (Map.insert (rqID, itID) request)

waitForUtxoProduced :: Request Address -> InstanceState -> STM (NonEmpty ChainIndexTx)
waitForUtxoProduced Request{rqID, itID} InstanceState{issAddressRefs} = do
    theMap <- STM.readTVar issAddressRefs
    case Map.lookup (rqID, itID) theMap of
        Nothing                                         -> empty
        Just OpenTxOutProducedRequest{otxProducingTxns} -> STM.readTMVar otxProducingTxns

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

-- | Call an endpoint on a contract instance. Fail immediately if the endpoint is not active.
callEndpointOnInstance :: InstancesState -> EndpointDescription -> Value -> ContractInstanceId -> STM (Maybe NotificationError)
callEndpointOnInstance s endpointDescription value instanceID =
    let err = pure $ Just $ EndpointNotAvailable instanceID endpointDescription
    in callEndpointOnInstance' err s endpointDescription value instanceID

-- | Call an endpoint on a contract instance. If the endpoint is not active, wait until the
--   TMVar is filled, then fail. (if the endpoint becomes active in the meantime it will be
--   called)
callEndpointOnInstanceTimeout :: STM.TMVar () -> InstancesState -> EndpointDescription -> Value -> ContractInstanceId -> STM (Maybe NotificationError)
callEndpointOnInstanceTimeout tmv s endpointDescription value instanceID =
    let err = do
            _ <- STM.takeTMVar tmv
            pure $ Just $ EndpointNotAvailable instanceID endpointDescription
    in callEndpointOnInstance' err s endpointDescription value instanceID

-- | Call an endpoint on a contract instance. The caller can define what to do if the endpoint
--   is not available.
callEndpointOnInstance' ::
    STM (Maybe NotificationError) -- ^ What to do when the endpoint is not available
    -> InstancesState
    -> EndpointDescription
    -> Value
    -> ContractInstanceId
    -> STM (Maybe NotificationError)
callEndpointOnInstance' notAvailable (InstancesState m) endpointDescription value instanceID = do
    instances <- STM.readTVar m
    case Map.lookup instanceID instances of
        Nothing -> pure $ Just $ InstanceDoesNotExist instanceID
        Just is -> do
            mp <- openEndpoints is
            let match OpenEndpoint{oepName=ActiveEndpoint{aeDescription=d}} = endpointDescription == d
            case filter match $ fmap snd $ Map.toList mp of
                []   -> notAvailable
                [ep] -> callEndpoint ep (EndpointValue value) >> pure Nothing
                _    -> pure $ Just $ MoreThanOneEndpointAvailable instanceID endpointDescription

-- | State of all contract instances that are currently running
newtype InstancesState = InstancesState { getInstancesState :: TVar (Map ContractInstanceId InstanceState) }

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
observableContractState :: ContractInstanceId -> InstancesState -> STM Value
observableContractState instanceId m = do
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
        Done r  -> pure r
        Stopped -> pure Nothing
        _       -> empty

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

-- | Wait for the status of a transaction to change.
waitForTxStatusChange :: TxStatus -> TxId -> BlockchainEnv -> STM TxStatus
waitForTxStatusChange oldStatus tx BlockchainEnv{beTxChanges} = do
    idx <- STM.readTVar beTxChanges
    case Map.lookup tx idx of
        Nothing -> empty -- TODO: should be an error?
        Just newStatus -> do
            guard $ oldStatus /= newStatus
            pure newStatus

-- | The value at an address
valueAt :: Address -> BlockchainEnv -> STM Value.Value
valueAt addr BlockchainEnv{beAddressMap} = do
    am <- STM.readTVar beAddressMap
    let utxos = view (AM.fundsAt addr) am
    return $ foldMap (txOutValue . txOutTxOut) utxos

-- | The current slot number
currentSlot :: BlockchainEnv -> STM Slot
currentSlot BlockchainEnv{beCurrentSlot} = STM.readTVar beCurrentSlot

-- | The IDs of contract instances that are currently running
runningInstances :: InstancesState -> STM (Set ContractInstanceId)
runningInstances (InstancesState m) = do
    let flt :: InstanceState -> STM (Maybe InstanceState)
        flt s@InstanceState{issStatus} = do
            status <- STM.readTVar issStatus
            case status of
                Active -> pure (Just s)
                _      -> pure Nothing
    mp <- STM.readTVar m
    Map.keysSet . Map.mapMaybe id <$> traverse flt mp
