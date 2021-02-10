{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Queries are views of the database. Or if you prefer, folds over the event store.
--
-- In 'eventful' they are implemented as 'Projection' types which retain
-- a memory of the last event they saw, such that if you rerun a
-- projection, it will only process new events, rather than
-- recalculating the fold from scratch.
module Plutus.PAB.Query
    ( nullProjection
    , monoidProjection
    , setProjection
    , eventCount
    , utxoAt
    , blockCount
    , pureProjection
    -- * Queries related to the installed and active contracts
    , activeContractHistoryProjection
    , activeContractsProjection
    , txHistoryProjection
    , installedContractsProjection
    -- * Queries related to contract instances
    , contractStates
    , contractState
    , ContractIterationState(..)
    , contractIteration
    , IteratedContractState(..)
    , inboxMessages
    ) where

import           Control.Lens
import           Data.Map.Strict                         (Map)
import qualified Data.Map.Strict                         as Map
import           Data.Monoid                             (Sum)
import           Data.Semigroup                          (Last (..), Max (..))
import           Data.Set                                (Set)
import qualified Data.Set                                as Set
import           Data.Text.Prettyprint.Doc               (Pretty, pretty)
import           Eventful                                (Projection (Projection), StreamEvent (StreamEvent),
                                                          StreamProjection, VersionedStreamEvent,
                                                          projectionEventHandler, projectionMapMaybe, projectionSeed,
                                                          streamProjectionState)
import           Language.Plutus.Contract.Effects.UtxoAt (UtxoAtAddress (UtxoAtAddress), address, utxo)
import           Language.Plutus.Contract.Resumable      (Response)
import           Ledger                                  (Address, Tx, TxId, TxOutTx (TxOutTx), txOutAddress,
                                                          txOutRefId, txOutTxOut, txOutTxTx)
import           Ledger.Index                            (UtxoIndex (UtxoIndex))
import           Plutus.PAB.Events                       (ChainEvent (..), NodeEvent (SubmittedTx),
                                                          UserEvent (InstallContract), hasActiveRequests)
import           Plutus.PAB.Events.Contract              (ContractEvent (..), ContractInstanceId,
                                                          ContractInstanceState (..), ContractResponse (..),
                                                          IterationID)

-- | The empty projection. Particularly useful for commands that have no 'state'.
nullProjection :: Projection () event
nullProjection = contramap (const ()) monoidProjection

-- | This projection just collects all events it sees into some applicative.
pureProjection :: (Monoid (f e), Applicative f) => Projection (f e) e
pureProjection = contramap pure monoidProjection

-- | A projection that just accumulates any monoid you supply.
-- This is particulatly useful when combined with function that filters down interesting events using 'projectionMapMaybe':
--
-- @
-- allNames :: Projection [Text] Event
-- allNames = projectionMapMaybe extractName monoidProjection
--   where
--     extractName (CreateUser name dateOfBirth) = Just [name]
--     extractName (ChristenShip name tonnage)   = Just [name]
--     extractName _                             = Nothing
-- @
monoidProjection :: Monoid m => Projection m m
monoidProjection =
    Projection {projectionSeed = mempty, projectionEventHandler = mappend}

-- | Similar to 'monoidProjection', but for accumulating sets instead of monoids.
setProjection :: Ord a => Projection (Set a) a
setProjection = contramap Set.singleton monoidProjection

-- | A simple counter of all the events. This is the simplest 'Projection' that does any work.
eventCount :: Projection (Sum Int) (VersionedStreamEvent (ChainEvent t))
eventCount = contramap (const 1) monoidProjection

------------------------------------------------------------
-- | The Pretty instance for 'StreamProjection' just pretty prints its resulting 'state'.
instance Pretty state =>
         Pretty (StreamProjection key position state event) where
    pretty = pretty . streamProjectionState

utxoAt :: (Map TxId Tx, UtxoIndex) -> Address -> UtxoAtAddress
utxoAt (txById, UtxoIndex utxoIndex) address =
    let utxo =
            Map.foldMapWithKey
                (\txOutRef txOut ->
                     case Map.lookup (txOutRefId txOutRef) txById of
                         Nothing -> Map.empty
                         Just tx ->
                             if txOutAddress txOut == address
                                 then Map.singleton
                                          txOutRef
                                          (TxOutTx
                                               { txOutTxTx = tx
                                               , txOutTxOut = txOut
                                               })
                                 else Map.empty)
                utxoIndex
     in UtxoAtAddress {address, utxo}


blockCount :: forall t key position. Projection (Sum Integer) (StreamEvent key position (ChainEvent t))
blockCount = contramap (const 1) monoidProjection

-- | The last known state of the contract.
contractState :: forall t key position. Projection (Map ContractInstanceId (ContractInstanceState t)) (StreamEvent key position (ChainEvent t))
contractState =
    let projectionEventHandler oldMap = \case
            (StreamEvent _ _ (ContractEvent (ContractInstanceStateUpdateEvent s))) ->
                Map.union (Map.singleton (csContract s) s) oldMap
            _ -> oldMap

    in Projection
        { projectionSeed = Map.empty
        , projectionEventHandler
        }

-- | Records the last known iteration of a contract. This allows us to discard
--   events from older iterations.
newtype ContractIterationState =
    ContractIterationState
        { unContractIterationState :: Map ContractInstanceId (Max IterationID)
        }

instance Semigroup ContractIterationState where
    ContractIterationState l <> ContractIterationState r =
        ContractIterationState (Map.unionWith (<>) l r)

instance Monoid ContractIterationState where
    mappend = (<>)
    mempty = ContractIterationState mempty

updateContractIterationState :: ContractInstanceState t -> ContractIterationState -> ContractIterationState
updateContractIterationState ContractInstanceState{csContract,csCurrentIteration} ContractIterationState{unContractIterationState} =
    ContractIterationState (Map.insertWith (<>) csContract (Max csCurrentIteration) unContractIterationState)

-- | The last known iteration of the contract. Requests from iterations lower
--   than this can be ignored.
contractIteration :: forall t key position. Projection ContractIterationState (StreamEvent key position (ChainEvent t))
contractIteration =
    let projectionEventHandler oldState = \case
            (StreamEvent _ _ (ContractEvent (ContractInstanceStateUpdateEvent e))) -> updateContractIterationState e oldState
            _ -> oldState

    in Projection
        { projectionSeed = mempty
        , projectionEventHandler
        }

-- | Holds instance-specific values of 'a' that are indexed by iteration.
--   See note [Contract Iterations] in Plutus.PAB.Events.Contract.
data IteratedContractState a =
    IteratedContractState
        { icsContractIterations :: ContractIterationState
        , icsContractState      :: Map ContractInstanceId a
        }

-- | Get the values of the contract instances at their latest
--   iteration
contractStates ::
    IteratedContractState a
    -> Map ContractInstanceId (IterationID, a)
contractStates IteratedContractState{icsContractIterations=ContractIterationState its, icsContractState} =
    Map.mapMaybeWithKey (\k (Max i) -> fmap (i,) (Map.lookup k icsContractState)) its

-- Queries about active contracts

-- | IDs of active contracts by contract type
activeContractsProjection ::
       forall t key position. Ord t
    => Projection (Map t (Set ContractInstanceId)) (StreamEvent key position (ChainEvent t))
activeContractsProjection =
    let projectionEventHandler m = \case
            (StreamEvent _ _ (ContractEvent (ContractInstanceStateUpdateEvent state))) ->
                let key = csContractDefinition state
                 in if hasActiveRequests state
                        then Map.insertWith (<>) key (Set.singleton (csContract state)) m
                        else Map.delete key m
            _ -> m
     in Projection {projectionSeed = Map.empty, projectionEventHandler}

-- | Transactions submitted to the node.
txHistoryProjection ::
    forall t key position.
       Projection [Ledger.Tx] (StreamEvent key position (ChainEvent t))
txHistoryProjection = projectionMapMaybe submittedTxs monoidProjection
  where
    submittedTxs (StreamEvent _ _ (NodeEvent (SubmittedTx tx))) = Just [tx]
    submittedTxs _                                              = Nothing

-- | Past states of the contract instance.
activeContractHistoryProjection ::
    forall t key position.
    ContractInstanceId
    -> Projection [ContractInstanceState t] (StreamEvent key position (ChainEvent t))
activeContractHistoryProjection cid =
    projectionMapMaybe contractPaths monoidProjection
    where
    contractPaths (StreamEvent _ _ (ContractEvent (ContractInstanceStateUpdateEvent state))) =
        if csContract state == cid
            then Just [state]
            else Nothing
    contractPaths _ = Nothing

-- | Set of all contracts that have been installed.
installedContractsProjection ::
    forall t key position.
    Ord t => Projection (Set t) (StreamEvent key position (ChainEvent t))
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing

-- | Responses sent to the contract
inboxMessages ::
    forall t key position.
    Projection (Map ContractInstanceId (Last (Response ContractResponse))) (StreamEvent key position (ChainEvent t))
inboxMessages =
    let projectionEventHandler oldMap = \case
            (StreamEvent _ _ (ContractEvent (ContractInboxMessage i s))) ->
                Map.unionWith (<>) oldMap (Map.singleton i (Last s))
            _ -> oldMap

    in Projection
        { projectionSeed = Map.empty
        , projectionEventHandler
        }
