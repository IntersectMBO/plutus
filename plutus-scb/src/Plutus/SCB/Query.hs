{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Queries are views of the database. Or if you prefer, folds over the event store.
--
-- In 'eventful' they are implemented as 'Projection' types which retain
-- a memory of the last event they saw, such that if you rerun a
-- projection, it will only process new events, rather than
-- recalculating the fold from scratch.
module Plutus.SCB.Query
    ( nullProjection
    , monoidProjection
    , setProjection
    , eventCount
    , latestContractStatus
    , utxoAt
    , utxoIndexProjection,blockCount
    , pureProjection
    ) where

import           Data.Functor.Contravariant              (contramap)
import           Data.Map.Strict                         (Map)
import qualified Data.Map.Strict                         as Map
import           Data.Monoid                             (Sum)
import           Data.Set                                (Set)
import qualified Data.Set                                as Set
import           Data.Text.Prettyprint.Doc               (Pretty, pretty)
import           Data.UUID                               (UUID)
import           Eventful                                (Projection (Projection), StreamEvent (StreamEvent),
                                                          StreamProjection, VersionedStreamEvent,
                                                          projectionEventHandler, projectionMapMaybe, projectionSeed,
                                                          streamProjectionState)
import           Language.Plutus.Contract.Effects.UtxoAt (UtxoAtAddress (UtxoAtAddress), address, utxo)
import           Ledger                                  (Address, Tx, TxId, TxOutTx (TxOutTx), txId, txOutAddress,
                                                          txOutRefId, txOutTxOut, txOutTxTx)
import           Ledger.Index                            (UtxoIndex (UtxoIndex))
import qualified Ledger.Index                            as UtxoIndex
import           Plutus.SCB.Events                       (ChainEvent (NodeEvent, UserEvent), NodeEvent (BlockAdded),
                                                          UserEvent (ContractStateTransition))
import           Plutus.SCB.Types                        (ActiveContractState, activeContract, activeContractId)

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
eventCount :: Projection (Sum Int) (VersionedStreamEvent ChainEvent)
eventCount = contramap (const 1) monoidProjection

-- | Retain the latest status for a given contract.
latestContractStatus ::
       Projection (Map UUID ActiveContractState) (StreamEvent key position ChainEvent)
latestContractStatus = projectionMapMaybe extractState monoidProjection
  where
    extractState (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        let uuid = activeContractId $ activeContract state
         in Just $ Map.singleton uuid state
    extractState _ = Nothing

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

utxoIndexProjection ::
       Projection (Map TxId Tx, UtxoIndex) (StreamEvent key position ChainEvent)
utxoIndexProjection =
    Projection
        { projectionSeed = (Map.empty, UtxoIndex Map.empty)
        , projectionEventHandler
        }
  where
    projectionEventHandler (oldTxById, oldUtxoIndex) (StreamEvent _ _ (NodeEvent (BlockAdded txs))) =
        let newUtxoIndex = UtxoIndex.insertBlock txs oldUtxoIndex
            unprunedTxById =
                foldl (\m tx -> Map.insert (txId tx) tx m) oldTxById txs
            newTxById = id unprunedTxById -- TODO Prune spent keys.
         in (newTxById, newUtxoIndex)
    projectionEventHandler m _ = m

blockCount :: Projection (Sum Integer) (StreamEvent key position ChainEvent)
blockCount = contramap (const 1) monoidProjection
