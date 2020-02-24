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
    ) where

import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc (Pretty, pretty)
import           Data.UUID                 (UUID)
import           Eventful                  (Projection (Projection), StreamEvent (StreamEvent), StreamProjection,
                                            VersionedStreamEvent, projectionEventHandler, projectionSeed,
                                            streamProjectionState)
import           Plutus.SCB.Events         (ChainEvent (UserEvent), UserEvent (ContractStateTransition))
import           Plutus.SCB.Types          (ActiveContractState, activeContract, activeContractId)

-- | The empty projection. Particularly useful for commands that have no 'state'.
nullProjection :: Projection () event
nullProjection =
    Projection {projectionSeed = (), projectionEventHandler = const}

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
setProjection =
    Projection
        { projectionSeed = Set.empty
        , projectionEventHandler = \state event -> Set.insert event state
        }

-- | A simple counter of all the events. This is the simplest 'Projection' that does any work.
eventCount :: Projection Int (VersionedStreamEvent ChainEvent)
eventCount = Projection {projectionSeed = 0, projectionEventHandler}
  where
    projectionEventHandler count _ = count + 1

-- | Retain the latest status for a given contract.
latestContractStatus ::
       Projection (Map UUID ActiveContractState) (StreamEvent key position ChainEvent)
latestContractStatus =
    Projection {projectionSeed = Map.empty, projectionEventHandler}
  where
    projectionEventHandler m (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        let uuid = activeContractId $ activeContract state
         in Map.insert uuid state m
    projectionEventHandler m _ = m

------------------------------------------------------------
-- | The Pretty instance for 'StreamProjection' just pretty prints its resulting 'state'.
instance Pretty state =>
         Pretty (StreamProjection key position state event) where
    pretty = pretty . streamProjectionState
