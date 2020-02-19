{-# LANGUAGE NamedFieldPuns #-}

-- | Commands, in CQRS parlance, are inbound message which will
-- will be processed into events to put in the event store.
--
-- Commands in 'eventful' are handled by a function:
--
-- > state -> command -> [event]
--
-- What's the 'state'? A projection, which allows us keep the
-- up-to-date results of any query over the event database.
--
-- These two things are bundled up in an 'Aggregate'. So for example,
-- you might have an aggregate whose state was, "the details of all
-- open orders" and a command, "Order 123 was dispatched," yielding
-- the two events, @OrderDispatched 123@ and @NotificationSent
-- "steve\@iohk.com"@.
--
-- Of note in this module is the use of 'nullProjection' as a way of
-- ignoring the 'state'.
module Plutus.SCB.Command
    ( saveTxAggregate
    , saveRequestResponseAggregate
    ) where

import           Data.Maybe        (catMaybes)
import           Eventful          (Aggregate (Aggregate), aggregateCommandHandler, aggregateProjection)
import           Plutus.SCB.Events (ChainEvent (..), ContractRequest, ContractResponse, RequestEvent, ResponseEvent,
                                    Tx (Tx), entries)
import           Plutus.SCB.Query  (nullProjection)

-- | Turns a mock transaction into two mock entries.
--
-- Like all the mock code, this is here to exercise the framework
-- while we wait for real events, so the question, "Should 'Tx' be a
-- single event?" is moot.
saveTxAggregate :: Aggregate () ChainEvent Tx
saveTxAggregate =
    Aggregate
        { aggregateProjection = nullProjection
        , aggregateCommandHandler = \() Tx {entries} -> RecordEntry <$> entries
        }

-- | Stores a request, and its possible response and/or cancellation,
-- as the appropriate set of events.
saveRequestResponseAggregate ::
       Aggregate () ChainEvent ( RequestEvent ContractRequest
                               , Maybe (RequestEvent ContractRequest)
                               , Maybe (ResponseEvent ContractResponse))
saveRequestResponseAggregate =
    Aggregate {aggregateProjection = nullProjection, aggregateCommandHandler}
  where
    aggregateCommandHandler _ (request, mCancellation, mResponse) =
        catMaybes
            [ Just $ RecordRequest request
            , RecordRequest <$> mCancellation
            , RecordResponse <$> mResponse
            ]
