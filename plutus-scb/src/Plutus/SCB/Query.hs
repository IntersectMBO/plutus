{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
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
    , eventCount
    , balances
    , trialBalance
    , requestStats
    , RequestStats
    ) where

import           Control.Lens                    (makeLenses, over)
import           Control.Monad                   ((>=>))
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Maybe                      (fromMaybe)
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Eventful                        (Projection (Projection), StreamEvent (StreamEvent), StreamProjection,
                                                  VersionedStreamEvent, projectionEventHandler, projectionSeed,
                                                  streamProjectionState)
import           Ledger.Ada                      (lovelaceValueOf)
import           Ledger.Value                    (Value)
import           Options.Applicative.Help.Pretty (Pretty, indent, int, pretty, vsep, (<+>))
import           Plutus.SCB.Events               (AccountId, ChainEvent (..), Entry (Entry), EventId,
                                                  RequestEvent (CancelRequest, IssueRequest),
                                                  ResponseEvent (ResponseEvent), accountId, amount)

-- | The empty projection. Particularly useful for commands that have no 'state'.
nullProjection :: Projection () event
nullProjection =
    Projection {projectionSeed = (), projectionEventHandler = const}

-- | A simple counter of all the events. This is the simplest 'Projection' that does any work.
eventCount :: Projection Int (VersionedStreamEvent ChainEvent)
eventCount = Projection {projectionSeed = 0, projectionEventHandler}
  where
    projectionEventHandler count _ = count + 1

-- | Fold over each entry and store the total amounts seen, indexed by
-- 'AccountId'. This will give us a final balance of all the mock entries.
balances :: Projection (Map AccountId Value) (VersionedStreamEvent ChainEvent)
balances = Projection {projectionSeed = mempty, projectionEventHandler}
  where
    projectionEventHandler acc (StreamEvent _ _ (RecordEntry Entry { accountId
                                                                   , amount
                                                                   })) =
        Map.alter updater accountId acc
      where
        updater :: Maybe Value -> Maybe Value
        updater current = Just $ amount <> fromMaybe (lovelaceValueOf 0) current
    projectionEventHandler acc _ = acc

-- | The trial balance adds up all 'Entry' types in the database. If
-- we've done our double-entry accounting correctly, this should
-- always be zero (because every entry has an equal and opposite entry
-- somewhere else).
trialBalance :: Projection Value (VersionedStreamEvent ChainEvent)
trialBalance = Projection {projectionSeed = mempty, projectionEventHandler}
  where
    projectionEventHandler total (StreamEvent _ _ (RecordEntry Entry {amount})) =
        total <> amount
    projectionEventHandler total _ = total

------------------------------------------------------------

data RequestStats =
    RequestStats
        { _made      :: Int
        , _cancelled :: Int
        , _responded :: Int
        , _openIds   :: Set EventId
        }
    deriving (Show, Eq)

makeLenses ''RequestStats

-- | Query out some interesting statistics about the Contract events we've seen.
--
-- Implementation detail: Noteworthy here is the use of the @(->)@
-- monad so that we can easily compose projection handlers with '>=>'.
requestStats :: Projection RequestStats (VersionedStreamEvent ChainEvent)
requestStats =
    Projection
        { projectionSeed = RequestStats 0 0 0 Set.empty
        , projectionEventHandler = trackEventIds >=> countMessageTypes
        }

-- | Tickers for each kind of message.
countMessageTypes ::
       RequestStats -> VersionedStreamEvent ChainEvent -> RequestStats
countMessageTypes stats (StreamEvent _ _ event) =
    case event of
        RecordRequest (IssueRequest _ _)   -> over made (+ 1) stats
        RecordRequest (CancelRequest _)    -> over cancelled (+ 1) stats
        RecordResponse (ResponseEvent _ _) -> over responded (+ 1) stats
        _                                  -> stats

-- | When we see a request, track its 'EventId'. When it is canceled
-- or responded to, remove it.
  --
-- We'll be left with a list of unanswered (open) requests.
trackEventIds :: RequestStats -> VersionedStreamEvent ChainEvent -> RequestStats
trackEventIds stats (StreamEvent _ _ event) =
    case event of
        RecordRequest (IssueRequest eventId _) ->
            over openIds (Set.insert eventId) stats
        RecordRequest (CancelRequest eventId) ->
            over openIds (Set.delete eventId) stats
        RecordResponse (ResponseEvent eventId _) ->
            over openIds (Set.delete eventId) stats
        _ -> stats

instance Pretty RequestStats where
    pretty RequestStats {_made, _cancelled, _responded, _openIds} =
        vsep
            [ "Request Stats:"
            , indent 2 $
              vsep
                  [ "Made:" <+> int _made
                  , "Cancelled:" <+> int _cancelled
                  , "Responded:" <+> int _responded
                  , "Open:" <+> int (Set.size _openIds)
                  ]
            ]

-- | The Pretty instance for 'StreamProjection' just pretty prints its resulting 'state'.
instance Pretty state =>
         Pretty (StreamProjection key position state event) where
    pretty = pretty . streamProjectionState
