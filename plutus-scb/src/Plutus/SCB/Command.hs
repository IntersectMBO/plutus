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
    ( installCommand
    , saveBalancedTx
    , saveBalancedTxResult
    , saveContractState
    ) where

import           Eventful          (Aggregate (Aggregate), aggregateCommandHandler, aggregateProjection)
import qualified Ledger
import           Plutus.SCB.Events (ChainEvent (UserEvent), UserEvent (ContractStateTransition, InstallContract))
import qualified Plutus.SCB.Events as Events
import           Plutus.SCB.Query  (nullProjection)
import           Plutus.SCB.Types  (ActiveContractState, Contract)

installCommand :: Aggregate () ChainEvent Contract
installCommand =
    Aggregate
        { aggregateProjection = nullProjection
        , aggregateCommandHandler =
              \() contract -> [UserEvent $ InstallContract contract]
        }

saveBalancedTx :: Aggregate () ChainEvent Ledger.Tx
saveBalancedTx = Aggregate {aggregateProjection, aggregateCommandHandler}
  where
    aggregateProjection = nullProjection
    aggregateCommandHandler _ txn = [Events.WalletEvent $ Events.BalancedTx txn]

saveBalancedTxResult :: Aggregate () ChainEvent Ledger.Tx
saveBalancedTxResult = Aggregate {aggregateProjection, aggregateCommandHandler}
  where
    aggregateProjection = nullProjection
    aggregateCommandHandler _ tx =
        [Events.NodeEvent $ Events.SubmittedTx tx]

saveContractState :: Aggregate () ChainEvent ActiveContractState
saveContractState =
    Aggregate {aggregateProjection = nullProjection, aggregateCommandHandler}
  where
    aggregateCommandHandler _ state =
        [UserEvent $ ContractStateTransition state]
