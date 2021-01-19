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
module Plutus.PAB.Command
    ( installCommand
    , saveBalancedTx
    , saveBalancedTxResult
    -- * Commands related to updating the contract state
    , sendContractEvent
    ) where

import           Eventful                   (Aggregate (Aggregate), aggregateCommandHandler, aggregateProjection)
import qualified Ledger
import           Plutus.PAB.Events          (ChainEvent (ContractEvent, UserEvent), UserEvent (InstallContract))
import qualified Plutus.PAB.Events          as Events
import           Plutus.PAB.Query           (nullProjection)

import qualified Plutus.PAB.Events.Contract as Events.Contract

-- | An aggregate that just sends a list of events with no state
sendEvents ::
  forall a t.
  (a -> [ChainEvent t])
  -> Aggregate () (ChainEvent t) a
sendEvents f =
  Aggregate
    { aggregateProjection = nullProjection
    , aggregateCommandHandler =
        \() a -> f a
    }

installCommand :: Aggregate () (ChainEvent t) t
installCommand = sendEvents (return . UserEvent . InstallContract)

saveBalancedTx :: forall t. Aggregate () (ChainEvent t) Ledger.Tx
saveBalancedTx = sendEvents (return . Events.WalletEvent . Events.BalancedTx)

saveBalancedTxResult :: forall t. Aggregate () (ChainEvent t) Ledger.Tx
saveBalancedTxResult = sendEvents (return . Events.NodeEvent . Events.SubmittedTx)

sendContractEvent :: forall t. Aggregate () (ChainEvent t) (Events.Contract.ContractEvent t)
sendContractEvent = sendEvents (return . ContractEvent)
