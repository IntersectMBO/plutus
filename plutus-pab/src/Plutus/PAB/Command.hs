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
    , saveBalancedTxResult
    -- * Commands related to updating the contract state
    , updateContractInstanceState
    ) where

import           Eventful                                (Aggregate (Aggregate), aggregateCommandHandler,
                                                          aggregateProjection)
import qualified Ledger
import           Plutus.PAB.Events                       (PABEvent (InstallContract, SubmitTx, UpdateContractInstanceState))
import qualified Plutus.PAB.Events                       as Events
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Plutus.PAB.Query                        (nullProjection)
import           Wallet.Types                            (ContractInstanceId)

-- | An aggregate that just sends a list of events with no state
sendEvents ::
  forall a t.
  (a -> [PABEvent t])
  -> Aggregate () (PABEvent t) a
sendEvents f =
  Aggregate
    { aggregateProjection = nullProjection
    , aggregateCommandHandler =
        \() a -> f a
    }

installCommand :: Aggregate () (PABEvent t) t
installCommand = sendEvents (return . InstallContract)

saveBalancedTxResult :: forall t. Aggregate () (PABEvent t) Ledger.Tx
saveBalancedTxResult = sendEvents (return . SubmitTx)

updateContractInstanceState :: forall t. Aggregate () (PABEvent t) (t, ContractInstanceId, (PartiallyDecodedResponse ContractPABRequest))
updateContractInstanceState = sendEvents (\(x, y, z) -> return $ UpdateContractInstanceState x y z)
