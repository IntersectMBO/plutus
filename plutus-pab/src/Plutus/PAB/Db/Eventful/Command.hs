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
module Plutus.PAB.Db.Eventful.Command
    ( installCommand
    , saveBalancedTxResult
    -- * Commands related to updating the contract state
    , updateContractInstanceState
    , startContractInstance
    , stopContractInstance
    ) where

import           Data.Aeson                   (Value)
import           Eventful                     (Aggregate (Aggregate), aggregateCommandHandler, aggregateProjection)
import qualified Ledger
import           Plutus.Contract.Effects      (PABReq)
import           Plutus.Contract.State        (ContractResponse)
import           Plutus.PAB.Db.Eventful.Query (nullProjection)
import           Plutus.PAB.Events            (PABEvent (..))
import           Plutus.PAB.Webserver.Types   (ContractActivationArgs)
import           Wallet.Types                 (ContractInstanceId)

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

updateContractInstanceState :: forall t. Aggregate () (PABEvent t) (ContractActivationArgs t, ContractInstanceId, (ContractResponse Value Value Value PABReq))
updateContractInstanceState = sendEvents (\(x, y, z) -> return $ UpdateContractInstanceState x y z)

startContractInstance :: forall t. Aggregate () (PABEvent t) (ContractActivationArgs t, ContractInstanceId)
startContractInstance = sendEvents (\(x, y) -> return $ ActivateContract x y)

stopContractInstance :: forall t. Aggregate () (PABEvent t) ContractInstanceId
stopContractInstance = sendEvents (return . StopContract)
