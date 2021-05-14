{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-

Interface to the 'eventful' and 'eventful-sqlite' libraries used by the PAB

-}
module Plutus.PAB.Db.Eventful(
    -- * Effect handlers
    handleContractDefinitionStore
    , handleContractStore
    -- * Reports
    , runEventfulStoreAction
    ) where

import           Cardano.BM.Trace                               (Trace)
import           Control.Monad.Freer                            (Eff, interpret, runM, subsume)
import           Control.Monad.Freer.Delay                      (DelayEffect, handleDelayEffect)
import           Control.Monad.Freer.Error                      (runError)
import qualified Control.Monad.Freer.Extras.Modify              as Modify
import           Control.Monad.Freer.Reader                     (runReader)
import           Plutus.PAB.Db.Eventful.ContractDefinitionStore (handleContractDefinitionStore)
import           Plutus.PAB.Db.Eventful.ContractStore           (handleContractStore)
import           Plutus.PAB.Effects.Contract                    (ContractDefinitionStore, ContractStore)
import           Plutus.PAB.Effects.Contract.ContractExe        (ContractExe)
import           Plutus.PAB.Effects.EventLog                    (EventLogBackend, handleEventLog)
import           Plutus.PAB.Events                              (PABEvent)
import           Plutus.PAB.Monitoring.MonadLoggerBridge        (MonadLoggerMsg)
import           Plutus.PAB.Types                               (PABError)

-- | Run the ContractStore and ContractDefinitionStore effects on the
--   SQLite database.
runEventfulStoreAction ::
    forall a.
    EventLogBackend (PABEvent ContractExe)
    -> Trace IO MonadLoggerMsg
    -> Eff '[ContractDefinitionStore ContractExe, ContractStore ContractExe, DelayEffect, IO] a
    -> IO (Either PABError a)
runEventfulStoreAction connection trace =
    runM
    . runError
    . runReader connection
    . interpret (handleEventLog @_ @(PABEvent ContractExe) trace)
    . subsume @IO
    . handleDelayEffect
    . interpret handleContractStore
    . interpret handleContractDefinitionStore
    . Modify.raiseEnd
