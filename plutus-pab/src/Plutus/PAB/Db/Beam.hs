{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-

Interface to beam ecosystem used by the PAB to store contracts.

-}
module Plutus.PAB.Db.Beam
  where

import           Cardano.BM.Trace                           (Trace)
import           Control.Monad.Freer                        (Eff, interpret, runM, subsume)
import           Control.Monad.Freer.Delay                  (DelayEffect, handleDelayEffect)
import           Control.Monad.Freer.Error                  (runError)
import qualified Control.Monad.Freer.Extras.Modify          as Modify
import           Control.Monad.Freer.Reader                 (runReader)
import           Database.SQLite.Simple                     (Connection)
import           Plutus.PAB.Db.Beam.ContractDefinitionStore (handleContractDefinitionStore)
import           Plutus.PAB.Db.Beam.ContractStore           (handleContractStore)
import           Plutus.PAB.Effects.Contract                (ContractDefinitionStore, ContractStore)
import           Plutus.PAB.Effects.Contract.ContractExe    (ContractExe)
import           Plutus.PAB.Effects.DbStore
import           Plutus.PAB.Monitoring.MonadLoggerBridge    (MonadLoggerMsg)
import           Plutus.PAB.Types                           (PABError)

-- | Run the ContractStore and ContractDefinitionStore effects on the
--   SQLite database.
runBeamStoreAction ::
    forall a.
    Connection
    -> Trace IO MonadLoggerMsg
    -> Eff '[ContractDefinitionStore ContractExe, ContractStore ContractExe, DelayEffect, IO] a
    -> IO (Either PABError a)
runBeamStoreAction connection trace =
    runM
    . runError
    . runReader connection
    . interpret (handleDbStore trace)
    . subsume @IO
    . handleDelayEffect
    . interpret handleContractStore
    . interpret handleContractDefinitionStore
    . Modify.raiseEnd
