{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}
module Plutus.ChainIndex(
    runChainIndexEffects
    , RunRequirements(..)
    , module Export
    ) where

import           Control.Monad.Freer.Extras.Pagination as Export
import           Plutus.ChainIndex.ChainIndexError     as Export
import           Plutus.ChainIndex.ChainIndexLog       as Export
import           Plutus.ChainIndex.Effects             as Export
import           Plutus.ChainIndex.Handlers            as Export
import           Plutus.ChainIndex.Tx                  as Export
import           Plutus.ChainIndex.TxIdState           as Export hiding (fromBlock, fromTx, rollback)
import           Plutus.ChainIndex.TxOutBalance        as Export hiding (fromBlock, fromTx, isSpentOutput,
                                                                  isUnspentOutput, rollback)
import           Plutus.ChainIndex.Types               as Export
import           Plutus.ChainIndex.UtxoState           as Export

import           Cardano.BM.Trace                      (Trace)
import           Control.Concurrent.STM                (TVar)
import qualified Control.Concurrent.STM                as STM
import           Control.Lens                          (unto)
import           Control.Monad.Freer                   (Eff, interpret, reinterpret, runM)
import           Control.Monad.Freer.Error             (handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Beam       (BeamEffect, handleBeam)
import           Control.Monad.Freer.Extras.Log        (LogMessage (..), handleLogWriter)
import           Control.Monad.Freer.Extras.Modify     (raiseEnd)
import           Control.Monad.Freer.Reader            (runReader)
import           Control.Monad.Freer.State             (runState)
import           Control.Monad.Freer.Writer            (runWriter)
import           Data.Sequence                         (Seq)
import qualified Database.SQLite.Simple                as Sqlite
import           Plutus.Monitoring.Util                (convertLog)

-- | The required arguments to run the chain-index effects.
data RunRequirements = RunRequirements
    { trace         :: Trace IO ChainIndexLog
    , stateTVar     :: TVar ChainIndexState
    , conn          :: Sqlite.Connection
    , securityParam :: Int
    }

-- | Run the chain-index effects.
runChainIndexEffects
    :: RunRequirements
    -> Eff '[ChainIndexQueryEffect, ChainIndexControlEffect, BeamEffect] a
    -> IO (Either ChainIndexError a, Seq (LogMessage ChainIndexLog))
runChainIndexEffects RunRequirements{trace, stateTVar, conn, securityParam} action = do
    state <- STM.readTVarIO stateTVar
    ((result, newState), logs) <- runM
        $ runWriter @(Seq (LogMessage ChainIndexLog))
        $ reinterpret
            (handleLogWriter @ChainIndexLog
                             @(Seq (LogMessage ChainIndexLog)) $ unto pure)
        $ runState state
        $ runReader conn
        $ runReader (Depth securityParam)
        $ runError @ChainIndexError
        $ flip handleError (throwError . BeamEffectError)
        $ interpret (handleBeam (convertLog BeamLogItem trace))
        $ interpret handleControl
        $ interpret handleQuery
        $ raiseEnd action
    STM.atomically $ STM.writeTVar stateTVar newState
    pure (result, logs)
