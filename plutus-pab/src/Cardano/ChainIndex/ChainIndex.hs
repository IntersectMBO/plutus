{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Cardano.ChainIndex.ChainIndex
    ( processChainIndexEffects
    , syncState
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import           Control.Concurrent.STM           (TVar)
import qualified Control.Concurrent.STM           as STM
import           Control.Monad.Freer
import           Control.Monad.Freer.Error        (runError)
import qualified Control.Monad.Freer.State        as Eff
import           Control.Monad.IO.Class           (MonadIO (..))
import           Ledger.Blockchain                (Block)
import           Ledger.Slot                      (Slot)

import           Cardano.ChainIndex.Types
import           Plutus.ChainIndex                (ChainIndexEmulatorState, ChainIndexLog)
import qualified Plutus.ChainIndex                as ChainIndex
import           Plutus.PAB.Monitoring.Monitoring (convertLog, handleLogMsgTrace)
import           Plutus.Trace.Emulator.System     (appendNewTipBlock)

-- | Update the chain index by asking the node for new blocks since the last
--   time.
syncState ::
    ( Member ChainIndex.ChainIndexControlEffect effs
    , Member ChainIndex.ChainIndexQueryEffect effs
    )
    => Block
    -> Slot
    -> Eff effs ()
syncState block slot = do
    currentTip <- ChainIndex.getTip
    appendNewTipBlock currentTip block slot

-- | Process the chain index effects for the emulator.
processChainIndexEffects ::
    MonadIO m
    => ChainIndexTrace
    -> TVar ChainIndexEmulatorState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processChainIndexEffects trace stateVar eff = do
  emState <- liftIO $ STM.atomically $ STM.readTVar stateVar
  resultE <- liftIO $
        runM
        $ runError
        $ interpret (handleLogMsgTrace (toChainIndexServerMsg trace))
        $ Eff.runState emState
        $ interpret ChainIndex.handleQuery
        $ interpret ChainIndex.handleControl eff
  case resultE of
    Left e -> error (show e)
    Right (result, newEmState) -> do
      liftIO $ STM.atomically $ STM.writeTVar stateVar newEmState
      pure result
  where
      toChainIndexServerMsg :: Trace m ChainIndexServerMsg -> Trace m ChainIndexLog
      toChainIndexServerMsg = convertLog ChainEvent
