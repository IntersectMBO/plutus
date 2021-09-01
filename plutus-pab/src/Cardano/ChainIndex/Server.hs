{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Cardano.ChainIndex.Server(
    -- $chainIndex
    main
    , ChainIndexConfig(..)
    , ChainIndexServerMsg
    ) where

import           Control.Concurrent.STM              (TVar)
import qualified Control.Concurrent.STM              as STM
import           Control.Monad.Freer.Extras.Log
import           Servant.Client                      (BaseUrl (baseUrlPort))

import           Data.Coerce                         (coerce)
import           Plutus.PAB.Monitoring.Util          (runLogEffects)

import           Cardano.ChainIndex.ChainIndex       (processChainIndexEffects, syncState)
import           Control.Monad.IO.Class              (MonadIO (..))
import           Ledger.Blockchain                   (Block)
import           Ledger.TimeSlot                     (SlotConfig)

import           Cardano.ChainIndex.Types
import           Cardano.Protocol.Socket.Mock.Client (runChainSync)
import           Ledger.Slot                         (Slot (..))
import           Plutus.ChainIndex                   (ChainIndexEmulatorState)
import           Plutus.ChainIndex.Server            (serveChainIndexQueryServer)

-- $chainIndex
-- The PAB chain index that keeps track of transaction data (UTXO set enriched
-- with datums)

main :: ChainIndexTrace -> ChainIndexConfig -> FilePath -> SlotConfig -> IO ()
main trace ChainIndexConfig{ciBaseUrl} socketPath slotConfig = runLogEffects trace $ do
    tVarState <- liftIO $ STM.atomically $ STM.newTVar mempty

    logInfo StartingNodeClientThread
    _ <- liftIO $ runChainSync socketPath slotConfig $ updateChainState tVarState

    logInfo $ StartingChainIndex servicePort
    liftIO $ serveChainIndexQueryServer servicePort tVarState
    where
        servicePort = baseUrlPort (coerce ciBaseUrl)
        updateChainState :: TVar ChainIndexEmulatorState -> Block -> Slot -> IO ()
        updateChainState tv block slot = do
          processChainIndexEffects trace tv $ syncState block slot
