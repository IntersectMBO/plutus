{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Cardano.ChainIndex.ChainIndex
    ( processIndexEffects
    , startWatching
    , watchedAddresses
    , confirmedBlocks
    , syncState
    , healthcheck
    ) where

import           Cardano.BM.Data.Trace            (Trace)
import           Control.Concurrent.MVar          (MVar, putMVar, takeMVar)
import           Control.Monad.Freer              hiding (run)
import qualified Control.Monad.Freer.State        as Eff
import           Control.Monad.IO.Class           (MonadIO (..))
import           Data.Foldable                    (traverse_)
import           Data.Function                    ((&))
import           Ledger.Blockchain                (Block)
import           Ledger.Slot                      (Slot)
import           Servant                          (NoContent (NoContent))

import           Cardano.ChainIndex.Types
import           Ledger.Address                   (Address)
import           Ledger.AddressMap                (AddressMap)
import           Plutus.PAB.Monitoring.Monitoring (convertLog, handleLogMsgTrace)
import           Wallet.Effects                   (ChainIndexEffect)
import qualified Wallet.Effects                   as WalletEffects
import           Wallet.Emulator.ChainIndex       (ChainIndexControlEffect, ChainIndexEvent)
import qualified Wallet.Emulator.ChainIndex       as ChainIndex
import           Wallet.Emulator.NodeClient       (ChainClientNotification (BlockValidated, SlotChanged))

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

startWatching :: (Member ChainIndexEffect effs) => Address -> Eff effs NoContent
startWatching addr = WalletEffects.startWatching addr >> pure NoContent

watchedAddresses :: (Member ChainIndexEffect effs) => Eff effs AddressMap
watchedAddresses = WalletEffects.watchedAddresses

confirmedBlocks :: (Member ChainIndexEffect effs) => Eff effs [Block]
confirmedBlocks = WalletEffects.confirmedBlocks

-- | Update the chain index by asking the node for new blocks since the last
--   time.
syncState ::
    ( Member ChainIndexControlEffect effs)
    => Block
    -> Slot
    -> Eff effs ()
syncState block slot =
    traverse_ ChainIndex.chainIndexNotify [BlockValidated block, SlotChanged slot]

processIndexEffects ::
    MonadIO m
    => ChainIndexTrace
    -> MVar AppState
    -> Eff (ChainIndexEffects IO) a
    -> m a
processIndexEffects trace stateVar eff = do
    AppState {_indexState, _indexEvents} <- liftIO $ takeMVar stateVar
    (result, newState) <- liftIO
        $ ChainIndex.handleChainIndexControl eff
        & ChainIndex.handleChainIndex
        & Eff.runState _indexState
        & handleLogMsgTrace (toChainIndexServerMsg trace)
        & runM
    liftIO $ putMVar stateVar AppState{_indexState=newState, _indexEvents=_indexEvents}
    pure result
        where
            toChainIndexServerMsg :: Trace m ChainIndexServerMsg -> Trace m ChainIndexEvent
            toChainIndexServerMsg = convertLog ChainEvent
