{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Protocol.ChainEffect where

import           Control.Concurrent.STM
import           Control.Monad.Freer
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer
import           Control.Monad.IO.Class

import           Ledger                     (Tx (..))
import qualified Wallet.Emulator.Chain      as EC

type ChainEffs = '[State EC.ChainState, Writer [EC.ChainEvent], Reader (TQueue Tx)]

handleControlChain
  :: ( Members ChainEffs effs )
  => Eff (EC.ChainControlEffect ': effs) ~> Eff effs
handleControlChain = interpret $ \case
  EC.ProcessBlock -> EC.handleControlChain EC.processBlock

{- | This effect interprets queuing Txs by *also* sending them
     to a `TQueue`, communicating with the server node. -}
handleChain
    :: ( Members ChainEffs effs
       , LastMember m effs
       , MonadIO m
       )
    => Eff (EC.ChainEffect ': effs) ~> Eff effs
handleChain = interpret $ \case
  EC.QueueTx tx -> do
    ask >>= sendM . liftIO . atomically . flip writeTQueue tx
    EC.handleChain (EC.queueTx tx)
  EC.GetCurrentSlot ->
    EC.handleChain EC.getCurrentSlot
