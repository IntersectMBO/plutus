{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Protocol.ChainEffect where

import           Control.Monad.Freer
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer
import           Control.Monad.IO.Class

import qualified Cardano.Protocol.Socket.Client as Client
import qualified Cardano.Protocol.Socket.Server as Server
import qualified Wallet.Emulator.Chain          as EC

type ChainEffs = '[ State EC.ChainState
                  , Writer [EC.ChainEvent]
                  , Reader Server.ServerHandler
                  , Reader Client.ClientHandler
                  ]

handleControlChain ::
    ( Members ChainEffs effs
    , LastMember m effs
    , MonadIO m )
 => Eff (EC.ChainControlEffect ': effs) ~> Eff effs
handleControlChain = interpret $ \case
    -- Send the command to process a block to the server. This will
    -- block until the command has been executed.
    EC.ProcessBlock -> do
        serverHandler  <- ask
        serverResponse <- liftIO $ Server.processBlock serverHandler
        case serverResponse of
            Right block -> pure block
            -- TODO: Add a logging effect to catch communication errors.
            response    ->
                error $ "Unexpected response from server: " <> show response

{- | This effect interprets queuing Txs by *also* sending them
     to a `TQueue`, communicating with the server node. -}
handleChain ::
    ( Members ChainEffs effs
    , LastMember m effs
    , MonadIO m
    )
 => Eff (EC.ChainEffect ': effs) ~> Eff effs
handleChain = interpret $ \case
  EC.QueueTx tx -> do
    clientHandler <- ask
    liftIO $ Client.queueTx clientHandler tx
    EC.handleChain (EC.queueTx tx)
  EC.GetCurrentSlot ->
    EC.handleChain EC.getCurrentSlot
