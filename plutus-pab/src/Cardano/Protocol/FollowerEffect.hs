{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Protocol.FollowerEffect where

import           Control.Monad.Freer
import           Control.Monad.Freer.Extras.Log
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Control.Monad.IO.Class

import           Data.Foldable                  (traverse_)

import qualified Cardano.Node.Follower          as NF
import           Cardano.Node.Types
import qualified Cardano.Protocol.Socket.Client as Client
import           Ledger                         (Block)
import           Wallet.Emulator.Chain          (ChainState (..), addBlock)

{- | This handler will update it's local state whenever interpreting
     a follower effect. -}
handleNodeFollower
  :: ( Member (State ChainState) effs
     , Member (State NodeFollowerState) effs
     , Member (Reader Client.ClientHandler) effs
     , Member (LogMsg NodeFollowerLogMsg) effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff (NF.NodeFollowerEffect ': effs) ~> Eff effs
handleNodeFollower =
    (synchroniseState >>) . NF.handleNodeFollower

synchroniseState
  :: ( Member (State ChainState) effs
     , Member (Reader Client.ClientHandler) effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff effs ()
synchroniseState = fetchBlocks >>= injectBlocks

fetchBlocks
  :: ( Member (Reader Client.ClientHandler) effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff effs [Block]
fetchBlocks =
  ask >>= sendM . liftIO . Client.flushBlocks

injectBlocks
  :: Member (State ChainState) effs
  => [Block]
  -> Eff effs ()
injectBlocks = traverse_ (modify . addBlock)
