{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Protocol.FollowerEffect where

import           Control.Concurrent.STM
import           Control.Monad.Freer
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Control.Monad.IO.Class

import           Data.Foldable                 (traverse_)

import qualified Cardano.Node.Follower         as NF
import qualified Cardano.Node.Types            as NT
import           Ledger                        (Block)
import           Wallet.Emulator.Chain         (ChainState (..), addBlock)

{- | This handler will update it's local state whenever interpreting
     a follower effect. -}
handleNodeFollower
  :: ( Member (State ChainState) effs
     , Member (State NT.NodeFollowerState) effs
     , Member (Reader (TQueue Block)) effs
     , Member Log effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff (NF.NodeFollowerEffect ': effs) ~> Eff effs
handleNodeFollower =
    (synchroniseState >>) . NF.handleNodeFollower

synchroniseState
  :: ( Member (State ChainState) effs
     , Member (Reader (TQueue Block)) effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff effs ()
synchroniseState = fetchBlocks >>= injectBlocks

fetchBlocks
  :: ( Member (Reader (TQueue Block)) effs
     , LastMember m effs
     , MonadIO m
     )
  => Eff effs [Block]
fetchBlocks =
  ask >>= sendM . liftIO . atomically . flushTQueue

injectBlocks
  :: Member (State ChainState) effs
  => [Block]
  -> Eff effs ()
injectBlocks = traverse_ (modify . addBlock)
