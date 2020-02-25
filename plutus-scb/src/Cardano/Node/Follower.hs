{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Node.Follower where

import           Control.Lens                    hiding (assign, modifying, use)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH          (makeEffect)

import qualified Data.Map                        as Map

import           Cardano.Node.Types              (FollowerID, NodeFollowerState, _NodeFollowerState)
import           Ledger                          (Block)
import           Plutus.SCB.Utils                (tshow)
import           Wallet.Emulator.Chain           (ChainState)
import qualified Wallet.Emulator.Chain           as Chain

data NodeFollowerEffect r where
    NewFollower :: NodeFollowerEffect FollowerID
    GetBlocks :: FollowerID -> NodeFollowerEffect [Block]

makeEffect ''NodeFollowerEffect

handleNodeFollower ::
    ( Member (State ChainState) effs
    , Member (State NodeFollowerState) effs
    , Member Log effs)
    => Eff (NodeFollowerEffect ': effs) ~> Eff effs
handleNodeFollower = interpret $ \case
    NewFollower -> do
        newID <- maybe 0 succ <$> use (_NodeFollowerState . to (fmap fst <$> Map.lookupMax))
        assign (_NodeFollowerState . at newID) (Just 0)
        logInfo $ "New follower ID: " <> tshow newID
        pure newID
    GetBlocks i -> do
        logDebug $ "Get blocks for " <> tshow i
        lastBlock <- use (_NodeFollowerState . at i . non 0)
        logDebug $ "Last block: " <> tshow lastBlock
        chain <- use Chain.chainNewestFirst
        let newLastBlock = length chain
        logDebug $ "New last block: " <> tshow newLastBlock
        assign (_NodeFollowerState . at i) (Just newLastBlock)
        pure $ take (newLastBlock - lastBlock) $ reverse chain
