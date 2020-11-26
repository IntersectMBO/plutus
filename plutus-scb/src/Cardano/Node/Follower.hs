{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Node.Follower where

import           Control.Lens                    hiding (assign, use)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH          (makeEffect)
import           Data.Text.Prettyprint.Doc       (Pretty (..), (<+>))

import qualified Data.Map                        as Map

import           Cardano.Node.Types              (FollowerID, NodeFollowerState, _NodeFollowerState)
import           Ledger                          (Block, Slot)
import           Wallet.Emulator.Chain           (ChainState)
import qualified Wallet.Emulator.Chain           as Chain

data NodeFollowerEffect r where
    NewFollower :: NodeFollowerEffect FollowerID
    GetBlocks :: FollowerID -> NodeFollowerEffect [Block]
    GetSlot :: NodeFollowerEffect Slot

makeEffect ''NodeFollowerEffect

data NodeFollowerLogMsg =
    NewFollowerId FollowerID
    | GetBlocksFor FollowerID
    | LastBlock Int
    | NewLastBlock Int
    | GetCurrentSlot Slot

instance Pretty NodeFollowerLogMsg where
    pretty  = \case
        NewFollowerId newID -> "New follower ID:" <+> pretty newID
        GetBlocksFor i      -> "Get blocks for" <+> pretty i
        LastBlock i         -> "Last block:" <+> pretty i
        NewLastBlock i      -> "New last block:" <+> pretty i
        GetCurrentSlot s    -> "Get current slot:" <+> pretty s

handleNodeFollower ::
    ( Member (State ChainState) effs
    , Member (State NodeFollowerState) effs
    , Member (LogMsg NodeFollowerLogMsg) effs
    )
    => Eff (NodeFollowerEffect ': effs) ~> Eff effs
handleNodeFollower = interpret $ \case
    NewFollower -> do
        newID <- maybe 0 succ <$> use (_NodeFollowerState . to (fmap fst <$> Map.lookupMax))
        assign (_NodeFollowerState . at newID) (Just 0)
        logInfo $ NewFollowerId newID
        pure newID
    GetBlocks i -> do
        logDebug $ GetBlocksFor i
        lastBlock <- use (_NodeFollowerState . at i . non 0)
        logDebug $ LastBlock lastBlock
        chain <- use Chain.chainNewestFirst
        let newLastBlock = length chain
        logDebug $ NewLastBlock newLastBlock
        assign (_NodeFollowerState . at i) (Just newLastBlock)
        pure $ reverse $ take (newLastBlock - lastBlock) chain
    GetSlot -> do
        s <- use Chain.currentSlot
        logDebug $ GetCurrentSlot s
        pure s
