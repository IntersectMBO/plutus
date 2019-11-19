{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
module Wallet.Emulator.NodeClient where

import           Control.Lens               hiding (index)
import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH
import           Control.Monad.Freer.Writer
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc  hiding (annotate)
import           GHC.Generics               (Generic)
import           Ledger
import           Wallet.Emulator.Chain

data NodeClientEvent =
    TxSubmit TxId
    -- ^ A transaction has been added to the pool of pending transactions.
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty NodeClientEvent where
    pretty (TxSubmit tx) = "TxSubmit:" <+> pretty tx

data NodeClientState = NodeClientState {
    _clientSlot :: Slot
} deriving stock (Show, Eq)

emptyNodeClientState :: NodeClientState
emptyNodeClientState = NodeClientState (Slot 0)

makeLenses ''NodeClientState

-- | A notification sent to a node client about a change in the ledger.
data Notification = BlockValidated Block -- ^ A new block has been validated.
                  | CurrentSlot Slot -- ^ The current slot has changed.
                  deriving (Show, Eq)

data NodeClientEffect r where
    PublishTx :: Tx -> NodeClientEffect ()
    GetClientSlot :: NodeClientEffect Slot
    ClientNotify :: Notification -> NodeClientEffect ()
makeEffect ''NodeClientEffect

type NodeClientEffs = '[ChainEffect, State NodeClientState, Writer [NodeClientEvent]]

handleNodeClient
    :: (Members NodeClientEffs effs)
    => Eff (NodeClientEffect ': effs) ~> Eff effs
handleNodeClient = interpret $ \case
    PublishTx tx -> queueTx tx >> tell [TxSubmit (txId tx)]
    GetClientSlot -> gets _clientSlot
    ClientNotify n -> case n of
        BlockValidated _ -> modify (\s -> s & clientSlot +~ 1)
        CurrentSlot sl   -> modify (\s -> s & clientSlot .~ sl)
