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
import qualified Ledger.AddressMap          as AM
import           Wallet.Emulator.Chain

data NodeClientEvent =
    TxSubmit TxId
    -- ^ A transaction has been added to the pool of pending transactions.
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty NodeClientEvent where
    pretty (TxSubmit tx) = "TxSubmit:" <+> pretty tx

data NodeClientState = NodeClientState {
    _clientSlot  :: Slot,
    _clientIndex :: AM.AddressMap
    -- ^ Full index
} deriving stock (Show, Eq)

emptyNodeClientState :: NodeClientState
emptyNodeClientState = NodeClientState (Slot 0) mempty

makeLenses ''NodeClientState

-- | A notification sent to a node client about a change in the ledger.
newtype BlockValidated = BlockValidated Block -- ^ A new block has been validated.
                  deriving (Show, Eq)

data NodeClientEffect r where
    PublishTx :: Tx -> NodeClientEffect ()
    GetClientSlot :: NodeClientEffect Slot
    GetClientIndex :: NodeClientEffect AM.AddressMap
    ClientNotify :: BlockValidated -> NodeClientEffect ()
makeEffect ''NodeClientEffect

type NodeClientEffs = '[ChainEffect, State NodeClientState, Writer [NodeClientEvent]]

handleNodeClient
    :: (Members NodeClientEffs effs)
    => Eff (NodeClientEffect ': effs) ~> Eff effs
handleNodeClient = interpret $ \case
    PublishTx tx -> queueTx tx >> tell [TxSubmit (txId tx)]
    GetClientSlot -> gets _clientSlot
    GetClientIndex -> gets _clientIndex
    ClientNotify n -> case n of
        BlockValidated blk -> modify $ \s ->
            s & clientIndex %~ (\am -> foldl (\am' t -> AM.updateAllAddresses t am') am blk)
              & clientSlot +~ 1
