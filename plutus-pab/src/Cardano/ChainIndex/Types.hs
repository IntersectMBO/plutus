{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.ChainIndex.Types where

import           Control.Lens                  (makeLenses)
import           Control.Monad.Freer.Log       (LogMessage)
import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Sequence                 (Seq)
import           Data.Text.Prettyprint.Doc     (Pretty (..), parens, (<+>))
import           GHC.Generics                  (Generic)
import           Servant.Client                (BaseUrl)

import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (Tagged (..), mkObjectStr)
import           Cardano.Node.Types            (FollowerID)
import           Ledger.Address                (Address)
import           Wallet.Emulator.ChainIndex    (ChainIndexEvent, ChainIndexState)

data AppState =
    AppState
        { _indexState      :: ChainIndexState
        , _indexEvents     :: Seq (LogMessage ChainIndexEvent)
        , _indexFollowerID :: Maybe FollowerID
        } deriving (Eq, Show)

initialAppState :: AppState
initialAppState = AppState mempty mempty Nothing

data ChainIndexConfig =
    ChainIndexConfig
        { ciBaseUrl          :: BaseUrl
        , ciWatchedAddresses :: [Address]
        }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

makeLenses ''AppState
makeLenses ''ChainIndexConfig

-- | Messages from the ChainIndex Server
data ChainIndexServerMsg =
    -- | Obtaining a new follower
    ObtainingFollowerID
    -- | Obtained a new follower 'FollowerID'
    | ObtainedFollowerID FollowerID
    -- | Updating the chain index with 'FollowerID'
    | UpdatingChainIndex FollowerID
    -- | Requesting new blocks from the node
    | AskingNodeForNewBlocks
    -- | Requesting the current slot from the node
    | AskingNodeForCurrentSlot
    -- | Starting a node client thread
    | StartingNodeClientThread
    -- | Starting ChainIndex service
    | StartingChainIndex
        Int    -- ^ Port number
      -- | Received transaction
    | ReceivedBlocksTxns
        Int    -- ^ Blocks
        Int    -- ^ Transactions
    | ChainEvent ChainIndexEvent
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ChainIndexServerMsg where
    pretty = \case
        ObtainingFollowerID -> "Obtaining follower ID"
        ObtainedFollowerID i -> "Obtained follower ID:" <+> pretty i
        UpdatingChainIndex i -> "Updating chain index with follower ID" <+> pretty i
        ReceivedBlocksTxns blocks txns -> "Received" <+> pretty blocks <+> "blocks" <+> parens (pretty txns <+> "transactions")
        AskingNodeForNewBlocks -> "Asking the node for new blocks"
        AskingNodeForCurrentSlot -> "Asking the node for the current slot"
        StartingNodeClientThread -> "Starting node client thread"
        StartingChainIndex port -> "Starting chain index on port: " <> pretty port
        ChainEvent e -> "Processing chain index event: " <> pretty e

instance ToObject ChainIndexServerMsg where
    toObject _ = \case
      ObtainingFollowerID      -> mkObjectStr "obtaining FollowerID" ()
      ObtainedFollowerID fID   -> mkObjectStr "obtained FollowerID" (Tagged @"followerID" fID)
      UpdatingChainIndex fID   -> mkObjectStr "updating chainIndex with FollowerID" (Tagged @"followerID" fID)
      ReceivedBlocksTxns x y   -> mkObjectStr "received block transactions" (Tagged @"blocks" x, Tagged @"transactions" y)
      AskingNodeForNewBlocks   -> mkObjectStr "asking for new blocks" ()
      AskingNodeForCurrentSlot -> mkObjectStr "asking node for current slot" ()
      StartingNodeClientThread -> mkObjectStr "starting node client thread" ()
      StartingChainIndex p     -> mkObjectStr "starting chain index" (Tagged @"port" p)
      ChainEvent e             -> mkObjectStr "processing chain event" (Tagged @"event" e)
