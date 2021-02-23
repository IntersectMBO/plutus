{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-| This module exports data types for logging, events and configuration
-}
module Cardano.Node.Types
    (
      -- * Logging types
      MockServerLogMsg (..)
    , NodeFollowerLogMsg (..)
    , FollowerID

     -- * Event types
    , BlockEvent (..)

     -- * Effects
    , NodeFollowerEffect (..)
    , NodeServerEffects
    , getBlocks
    , getSlot
    , newFollower
    , GenRandomTx (..)
    , genRandomTx

     -- *  State types
    , AppState (..)
    , NodeFollowerState (..)
    , _NodeFollowerState
    , initialAppState
    , initialChainState
    , initialFollowerState

    -- * Lens functions
    , chainState
    , eventHistory
    , followerState

    -- * Config types
    , MockServerConfig (..)
    , BlockReaperConfig (..)

    -- * newtype wrappers
    , NodeUrl (..)
    )
        where

import           Control.Lens                   (makeLenses, makePrisms, view)
import           Control.Monad.Freer.TH         (makeEffect)
import           Data.Aeson                     (FromJSON, ToJSON)
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           Data.Text.Prettyprint.Doc      (Pretty (..), pretty, (<+>))
import           Data.Time.Units                (Second)
import           Data.Time.Units.Extra          ()
import           GHC.Generics                   (Generic)
import           Ledger                         (Block, Slot, Tx, txId)
import           Servant                        (FromHttpApiData, ToHttpApiData)
import           Servant.Client                 (BaseUrl)

import           Cardano.BM.Data.Tracer         (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras  (Tagged (..), mkObjectStr)
import           Cardano.Protocol.Socket.Client (ClientHandler)
import           Control.Monad.Freer.Extras.Log (LogMessage, LogMsg (..))
import           Control.Monad.Freer.Reader     (Reader)
import           Control.Monad.Freer.State      (State)
import qualified Language.Plutus.Contract.Trace as Trace
import           Wallet.Emulator                (Wallet)
import qualified Wallet.Emulator                as EM
import           Wallet.Emulator.Chain          (ChainControlEffect, ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.MultiAgent     as MultiAgent

import qualified Cardano.Protocol.Socket.Server as Server
import           Plutus.PAB.Arbitrary           ()

-- Configuration ------------------------------------------------------------------------------------------------------

newtype NodeUrl = NodeUrl BaseUrl
    deriving (Show, Eq) via BaseUrl

-- | Mock Node server configuration
data MockServerConfig =
    MockServerConfig
        { mscBaseUrl          :: BaseUrl
        -- ^ base url of the service
        , mscSlotLength       :: Second
        -- ^ Duration of one slot
        , mscRandomTxInterval :: Maybe Second
        -- ^ Time between two randomly generated transactions
        , mscBlockReaper      :: Maybe BlockReaperConfig
        -- ^ When to discard old blocks
        , mscInitialTxWallets :: [Wallet]
        -- ^ The wallets that receive money from the initial transaction.
        , mscSocketPath       :: FilePath
        -- ^ Path to the socket used to communicate with the server.
        }
    deriving (Show, Eq, Generic, FromJSON)

-- | Configuration for 'Cardano.Node.Mock.blockReaper'
data BlockReaperConfig =
    BlockReaperConfig
        { brcInterval     :: Second -- ^ interval in seconds for discarding blocks
        , brcBlocksToKeep :: Int    -- ^ number of blocks to keep
        }
    deriving (Show, Eq, Generic, FromJSON)


-- Logging ------------------------------------------------------------------------------------------------------------

-- | Top-level logging data type for structural logging
-- inside the Mock Node server.
data MockServerLogMsg =
    StartingSlotCoordination
    | NoRandomTxGeneration
    | StartingRandomTx
    | KeepingOldBlocks
    | RemovingOldBlocks
    | StartingMockServer Int
    | ProcessingChainEvent ChainEvent
    | BlockOperation BlockEvent
    | CreatingRandomTransaction
    | FollowerMsg NodeFollowerLogMsg
    deriving (Generic, Show, ToJSON, FromJSON)

instance Pretty MockServerLogMsg where
    pretty = \case
        NoRandomTxGeneration      -> "Not creating random transactions"
        StartingRandomTx          -> "Starting random transaction generation thread"
        KeepingOldBlocks          -> "Not starting block reaper thread (old blocks will be retained in-memory forever"
        RemovingOldBlocks         -> "Starting block reaper thread (old blocks will be removed)"
        StartingMockServer p      -> "Starting Mock Node Server on port " <+> pretty p
        StartingSlotCoordination  -> "Starting slot coordination thread"
        ProcessingChainEvent e    -> "Processing chain event " <+> pretty e
        BlockOperation e          -> "Block operation " <+> pretty e
        CreatingRandomTransaction -> "Generating a random transaction"
        FollowerMsg m             -> pretty m

instance ToObject MockServerLogMsg where
    toObject v = \case
        NoRandomTxGeneration      ->  mkObjectStr "Not creating random transactions" ()
        StartingRandomTx          ->  mkObjectStr "Starting random transaction generation thread" ()
        KeepingOldBlocks          ->  mkObjectStr "Not starting block reaper thread (old blocks will be retained in-memory forever" ()
        RemovingOldBlocks         ->  mkObjectStr "Starting block reaper thread (old blocks will be removed)" ()
        StartingMockServer p      ->  mkObjectStr "Starting Mock Node Server on port " (Tagged @"port" p)
        StartingSlotCoordination  ->  mkObjectStr "" ()
        ProcessingChainEvent e    ->  mkObjectStr "Processing chain event" (Tagged @"event" e)
        BlockOperation e          ->  mkObjectStr "Block operation" (Tagged @"event" e)
        CreatingRandomTransaction ->  mkObjectStr "Creating random transaction" ()
        FollowerMsg m             -> toObject v m

-- | logging type for 'Cardano.Node.Follower'
data NodeFollowerLogMsg =
    NewFollowerId FollowerID
    | GetBlocksFor FollowerID
    | LastBlock Int
    | NewLastBlock Int
    | GetCurrentSlot Slot
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

instance Pretty NodeFollowerLogMsg where
    pretty  = \case
        NewFollowerId newID -> "New follower ID:" <+> pretty newID
        GetBlocksFor i      -> "Get blocks for" <+> pretty i
        LastBlock i         -> "Last block:" <+> pretty i
        NewLastBlock i      -> "New last block:" <+> pretty i
        GetCurrentSlot s    -> "Get current slot:" <+> pretty s

instance ToObject NodeFollowerLogMsg where
    toObject _ = \case
        NewFollowerId fId  -> mkObjectStr "new follower id" (Tagged @"id" fId)
        GetBlocksFor bId   -> mkObjectStr "Get blocks for " (Tagged @"id" bId)
        LastBlock bId      -> mkObjectStr "Last block" (Tagged @"id" bId)
        NewLastBlock bId   -> mkObjectStr "New last block" (Tagged @"id" bId)
        GetCurrentSlot bId -> mkObjectStr "Get current slot" (Tagged @"id" bId)

newtype FollowerID = FollowerID Int
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (ToJSON, FromJSON, ToHttpApiData, FromHttpApiData, Integral, Enum, Real, Num, Pretty)

data BlockEvent = NewSlot
    | NewTransaction Tx
    deriving (Generic, Show, ToJSON, FromJSON)

instance Pretty BlockEvent where
    pretty = \case
        NewSlot          -> "Adding a new slot"
        NewTransaction t -> "Adding a transaction " <+> pretty (Ledger.txId t)


-- State --------------------------------------------------------------------------------------------------------------


newtype NodeFollowerState = NodeFollowerState { unNodeFollowerState :: Map FollowerID Int }
    deriving (Show)

makePrisms 'NodeFollowerState

-- | Application State
data AppState =
    AppState
        { _chainState    :: ChainState -- ^ blockchain state
        , _eventHistory  :: [LogMessage MockServerLogMsg] -- ^ history of all log messages
        , _followerState :: NodeFollowerState -- ^ follower state
        }
    deriving (Show)

makeLenses 'AppState

-- | 'AppState' with an initial transaction that pays some Ada to
--   the wallets.
initialAppState :: [Wallet] -> AppState
initialAppState wallets =
    AppState
        { _chainState = initialChainState (Trace.defaultDistFor wallets)
        , _eventHistory = mempty
        , _followerState = initialFollowerState
        }

-- | Empty initial 'NodeFollowerState'
initialFollowerState :: NodeFollowerState
initialFollowerState = NodeFollowerState Map.empty

-- | 'ChainState' with initial values
initialChainState :: Trace.InitialDistribution -> ChainState
initialChainState =
    view EM.chainState .
    MultiAgent.emulatorStateInitialDist . Map.mapKeys EM.walletPubKey

-- Effects -------------------------------------------------------------------------------------------------------------

data NodeFollowerEffect r where
    NewFollower :: NodeFollowerEffect FollowerID
    GetBlocks :: FollowerID -> NodeFollowerEffect [Block]
    GetSlot :: NodeFollowerEffect Slot

makeEffect ''NodeFollowerEffect

type NodeServerEffects m
     = '[ GenRandomTx
        , LogMsg MockServerLogMsg
        , NodeFollowerEffect
        , LogMsg NodeFollowerLogMsg
        , ChainControlEffect
        , ChainEffect
        , State NodeFollowerState
        , State ChainState
        , LogMsg MockServerLogMsg
        , Reader ClientHandler
        , Reader Server.ServerHandler
        , State AppState
        , LogMsg MockServerLogMsg
        , m]

data GenRandomTx r where
    GenRandomTx :: GenRandomTx Tx

makeEffect ''GenRandomTx
