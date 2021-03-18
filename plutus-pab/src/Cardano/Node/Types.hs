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

     -- * Event types
    , BlockEvent (..)

     -- * Effects
    , NodeServerEffects
    , GenRandomTx (..)
    , genRandomTx

     -- *  State types
    , AppState (..)
    , initialAppState
    , initialChainState

    -- * Lens functions
    , chainState
    , eventHistory

    -- * Config types
    , MockServerConfig (..)
    , BlockReaperConfig (..)

    -- * newtype wrappers
    , NodeUrl (..)
    )
        where

import           Control.Lens                   (makeLenses, view)
import           Control.Monad.Freer.TH         (makeEffect)
import           Data.Aeson                     (FromJSON, ToJSON)
import qualified Data.Map                       as Map
import           Data.Text.Prettyprint.Doc      (Pretty (..), pretty, (<+>))
import           Data.Time.Units                (Second)
import           Data.Time.Units.Extra          ()
import           GHC.Generics                   (Generic)
import           Ledger                         (Tx, txId)
import           Servant.Client                 (BaseUrl)

import           Cardano.BM.Data.Tracer         (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras  (Tagged (..), mkObjectStr)
import qualified Cardano.Protocol.Socket.Client as Client
import           Control.Monad.Freer.Extras.Log (LogMessage, LogMsg (..))
import           Control.Monad.Freer.Reader     (Reader)
import           Control.Monad.Freer.State      (State)
import qualified Plutus.Contract.Trace          as Trace
import           Wallet.Emulator                (Wallet)
import qualified Wallet.Emulator                as EM
import           Wallet.Emulator.Chain          (ChainControlEffect, ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.MultiAgent     as MultiAgent

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

instance ToObject MockServerLogMsg where
    toObject _ = \case
        NoRandomTxGeneration      ->  mkObjectStr "Not creating random transactions" ()
        StartingRandomTx          ->  mkObjectStr "Starting random transaction generation thread" ()
        KeepingOldBlocks          ->  mkObjectStr "Not starting block reaper thread (old blocks will be retained in-memory forever" ()
        RemovingOldBlocks         ->  mkObjectStr "Starting block reaper thread (old blocks will be removed)" ()
        StartingMockServer p      ->  mkObjectStr "Starting Mock Node Server on port " (Tagged @"port" p)
        StartingSlotCoordination  ->  mkObjectStr "" ()
        ProcessingChainEvent e    ->  mkObjectStr "Processing chain event" (Tagged @"event" e)
        BlockOperation e          ->  mkObjectStr "Block operation" (Tagged @"event" e)
        CreatingRandomTransaction ->  mkObjectStr "Creating random transaction" ()

data BlockEvent = NewSlot
    | NewTransaction Tx
    deriving (Generic, Show, ToJSON, FromJSON)

instance Pretty BlockEvent where
    pretty = \case
        NewSlot          -> "Adding a new slot"
        NewTransaction t -> "Adding a transaction " <+> pretty (Ledger.txId t)


-- State --------------------------------------------------------------------------------------------------------------

-- | Application State
data AppState =
    AppState
        { _chainState   :: ChainState -- ^ blockchain state
        , _eventHistory :: [LogMessage MockServerLogMsg] -- ^ history of all log messages
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
        }

-- | 'ChainState' with initial values
initialChainState :: Trace.InitialDistribution -> ChainState
initialChainState =
    view EM.chainState .
    MultiAgent.emulatorStateInitialDist . Map.mapKeys EM.walletPubKey

-- Effects -------------------------------------------------------------------------------------------------------------

type NodeServerEffects m
     = '[ GenRandomTx
        , LogMsg MockServerLogMsg
        , ChainControlEffect
        , ChainEffect
        , State ChainState
        , LogMsg MockServerLogMsg
        , Reader Client.ClientHandler
        , State AppState
        , LogMsg MockServerLogMsg
        , m]

data GenRandomTx r where
    GenRandomTx :: GenRandomTx Tx

makeEffect ''GenRandomTx
