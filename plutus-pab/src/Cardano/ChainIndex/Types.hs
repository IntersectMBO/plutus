{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.ChainIndex.Types where

import           Control.Lens                  (makeLenses)
import           Control.Monad.Freer.State
import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Default                  (Default, def)
import           Data.Text.Prettyprint.Doc     (Pretty (..), parens, (<+>))
import           GHC.Generics                  (Generic)
import           Servant.Client                (BaseUrl (..), Scheme (..))

import           Cardano.BM.Data.Trace         (Trace)
import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (Tagged (..), mkObjectStr)
import           Control.Monad.Freer.Error     (Error)
import           Control.Monad.Freer.Extras    (LogMsg)
import           Plutus.ChainIndex             (ChainIndexControlEffect, ChainIndexEmulatorState, ChainIndexError,
                                                ChainIndexLog, ChainIndexQueryEffect)

type ChainIndexEffects m
     = '[ ChainIndexControlEffect
        , ChainIndexQueryEffect
        , State ChainIndexEmulatorState
        , LogMsg ChainIndexLog
        , Error ChainIndexError
        , m
        ]

newtype ChainIndexUrl = ChainIndexUrl BaseUrl
    deriving (Eq, Show, FromJSON, ToJSON) via BaseUrl

newtype ChainIndexConfig =
    ChainIndexConfig
        { ciBaseUrl          :: ChainIndexUrl
        }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

defaultChainIndexConfig :: ChainIndexConfig
defaultChainIndexConfig =
  ChainIndexConfig
    -- See Note [pab-ports] in "test/full/Plutus/PAB/CliSpec.hs".
    { ciBaseUrl = ChainIndexUrl $ BaseUrl Http "127.0.0.1" 9083 ""
    }

instance Default ChainIndexConfig where
  def = defaultChainIndexConfig

makeLenses ''ChainIndexConfig

-- | Messages from the ChainIndex Server
data ChainIndexServerMsg =
    -- | Starting a node client thread
      StartingNodeClientThread
    -- | Starting ChainIndex service
    | StartingChainIndex
        Int    -- ^ Port number
      -- | Received transaction
    | ReceivedBlocksTxns
        Int    -- ^ Blocks
        Int    -- ^ Transactions
    | ChainEvent ChainIndexLog
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

type ChainIndexTrace = Trace IO ChainIndexServerMsg

instance Pretty ChainIndexServerMsg where
    pretty = \case
        ReceivedBlocksTxns blocks txns -> "Received" <+> pretty blocks <+> "blocks" <+> parens (pretty txns <+> "transactions")
        StartingNodeClientThread -> "Starting node client thread"
        StartingChainIndex port -> "Starting chain index on port: " <> pretty port
        ChainEvent e -> "Processing chain index event: " <> pretty e

instance ToObject ChainIndexServerMsg where
    toObject _ = \case
      ReceivedBlocksTxns x y   -> mkObjectStr "received block transactions" (Tagged @"blocks" x, Tagged @"transactions" y)
      StartingNodeClientThread -> mkObjectStr "starting node client thread" ()
      StartingChainIndex p     -> mkObjectStr "starting chain index" (Tagged @"port" p)
      ChainEvent e             -> mkObjectStr "processing chain event" (Tagged @"event" e)
