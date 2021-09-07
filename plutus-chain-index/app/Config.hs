{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Config(
  ChainIndexConfig(..),
  defaultConfig
  ) where

import           Cardano.Api               (NetworkId (..))
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc (Pretty (..), vsep, (<+>))
import           GHC.Generics              (Generic)
import           Ledger.TimeSlot           (SlotConfig (..))
import           Ouroboros.Network.Magic   (NetworkMagic (..))

data ChainIndexConfig = ChainIndexConfig
  { cicSocketPath :: String
  , cicPort       :: Int
  , cicNetworkId  :: NetworkId
  , cicSlotConfig :: SlotConfig
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | For some reason these are not defined anywhere, and these are the
--   reason for the -Wno-orphans option.
deriving stock instance Generic NetworkId
deriving anyclass instance FromJSON NetworkId
deriving anyclass instance ToJSON NetworkId
deriving anyclass instance FromJSON NetworkMagic
deriving anyclass instance ToJSON NetworkMagic

-- | These settings work with the Alonzo Purple testnet
defaultConfig :: ChainIndexConfig
defaultConfig = ChainIndexConfig
  { cicSocketPath = "/tmp/node-server.sock"
  , cicPort       = 9083
  , cicNetworkId  = Testnet $ NetworkMagic 8
  , cicSlotConfig =
      SlotConfig
        { scSlotZeroTime = 1591566291000
        , scSlotLength   = 1000
        }
  }

instance Pretty ChainIndexConfig where
  pretty ChainIndexConfig{cicSocketPath, cicPort} =
    vsep ["Socket:" <+> pretty cicSocketPath, "Port:" <+> pretty cicPort]
