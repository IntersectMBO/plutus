{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}

module Config(
  ChainIndexConfig(..),
  defaultConfig
  ) where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc (Pretty (..), vsep, (<+>))
import           GHC.Generics              (Generic)

data ChainIndexConfig = ChainIndexConfig
  { cicSocketPath :: String
  , cicPort       :: Int
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

defaultConfig :: ChainIndexConfig
defaultConfig = ChainIndexConfig
  { cicSocketPath = "/tmp/node-server.sock"
  , cicPort       = 9083
  }

instance Pretty ChainIndexConfig where
  pretty ChainIndexConfig{cicSocketPath, cicPort} =
    vsep ["Socket:" <+> pretty cicSocketPath, "Port:" <+> pretty cicPort]
