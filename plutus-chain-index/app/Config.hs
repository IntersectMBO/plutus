{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Config where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics (Generic)

newtype ChainIndexConfig = ChainIndexConfig
  { cicSocketPath :: String
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)
