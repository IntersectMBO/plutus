{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Events.User where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics (Generic)

newtype UserEvent =
    InstallContract FilePath
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)
