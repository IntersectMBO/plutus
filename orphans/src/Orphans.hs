{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
module Orphans () where

import           Control.Monad.Freer.Extras.Log (LogLevel, LogMessage)
import           Data.Aeson                     (Value (..))

import qualified Data.OpenApi                   as OpenApi
import qualified Data.OpenApi.Schema            as OpenApi

deriving instance {-# INCOHERENT #-} OpenApi.ToSchema (LogMessage Value)
deriving instance {-# INCOHERENT #-} OpenApi.ToSchema LogLevel

instance {-# INCOHERENT #-} OpenApi.ToSchema Value where
    declareNamedSchema _ = pure $ OpenApi.NamedSchema (Just "JSON") mempty

