{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
module Orphans () where

import           Control.Monad.Freer.Extras.Log (LogLevel, LogMessage)
import           Data.Aeson                     (Value (..))

import qualified Data.Swagger                   as Swagger
import qualified Data.Swagger.Schema            as Swagger

deriving instance {-# INCOHERENT #-} Swagger.ToSchema (LogMessage Value)
deriving instance {-# INCOHERENT #-} Swagger.ToSchema LogLevel

instance {-# INCOHERENT #-} Swagger.ToSchema Value where
    declareNamedSchema _ = pure $ Swagger.NamedSchema (Just "JSON") mempty

