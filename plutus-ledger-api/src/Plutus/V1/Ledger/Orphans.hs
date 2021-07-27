{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Plutus.V1.Ledger.Orphans where

import           Data.Aeson        (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson        as JSON
import qualified Data.Aeson.Extras as JSON
import qualified Data.ByteString   as BSS


instance ToJSON BSS.ByteString where
    toJSON = JSON.String . JSON.encodeByteString

instance FromJSON BSS.ByteString where
    parseJSON v = JSON.decodeByteString v
