{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Plutus.V1.Ledger.Orphans where

import Data.Aeson (FromJSON (parseJSON), ToJSON (toJSON))
import Data.Aeson qualified as JSON
import Data.Aeson.Extras qualified as JSON
import Data.ByteString qualified as BSS
import PlutusTx.Builtins qualified as PlutusTx


instance ToJSON BSS.ByteString where
    toJSON = JSON.String . JSON.encodeByteString

instance FromJSON BSS.ByteString where
    parseJSON v = JSON.decodeByteString v

instance ToJSON PlutusTx.BuiltinByteString where
    toJSON = JSON.String . JSON.encodeByteString . PlutusTx.fromBuiltin

instance FromJSON PlutusTx.BuiltinByteString where
    parseJSON v = PlutusTx.toBuiltin <$> JSON.decodeByteString v
