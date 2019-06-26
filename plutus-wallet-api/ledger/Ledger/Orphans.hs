{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Orphans where

import           Crypto.Hash                (Digest, SHA256)
import           IOTS                       (IotsType (iotsDefinition))
import qualified Language.PlutusTx.AssocMap as Map
import qualified Language.PlutusTx.Prelude  as P
import           Schema                     (ToSchema, toSchema)
import           Type.Reflection            (Typeable)

instance ToSchema (Digest SHA256) where
  toSchema = toSchema @String

instance ToSchema P.ByteString where
  toSchema = toSchema @String

instance IotsType (Digest SHA256) where
  iotsDefinition = iotsDefinition @String

instance IotsType P.ByteString where
  iotsDefinition = iotsDefinition @String

instance (Typeable k, Typeable v) => ToSchema (Map.Map k v)

instance (Typeable k, Typeable v, IotsType k, IotsType v) =>
         IotsType (Map.Map k v)
