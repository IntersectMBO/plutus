{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Orphans where

import           Crypto.Hash               (Digest, SHA256)
import           Data.Proxy                (Proxy (Proxy))
import qualified Language.PlutusTx.Prelude as P
import           Schema                    (ToSchema, toSchema)
import           Schema.IOTS               (HasReps (typeReps))

instance ToSchema (Digest SHA256) where
  toSchema _ = toSchema (Proxy :: Proxy String)

instance ToSchema P.ByteString where
  toSchema _ = toSchema (Proxy :: Proxy String)

instance HasReps (Digest SHA256) where
  typeReps _ = typeReps (Proxy :: Proxy String)

instance HasReps P.ByteString where
  typeReps _ = typeReps (Proxy :: Proxy String)
