{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Orphans where

import           Crypto.Hash                (Digest, SHA256)
import           Data.Proxy                 (Proxy (Proxy))
import           Data.Typeable              (Typeable)
import qualified Language.PlutusTx.AssocMap as Map
import qualified Language.PlutusTx.Prelude  as P
import           Schema                     (ToSchema, toSchema)

instance ToSchema (Digest SHA256) where
  toSchema _ = toSchema (Proxy :: Proxy String)

instance ToSchema P.ByteString where
  toSchema _ = toSchema (Proxy :: Proxy String)

deriving anyclass instance
         (Typeable k, Typeable v, ToSchema k, ToSchema v) =>
         ToSchema (Map.Map k v)
