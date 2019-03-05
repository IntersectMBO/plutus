{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map(module Map , module These) where

import           Data.Aeson                   (FromJSON (parseJSON), ToJSON (toJSON))
import           Data.Hashable                (Hashable)
import           Data.Swagger.Internal.Schema (ToSchema (..))
import           Data.Proxy
import           Language.PlutusTx.Prelude    hiding (all, lookup, map, foldr)
import           Language.PlutusTx.Map as Map
import qualified Language.PlutusTx.RBTree as Tree

import           Language.PlutusTx.These as These

{-# ANN module ("HLint: ignore Use newtype instead of data"::String) #-}

deriving anyclass instance Hashable Tree.Color
deriving anyclass instance (Hashable k, Hashable v) => (Hashable (Map k v))

instance (ToSchema k, ToSchema v) => (ToSchema (Map k v)) where
    declareNamedSchema _ = declareNamedSchema (Proxy @[(k, v)])

instance (ToJSON v, ToJSON k) => ToJSON (Map k v) where
    toJSON = toJSON . toList

instance (Ord k, FromJSON v, FromJSON k) => FromJSON (Map k v) where
    parseJSON v = fromList compare <$> parseJSON v
