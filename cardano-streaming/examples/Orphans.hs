{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Orphans where

import Cardano.Api (BlockHeader (BlockHeader), ChainPoint (ChainPoint, ChainPointAtGenesis), ToJSON)
import Cardano.Streaming.Helpers (ChainSyncEvent)
import GHC.Generics (Generic)

deriving instance Generic ChainPoint

deriving instance Generic BlockHeader

instance ToJSON BlockHeader

instance (ToJSON a) => ToJSON (ChainSyncEvent a)
