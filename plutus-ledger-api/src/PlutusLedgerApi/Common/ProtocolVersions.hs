{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
module PlutusLedgerApi.Common.ProtocolVersions
    ( ProtocolVersion (..)
    -- ** Protocol Version aliases
    -- | Based on https://github.com/input-output-hk/cardano-ledger/wiki/First-Block-of-Each-Era
    , shelleyPV
    , allegraPV
    , maryPV
    , alonzoPV
    , vasilPV
    , changPV
    ) where

import Codec.Serialise (Serialise)
import GHC.Generics (Generic)
import Prettyprinter

-- | This represents the Cardano protocol version, with its major and minor components.
-- This relies on careful understanding between us and the ledger as to what this means.
data ProtocolVersion = ProtocolVersion
    { pvMajor :: Int -- ^ the major component
    , pvMinor :: Int -- ^ the minor component
    }
  deriving stock (Show, Eq, Generic)
  deriving anyclass Serialise

instance Ord ProtocolVersion where
    -- same as deriving Ord, just for having it explicitly
    compare (ProtocolVersion major minor) (ProtocolVersion major' minor') =
        compare major major' <> compare minor minor'

instance Pretty ProtocolVersion where
    pretty (ProtocolVersion major minor) = pretty major <> "." <> pretty minor

-- | Shelley era was introduced in protocol version 2.0
shelleyPV :: ProtocolVersion
shelleyPV = ProtocolVersion 2 0

-- | Allegra era was introduced in protocol version 3.0
allegraPV :: ProtocolVersion
allegraPV = ProtocolVersion 3 0

-- | Mary era was introduced in protocol version 4.0
maryPV :: ProtocolVersion
maryPV = ProtocolVersion 4 0

-- | Alonzo era was introduced in protocol version 5.0
alonzoPV :: ProtocolVersion
alonzoPV = ProtocolVersion 5 0

-- | Vasil era was introduced in protocol version 7.0
vasilPV :: ProtocolVersion
vasilPV = ProtocolVersion 7 0

-- | Chang era is not yet published. It will probably be introduced in protocol version 8.0
changPV :: ProtocolVersion
changPV = ProtocolVersion 8 0
