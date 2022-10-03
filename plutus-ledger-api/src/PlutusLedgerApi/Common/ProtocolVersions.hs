{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
module PlutusLedgerApi.Common.ProtocolVersions where

import Codec.Serialise (Serialise)
import GHC.Generics (Generic)
import Prettyprinter

-- | This represents the Cardano protocol version, with its major and minor components.
-- This relies on careful understanding between us and the ledger as to what this means.
data ProtocolVersion = ProtocolVersion { pvMajor :: Int, pvMinor :: Int }
  deriving stock (Show, Eq, Generic)
  deriving anyclass Serialise

instance Ord ProtocolVersion where
    -- same as deriving Ord, just for having it explicitly
    compare (ProtocolVersion major minor) (ProtocolVersion major' minor') =
        compare major major' <> compare minor minor'

instance Pretty ProtocolVersion where
    pretty (ProtocolVersion major minor) = pretty major <> "." <> pretty minor

-- Based on https://github.com/input-output-hk/cardano-ledger/wiki/First-Block-of-Each-Era

pattern ShelleyPV :: ProtocolVersion
pattern ShelleyPV = ProtocolVersion 2 0

pattern AllegraPV :: ProtocolVersion
pattern AllegraPV = ProtocolVersion 3 0

pattern MaryPV :: ProtocolVersion
pattern MaryPV = ProtocolVersion 4 0

pattern AlonzoPV :: ProtocolVersion
pattern AlonzoPV = ProtocolVersion 5 0

pattern VasilPV :: ProtocolVersion
pattern VasilPV = ProtocolVersion 7 0

pattern ChangPV :: ProtocolVersion
-- FIXME: exact version number TBD
pattern ChangPV = ProtocolVersion 1000 0
