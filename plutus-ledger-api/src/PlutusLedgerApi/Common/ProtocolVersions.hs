{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
module PlutusLedgerApi.Common.ProtocolVersions
    ( MajorProtocolVersion (..)
    -- ** Protocol Version aliases
    -- | Based on https://github.com/input-output-hk/cardano-ledger/wiki/First-Block-of-Each-Era
    , shelleyPV
    , allegraPV
    , maryPV
    , alonzoPV
    , vasilPV
    , valentinePV
    , conwayPV
    , knownPVs
    , futurePV
    ) where

import Codec.Serialise (Serialise)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Prettyprinter

-- | This represents the major component of the Cardano protocol version.
-- The ledger can only supply the major component of the protocol version, not the minor
-- component, and Plutus should only need to care about the major component anyway.
-- This relies on careful understanding between us and the ledger as to what this means.
newtype MajorProtocolVersion = MajorProtocolVersion { getMajorProtocolVersion :: Int }
  deriving newtype (Eq, Ord, Show, Serialise)
  deriving stock (Generic)

instance Pretty MajorProtocolVersion where
    pretty (MajorProtocolVersion v) = pretty v

-- | Shelley era was introduced in protocol version 2.0
shelleyPV :: MajorProtocolVersion
shelleyPV = MajorProtocolVersion 2

-- | Allegra era was introduced in protocol version 3.0
allegraPV :: MajorProtocolVersion
allegraPV = MajorProtocolVersion 3

-- | Mary era was introduced in protocol version 4.0
maryPV :: MajorProtocolVersion
maryPV = MajorProtocolVersion 4

-- | Alonzo era was introduced in protocol version 5.0
alonzoPV :: MajorProtocolVersion
alonzoPV = MajorProtocolVersion 5

-- | Vasil era was introduced in protocol version 7.0
vasilPV :: MajorProtocolVersion
vasilPV = MajorProtocolVersion 7

-- | Protocol version 8.0 was the Valentine intra-era HF
valentinePV :: MajorProtocolVersion
valentinePV = MajorProtocolVersion 8

-- | Conway era was introduced in protocol version 9.0
conwayPV :: MajorProtocolVersion
conwayPV = MajorProtocolVersion 9

-- | The set of protocol versions that are "known", i.e. that have been released
-- and have actual differences associated with them.
knownPVs :: Set.Set MajorProtocolVersion
knownPVs = Set.fromList [ shelleyPV, allegraPV, maryPV, alonzoPV, vasilPV, valentinePV, conwayPV ]

-- | This is a placeholder for when we don't yet know what protocol
-- version will be used for something. It's a very high protocol
-- version that should never appear in reality.
--
-- We should not assign names to future protocol versions until it's
-- confirmed that they are correct, otherwise we could accidentally
-- associate something with the wrong protocol version.
futurePV :: MajorProtocolVersion
futurePV = MajorProtocolVersion maxBound
