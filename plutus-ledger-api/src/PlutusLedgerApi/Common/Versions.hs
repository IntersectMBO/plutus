-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
module PlutusLedgerApi.Common.Versions
    ( PlutusVersion (..)
    , ProtocolVersion (..)
    , pattern ShelleyPV
    , pattern AllegraPV
    , pattern MaryPV
    , pattern AlonzoPV
    , pattern VasilPV
    , pattern ChangPV
    ) where

import Codec.Serialise (Serialise)
import GHC.Generics (Generic)
import Prettyprinter.Extras

{-| The plutus language version as seen from the ledger's side.

IMPORTANT: the `Ord` instance matters and is the canonical derived one.
-}
data PlutusVersion =
      PlutusV1
    | PlutusV2
    | PlutusV3
   deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)
   deriving Pretty via (PrettyShow PlutusVersion)

{-| This represents the Cardano protocol version, with its major and minor components.
It relies on careful understanding between us and the ledger as to what this means.

IMPORTANT: the `Ord` instance matters and is the canonical derived one.
-}
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

-- | Synonym for `ProtocolVersion 2 0`
pattern ShelleyPV :: ProtocolVersion
pattern ShelleyPV = ProtocolVersion 2 0

-- | Synonym for `ProtocolVersion 3 0`
pattern AllegraPV :: ProtocolVersion
pattern AllegraPV = ProtocolVersion 3 0

-- | Synonym for `ProtocolVersion 4 0`
pattern MaryPV :: ProtocolVersion
pattern MaryPV = ProtocolVersion 4 0

-- | Synonym for `ProtocolVersion 5 0`
pattern AlonzoPV :: ProtocolVersion
pattern AlonzoPV = ProtocolVersion 5 0

-- | Synonym for `ProtocolVersion 7 0`
pattern VasilPV :: ProtocolVersion
pattern VasilPV = ProtocolVersion 7 0

-- | Synonym for `ProtocolVersion 1000 0`
pattern ChangPV :: ProtocolVersion
-- FIXME: exact version number TBD
pattern ChangPV = ProtocolVersion 1000 0
