module PlutusLedgerApi.Common.ProtocolVersions
  ( MajorProtocolVersion (..)

    -- ** Protocol Version aliases
    -- | Based on https://github.com/IntersectMBO/cardano-ledger/wiki/First-Block-of-Each-Era
  , shelleyPV
  , allegraPV
  , maryPV
  , alonzoPV
  , vasilPV
  , valentinePV
  , changPV
  , plominPV
  , pv11PV
  , newestPV
  , knownPVs
  , futurePV
  ) where

import Codec.Serialise (Serialise)
import GHC.Generics (Generic)
import Prettyprinter

{- Note [Adding new builtins: protocol versions]

  *** ATTENTION! *** New built-in functions must initially be added in a batch
  under `futurePV` in `builtinsAvailableIn` in `Common.Versions` and should only
  be moved to an earlier MajorProtocolVersion once they have been fully
  implemented and costed and their release under the relevant protocol version
  has been officially approved.  Remember to update the tests in `Spec.Versions`
  and `Spec.Data.Versions` when this happens.  If there are some builtins that
  are not to be released then leave them under `futurePV` (splitting the batch
  if necessary) and also make sure that the names of their cost model parameters
  come at the end of the `ParamName` types.
-}

{-| This represents the major component of the Cardano protocol version.
The ledger can only supply the major component of the protocol version, not the minor
component, and Plutus should only need to care about the major component anyway.
This relies on careful understanding between us and the ledger as to what this means. -}
newtype MajorProtocolVersion = MajorProtocolVersion {getMajorProtocolVersion :: Int}
  deriving newtype (Eq, Ord, Show, Serialise, Enum)
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

-- According to https://cardano.org/hardforks/, PV 6 was called "Lobster".

-- | The Vasil HF introduced the Babbage era and Plutus V2
vasilPV :: MajorProtocolVersion
vasilPV = MajorProtocolVersion 7

{-| Valentine was an intra-era HF where builtin functions @VerifyEcdsaSecp256k1Signature@ and
@VerifySchnorrSecp256k1Signature@ were enabled. -}
valentinePV :: MajorProtocolVersion
valentinePV = MajorProtocolVersion 8

-- | The Chang HF introduced the Conway era and Plutus V3
changPV :: MajorProtocolVersion
changPV = MajorProtocolVersion 9

{-| The Plomin HF was an intra-era HF where some new builtin functions were
introduced in Plutus V2 and V3. -}
plominPV :: MajorProtocolVersion
plominPV = MajorProtocolVersion 10

-- | Not sure what this is going to be called yet
pv11PV :: MajorProtocolVersion
pv11PV = MajorProtocolVersion 11

{-| The set of protocol versions that are "known", i.e. that have been released
and have actual differences associated with them.  This is currently only
used for testing, so efficiency is not parmount and a list is fine. -}
knownPVs :: [MajorProtocolVersion]
knownPVs =
  [ shelleyPV
  , allegraPV
  , maryPV
  , alonzoPV
  , vasilPV
  , valentinePV
  , changPV
  , plominPV
  , pv11PV
  ]

-- We're sometimes in an intermediate state where we've added new builtins but
-- not yet released them (but intend to). This is used by some of the tests to
-- decide what PVs the test should include.  UPDATE THIS when we're expecting to
-- release new builtins in a forthcoming PV.
newestPV :: MajorProtocolVersion
newestPV = pv11PV

{-| This is a placeholder for when we don't yet know what protocol version will
  be used for something. It's a very high protocol version that should never
  appear in reality.

  We should not assign names to future protocol versions until it's
  confirmed that they are correct, otherwise we could accidentally
  associate something with the wrong protocol version. -}
futurePV :: MajorProtocolVersion
futurePV = MajorProtocolVersion maxBound

{- Note [Mapping of protocol versions and ledger languages to semantics variants]
Semantics variants depend on both the protocol version and the ledger language.

Here's a table specifying the mapping in full:

  pv pre-Conway post-Conway
ll
1       A           B
2       A           B
3       C           C

I.e. for example

- post-Conway 'PlutusV1' corresponds to 'DefaultFunSemanticsVariantB'
- pre-Conway  'PlutusV2' corresponds to 'DefaultFunSemanticsVariantA'
- post-Conway 'PlutusV3' corresponds to 'DefaultFunSemanticsVariantC'
-}
