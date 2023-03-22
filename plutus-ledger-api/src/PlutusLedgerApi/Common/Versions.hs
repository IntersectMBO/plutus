-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{- | This module contains the code for handling the various kinds of version that we care about:

* Protocol versions
* Plutus ledger languages
* Plutus Core language versions
-}
module PlutusLedgerApi.Common.Versions
    ( -- * Cardano Protocol versions
      module PlutusLedgerApi.Common.ProtocolVersions
      -- * Plutus ledger languages
    , PlutusLedgerLanguage (..)
      -- * Plutus Core language versions
    , Version (..)
      -- * Version-testing functions
    , ledgerLanguageIntroducedIn
    , ledgerLanguagesAvailableIn
    , plcVersionsIntroducedIn
    , plcVersionsAvailableIn
    , builtinsIntroducedIn
    , builtinsAvailableIn
    ) where

import PlutusCore
import PlutusLedgerApi.Common.ProtocolVersions
import PlutusPrelude

import Data.Map qualified as Map
import Data.Set qualified as Set
import PlutusCore.Version (plcVersion100, plcVersion110)
import Prettyprinter

{- Note [New builtins/language versions and protocol versions]
When we add a new builtin to the Plutus language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

The same is true for new Plutus Core language versions: adding these is also backwards-compatible.

It would be nice, therefore, to get away with just having one definition of the set of builtin
functions/language features. Then the new features will just "work". However, this neglects the fact that
support for the new feature will be added in the *software update* that
brings a new Plutus ledger language, but they should only be usable after the corresponding
*hard fork*. So there is a period of time in which the feature must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a feature was introduced in.
- Given the protocol version, check a program for features that should not be usable yet.

To simplify our lives, we pervasively make the assumption that after a
feature is introduced in a ledger-language/protocol-version combo, it is present in all
later ledger-languages/protocol-versions.

Note that this doesn't currently handle removals, although it fairly straighforwardly
could do, just by tracking when they were removed.
-}

{-| The Plutus ledger language. These are entirely different script languages from the ledger's perspective,
which on our side are interpreted in very similar ways.

It is a simple enumerated datatype (there is no major and minor components as in protocol version)
and the __ordering of constructors__ is essential for deriving Enum,Ord,Bounded.

IMPORTANT: this is different from the Plutus Core language version, `PlutusCore.Version`
-}
data PlutusLedgerLanguage =
      PlutusV1 -- ^ introduced in shelley era
    | PlutusV2 -- ^ introduced in vasil era
    | PlutusV3 -- ^ not yet enabled
   deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance Pretty PlutusLedgerLanguage where
    pretty = viaShow

{-| A map indicating which builtin functions were introduced in which 'ProtocolVersion'.
Each builtin function should appear at most once.

This __must__ be updated when new builtins are added.
See Note [New builtins/language versions and protocol versions]
-}
builtinsIntroducedIn :: Map.Map (PlutusLedgerLanguage, ProtocolVersion) (Set.Set DefaultFun)
builtinsIntroducedIn = Map.fromList [
  ((PlutusV1, alonzoPV), Set.fromList [
          AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger,
          AppendByteString, ConsByteString, SliceByteString, LengthOfByteString, IndexByteString, EqualsByteString, LessThanByteString, LessThanEqualsByteString,
          Sha2_256, Sha3_256, Blake2b_256, VerifyEd25519Signature,
          AppendString, EqualsString, EncodeUtf8, DecodeUtf8,
          IfThenElse,
          ChooseUnit,
          Trace,
          FstPair, SndPair,
          ChooseList, MkCons, HeadList, TailList, NullList,
          ChooseData, ConstrData, MapData, ListData, IData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData,
          MkPairData, MkNilData, MkNilPairData
          ]),
  ((PlutusV2, vasilPV), Set.fromList [
          SerialiseData
          ]),
  ((PlutusV2, valentinePV), Set.fromList [
          VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature
          ]),
  ((PlutusV3, futurePV), Set.fromList [
          Bls12_381_G1_add, Bls12_381_G1_neg, Bls12_381_G1_scalarMul,
          Bls12_381_G1_equal, Bls12_381_G1_hashToGroup,
          Bls12_381_G1_compress, Bls12_381_G1_uncompress,
          Bls12_381_G2_add, Bls12_381_G2_neg, Bls12_381_G2_scalarMul,
          Bls12_381_G2_equal, Bls12_381_G2_hashToGroup,
          Bls12_381_G2_compress, Bls12_381_G2_uncompress,
          Bls12_381_millerLoop, Bls12_381_mulMlResult, Bls12_381_finalVerify
          ])
  ]

{-| A map indicating which Plutus Core versions were introduced in which
'ProtocolVersion' and 'PlutusLedgerLanguage'. Each version should appear at most once.

This __must__ be updated when new versions are added.
See Note [New builtins/language versions and protocol versions]
-}
plcVersionsIntroducedIn :: Map.Map (PlutusLedgerLanguage, ProtocolVersion) (Set.Set Version)
plcVersionsIntroducedIn = Map.fromList [
  ((PlutusV1, alonzoPV), Set.fromList [ plcVersion100 ]),
  ((PlutusV3, futurePV), Set.fromList [ plcVersion110 ])
  ]

{-| Query the protocol version that a specific Plutus ledger language was first introduced in.
-}
ledgerLanguageIntroducedIn :: PlutusLedgerLanguage -> ProtocolVersion
ledgerLanguageIntroducedIn = \case
    PlutusV1 -> alonzoPV
    PlutusV2 -> vasilPV
    PlutusV3 -> futurePV

{-| Which Plutus language versions are available in the given 'ProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
ledgerLanguagesAvailableIn :: ProtocolVersion -> Set.Set PlutusLedgerLanguage
ledgerLanguagesAvailableIn searchPv =
    foldMap ledgerVersionToSet enumerate
  where
    -- OPTIMIZE: could be done faster using takeWhile
    ledgerVersionToSet :: PlutusLedgerLanguage -> Set.Set PlutusLedgerLanguage
    ledgerVersionToSet lv
        | ledgerLanguageIntroducedIn lv <= searchPv = Set.singleton lv
        | otherwise = mempty

{-| Which Plutus Core language versions are available in the given 'PlutusLedgerLanguage'
and 'ProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
plcVersionsAvailableIn :: PlutusLedgerLanguage -> ProtocolVersion -> Set.Set Version
plcVersionsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone plcVersionAvailableIn plcVersionsIntroducedIn
    where
      plcVersionAvailableIn :: (PlutusLedgerLanguage, ProtocolVersion) -> Bool
      plcVersionAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv

{-| Which builtin functions are available in the given given 'PlutusLedgerLanguage'
and 'ProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
builtinsAvailableIn :: PlutusLedgerLanguage -> ProtocolVersion -> Set.Set DefaultFun
builtinsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone builtinAvailableIn builtinsIntroducedIn
    where
      builtinAvailableIn :: (PlutusLedgerLanguage, ProtocolVersion) -> Bool
      builtinAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv
