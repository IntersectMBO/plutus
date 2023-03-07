-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
-- | This module contains the protocol versions and plutus versions as witnessed by the cardano ledger.
module PlutusLedgerApi.Common.Versions
    ( -- * Cardano Protocol versions
      module PlutusLedgerApi.Common.ProtocolVersions
      -- * Plutus versions
    , LedgerPlutusVersion (..)
      -- * Version-testing functions
    , languageIntroducedIn
    , languagesAvailableIn
    , builtinsIntroducedIn
    , builtinsAvailableIn
    ) where

import PlutusCore
import PlutusLedgerApi.Common.ProtocolVersions
import PlutusPrelude

import Data.Map qualified as Map
import Data.Set qualified as Set
import Prettyprinter

{- Note [New builtins and protocol versions]
When we add a new builtin to the Plutus language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

It would be nice, therefore, to get away with just having one definition of the set of builtin
functions. Then the new builtins will just "work". However, this neglects the fact that
the new builtins will be added to the builtin universe in the *software update* that
brings a new ledger Plutus version, but they should only be usable after the corresponding
*hard fork*. So there is a period of time in which they must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a builtin was introduced in.
- Given the protocol version, check a program for builtins that should not be usable yet.

Note that this doesn't currently handle removals of builtins, although it fairly straighforwardly
could do, just by tracking when they were removed.
-}

{-| The ledger Plutus versions. These are entirely different script languages from the ledger's perspective,
which on our side are interpreted in very similar ways.

It is a simple enumerated datatype (there is no major and minor components as in protocol version)
and the __ordering of constructors__ is essential for deriving Enum,Ord,Bounded.

IMPORTANT: this is different from the AST's `PlutusCore.Core.Type.Version`
-}
data LedgerPlutusVersion =
      PlutusV1 -- ^ introduced in shelley era
    | PlutusV2 -- ^ introduced in vasil era
    | PlutusV3 -- ^ not yet enabled, probably will be introduced in chang era
   deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance Pretty LedgerPlutusVersion where
    pretty = viaShow

{-| A map indicating which builtin functions were introduced in which 'ProtocolVersion'. Each builtin function should appear at most once.

This __must__ be updated when new builtins are added.
See Note [New builtins and protocol versions]
-}
builtinsIntroducedIn :: Map.Map (LedgerPlutusVersion, ProtocolVersion) (Set.Set DefaultFun)
builtinsIntroducedIn = Map.fromList [
  -- Alonzo is protocolversion=5.0
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
  -- Vasil is protocolversion=7.0
  ((PlutusV2, vasilPV), Set.fromList [
          SerialiseData
          ]),
  -- Chang is protocolversion=8.0
  ((PlutusV2, changPV), Set.fromList [
          VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature,
          IntegerToByteString, ByteStringToInteger,
          AndByteString, IorByteString, XorByteString, ComplementByteString,
          ShiftByteString, RotateByteString,
          TestBitByteString, WriteBitByteString,
          PopCountByteString, FindFirstSetByteString
          ])
  ]

{-| Query the protocol version that a specific ledger Plutus version was first introduced in.

/Introduction/ in this context means the enablement/allowance of scripts of that ledger Plutus version to be executed on-chain.
-}
languageIntroducedIn :: LedgerPlutusVersion -> ProtocolVersion
languageIntroducedIn = \case
    PlutusV1 -> alonzoPV
    PlutusV2 -> vasilPV
    PlutusV3 -> changPV

{-| Given a protocol version return a set of all available ledger Plutus versions that are enabled/allowed to run.

Assumes that the ledger Plutus versions once introduced/enabled, will never be disabled in the future.
-}
languagesAvailableIn :: ProtocolVersion -> Set.Set LedgerPlutusVersion
languagesAvailableIn searchPv =
    foldMap ledgerVersionToSet enumerate
  where
    -- OPTIMIZE: could be done faster using takeWhile
    ledgerVersionToSet :: LedgerPlutusVersion -> Set.Set LedgerPlutusVersion
    ledgerVersionToSet lv
        | languageIntroducedIn lv <= searchPv = Set.singleton lv
        | otherwise = mempty

{-| Which builtin functions are available in the given 'ProtocolVersion'?

See Note [New builtins and protocol versions]
-}
builtinsAvailableIn :: LedgerPlutusVersion -> ProtocolVersion -> Set.Set DefaultFun
builtinsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone builtinAvailableIn builtinsIntroducedIn
    where
      builtinAvailableIn :: (LedgerPlutusVersion, ProtocolVersion) -> Bool
      builtinAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv
