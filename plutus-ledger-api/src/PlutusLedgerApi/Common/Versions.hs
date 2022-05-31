-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
module PlutusLedgerApi.Common.Versions
    ( module PlutusLedgerApi.Common.ProtocolVersions
    , LedgerPlutusVersion (..)
    , builtinsIntroducedIn
    , builtinsAvailableIn
    ) where

import PlutusCore
import PlutusLedgerApi.Common.ProtocolVersions

import Data.Foldable
import Data.Map qualified as Map
import Data.Set qualified as Set
import Prettyprinter

{- Note [New builtins and protocol versions]
When we add a new builtin to the language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

It would be nice, therefore, to get away with just having one definition of the set of builtin
functions. Then the new builtins will just "work". However, this neglects the fact that
the new builtins will be added to the builtin universe in the *software update* that
brings a new version of Plutus, but they should only be usable after the corresponding
*hard fork*. So there is a period of time in which they must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a builtin was introduced in.
- Given the protocol version, check a program for builtins that should not be usable yet.

Note that this doesn't currently handle removals of builtins, although it fairly straighforwardly
could do, just by tracking when they were removed.
-}

-- | The plutus language version as seen from the ledger's side.
-- Note: the ordering of constructors matters for deriving Ord
data LedgerPlutusVersion =
      PlutusV1
    | PlutusV2
    | PlutusV3
   deriving stock (Eq, Ord, Show)

instance Pretty LedgerPlutusVersion where
    pretty = viaShow

{-| A map indicating which builtin functions were introduced in which 'ProtocolVersion'. Each builtin function should appear at most once.

This *must* be updated when new builtins are added.
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
          SerialiseData, VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature
          ])
  ]

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
