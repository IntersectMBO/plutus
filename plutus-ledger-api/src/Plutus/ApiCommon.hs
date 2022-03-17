{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-|
Common types and functions used across all the ledger API modules.
-}
module Plutus.ApiCommon where

import Data.ByteString.Short
import Data.Foldable (fold)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text
import PlutusCore as PLC
import Prettyprinter

-- | This represents the Cardano protocol version, with its major and minor components.
-- This relies on careful understanding between us and the ledger as to what this means.
data ProtocolVersion = ProtocolVersion { pvMajor :: Int, pvMinor :: Int }
  deriving stock (Show, Eq)

instance Ord ProtocolVersion where
    compare (ProtocolVersion major minor) (ProtocolVersion major' minor') = compare major major' <> compare minor minor'

instance Pretty ProtocolVersion where
    pretty (ProtocolVersion major minor) = pretty major <> "." <> pretty minor

-- | A simple toggle indicating whether or not we should produce logs.
data VerboseMode = Verbose | Quiet
    deriving stock (Eq)

-- | The type of log output: just a list of 'Text'.
type LogOutput = [Text]

-- | Scripts to the ledger are serialised bytestrings.
type SerializedScript = ShortByteString

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

-- | A map indicating which builtin functions were introduced in which 'ProtocolVersion'. Each builtin function should appear at most once.
--
-- This *must* be updated when new builtins are added.
-- See Note [New builtins and protocol versions]
builtinsIntroducedIn :: Map.Map ProtocolVersion (Set.Set PLC.DefaultFun)
builtinsIntroducedIn = Map.fromList [
  -- 5.0 is Alonzo
  (ProtocolVersion 5 0, Set.fromList [
          AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger,
          AppendByteString, ConsByteString, SliceByteString, LengthOfByteString, IndexByteString, EqualsByteString, LessThanByteString, LessThanEqualsByteString,
          Sha2_256, Sha3_256, Blake2b_256, VerifySignature,
          AppendString, EqualsString, EncodeUtf8, DecodeUtf8,
          IfThenElse,
          ChooseUnit,
          Trace,
          FstPair, SndPair,
          ChooseList, MkCons, HeadList, TailList, NullList,
          ChooseData, ConstrData, MapData, ListData, IData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData,
          MkPairData, MkNilData, MkNilPairData
          ]),
  (ProtocolVersion 6 0, Set.fromList [
          SerialiseData, VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature
          ])
  ]

-- | Which builtin functions are available in the given 'ProtocolVersion'?
--
-- See Note [New builtins and protocol versions]
builtinsAvailableIn :: ProtocolVersion -> Set.Set PLC.DefaultFun
builtinsAvailableIn pv = fold $ Map.elems $ Map.takeWhileAntitone (\introducedInPv -> introducedInPv <= pv) builtinsIntroducedIn
