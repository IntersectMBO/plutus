-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase     #-}

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

import Codec.Serialise.Class (Serialise)
import Data.Map qualified as Map
import Data.Set qualified as Set
import NoThunks.Class (NoThunks)
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

See also Note [Adding new builtins: protocol versions].
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
   deriving anyclass (NFData, NoThunks, Serialise)

instance Pretty PlutusLedgerLanguage where
    pretty = viaShow

-- Batches of builtins which were introduced at the same time: see
-- `builtinsIntroducedIn` below.
batch1 :: [DefaultFun]
batch1 =
  [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger
  , RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger
  , AppendByteString, ConsByteString, SliceByteString, LengthOfByteString
  , IndexByteString, EqualsByteString, LessThanByteString, LessThanEqualsByteString
  , Sha2_256, Sha3_256, Blake2b_256, VerifyEd25519Signature, AppendString, EqualsString
  , EncodeUtf8, DecodeUtf8, IfThenElse, ChooseUnit, Trace, FstPair, SndPair, ChooseList
  , MkCons, HeadList, TailList, NullList, ChooseData, ConstrData, MapData, ListData
  , IData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData
  , MkPairData, MkNilData, MkNilPairData
  ]

batch2 :: [DefaultFun]
batch2 =
  [ SerialiseData ]

batch3 :: [DefaultFun]
batch3 =
  [ VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature ]

-- `cekCase` and `cekConstr` costs come between Batch 3 and Batch 4 in the
-- PlutusV3 cost model parameters, although that's irrelevant here.

-- batch4, excluding IntegerToByteString and ByteStringToInteger.
batch4a :: [DefaultFun]
batch4a =
  [ Bls12_381_G1_add, Bls12_381_G1_neg, Bls12_381_G1_scalarMul
  , Bls12_381_G1_equal, Bls12_381_G1_hashToGroup
  , Bls12_381_G1_compress, Bls12_381_G1_uncompress
  , Bls12_381_G2_add, Bls12_381_G2_neg, Bls12_381_G2_scalarMul
  , Bls12_381_G2_equal, Bls12_381_G2_hashToGroup
  , Bls12_381_G2_compress, Bls12_381_G2_uncompress
  , Bls12_381_millerLoop, Bls12_381_mulMlResult, Bls12_381_finalVerify
  , Keccak_256, Blake2b_224
  ]

{- batch4b: IntegerToByteString and ByteStringToInteger.  These were enabled in
PlutusV2 at PV10 in #6056 and #6065.  They are available on the chain, but
they're prohibitively expensive because the proposal to update the relevant
protocol parameters has not (yet) been enacted.  This has left a "gap" in the
cost model paramters: for PlutusV3, the parameters for Batch 3 are followed
those for 4a, then 4b, but for PlutusV2 those for Batch3 are followed by those
for Batch 4b, and those for 4a aren't in use yet.  Since you can't actually use
the 4b builtins in PlutusV2 at the moment, it's tempting to insert the 4a
parameter before the 4b parameters and enable them all at PV11 and with a
suitable parameter update.  However, if we do do this there's a theoretical risk
of turning a phase 2 failure into a phase 1 failure: would that be problematic?
-}
batch4b :: [DefaultFun]
batch4b =
  [ IntegerToByteString, ByteStringToInteger ]

batch4 :: [DefaultFun]
batch4 = batch4a ++ batch4b

batch5 :: [DefaultFun]
batch5 =
  [ AndByteString, OrByteString, XorByteString, ComplementByteString
  , ReadBit, WriteBits, ReplicateByte
  , ShiftByteString, RotateByteString, CountSetBits, FindFirstSetBit
  , Ripemd_160
  ]

batch6 :: [DefaultFun]
batch6 =
  [ ExpModInteger, DropList
  , ListToArray, IndexArray, LengthOfArray
  ]

{-| A map indicating which builtin functions were introduced in which 'MajorProtocolVersion'.

This __must__ be updated when new builtins are added.
See Note [New builtins/language versions and protocol versions]

All builtins will become available in all protocol versions from `anonPV` onwards.
-}
builtinsIntroducedIn :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set DefaultFun)
builtinsIntroducedIn =
  Map.fromList [
  -- PlutusV1
    ((PlutusV1, alonzoPV),    Set.fromList batch1)
  , ((PlutusV1, anonPV),      Set.fromList (batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6))
  -- PlutusV2
  , ((PlutusV2, vasilPV),     Set.fromList batch2)
  , ((PlutusV2, valentinePV), Set.fromList batch3)
  , ((PlutusV2, plominPV),    Set.fromList batch4b)
  , ((PlutusV2, anonPV),      Set.fromList (batch4a ++ batch5 ++ batch6))
  -- PlutusV3
  , ((PlutusV3, changPV),     Set.fromList batch4)
  , ((PlutusV3, plominPV),    Set.fromList batch5)
  , ((PlutusV3, anonPV),      Set.fromList batch6)
  ]


-- I THINK THIS IS BROKEN NOW: we assume that if something's introduced in eg V1
-- then it's available in V2 and V3 as well, but introducing 1.1.0 for V2 in Anon
-- may confuse it about when it's introduced for V3
--
{-| A map indicating which Plutus Core versions were introduced in which
'MajorProtocolVersion' and 'PlutusLedgerLanguage'. Each version should appear at most once.

This __must__ be updated when new versions are added.
See Note [New builtins/language versions and protocol versions]
-}

{-
-- ** This should probably be something like
-- Map.Map PlutusLedgerLanguage (Map.Map MajorProtocolVersion) (Set.Set Version))
plcVersionsIntroducedIn :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set Version)
plcVersionsIntroducedIn =
  Map.fromList [
    ((PlutusV1, alonzoPV), Set.fromList [ plcVersion100 ])
  , ((PlutusV3, changPV),  Set.fromList [ plcVersion110 ])
  , ((PlutusV1, anonPV),   Set.fromList [ plcVersion110 ])
  ]
-}

{-
plcVersionsIntroducedIn :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set Version)
 plcVersionsIntroducedIn =
   Map.fromList [
     ((PlutusV1, alonzoPV), Set.fromList [ plcVersion100 ])
   , ((PlutusV3, changPV),  Set.fromList [ plcVersion110 ])
   , ((PlutusV1, anonPV),   Set.fromList [ plcVersion110 ])
  ]


plcVersionsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone plcVersionAvailableIn plcVersionsIntroducedIn
    where
      plcVersionAvailableIn :: (PlutusLedgerLanguage, MajorProtocolVersion) -> Bool
      plcVersionAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv
-}

plcVersionsIntroducedIn :: Map.Map PlutusLedgerLanguage (Map.Map MajorProtocolVersion (Set.Set Version))
plcVersionsIntroducedIn =
  Map.fromList [
    (PlutusV1, Map.fromList [(alonzoPV, Set.fromList [ plcVersion100 ]), (anonPV, Set.fromList [plcVersion110])])
  , (PlutusV2, Map.fromList [(alonzoPV, Set.fromList [ plcVersion100 ]), (anonPV, Set.fromList [plcVersion110])])
  , (PlutusV3, Map.fromList [(changPV,  Set.fromList [ plcVersion110 ])])
  ]

{-| Query the protocol version that a specific Plutus ledger language was first introduced in.
-}
ledgerLanguageIntroducedIn :: PlutusLedgerLanguage -> MajorProtocolVersion
ledgerLanguageIntroducedIn = \case
    PlutusV1 -> alonzoPV
    PlutusV2 -> vasilPV
    PlutusV3 -> changPV

{-| Which Plutus language versions are available in the given 'MajorProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
ledgerLanguagesAvailableIn :: MajorProtocolVersion -> Set.Set PlutusLedgerLanguage
ledgerLanguagesAvailableIn searchPv =
    foldMap ledgerVersionToSet enumerate
  where
    -- OPTIMIZE: could be done faster using takeWhile
    ledgerVersionToSet :: PlutusLedgerLanguage -> Set.Set PlutusLedgerLanguage
    ledgerVersionToSet ll
        | ledgerLanguageIntroducedIn ll <= searchPv = Set.singleton ll
        | otherwise = mempty

{-| Which Plutus Core language versions are available in the given 'PlutusLedgerLanguage'
and 'MajorProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
plcVersionsAvailableIn :: PlutusLedgerLanguage -> MajorProtocolVersion -> Set.Set Version
plcVersionsAvailableIn thisLv thisPv =
  fold $ -- ie, union
  Map.elems $ Map.takeWhileAntitone (<= thisPv) $
  Map.findWithDefault Map.empty thisLv plcVersionsIntroducedIn

{-| Which builtin functions are available in the given given 'PlutusLedgerLanguage'
and 'MajorProtocolVersion'?

See Note [New builtins/language versions and protocol versions]
-}
builtinsAvailableIn :: PlutusLedgerLanguage -> MajorProtocolVersion -> Set.Set DefaultFun
builtinsAvailableIn thisLv thisPv = fold $
    Map.filterWithKey (const . alreadyIntroduced) builtinsIntroducedIn
    where
      alreadyIntroduced :: (PlutusLedgerLanguage, MajorProtocolVersion) -> Bool
      alreadyIntroduced (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv

{-
i < j => p i >= p j
ie, if p i is true and i < j then p j can be true or false, if p i is false and j > i then p j must also be false.
-}
-- ** We can probably assume (for now) that if a builtin or laguage feature is
-- introduced for a particular Plutus LL version, then it'll also be available
-- _for that version_ in all later PVs.  What is no longer true is that if
-- something's introduced in PlutusV<n> then it won't be introduced in a PlutusV<m>
-- with m < n at a later PV.
