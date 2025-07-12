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
    , batch1
    , batch2
    , batch3
    , batch4a
    , batch4b
    , batch5
    , batch6
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

Abbreviations: LL = ledger language, PV = (major) protocol version.

When we add a new builtin to the Plutus language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

The same is true for new Plutus Core language versions: adding these is also backwards-compatible.

It would be nice, therefore, to get away with just having one definition of the
set of builtin functions/language features. Then the new features will just
"work". However, this neglects the fact that support for the new feature will be
added in the *software update* that brings a new Plutus ledger language, but
they should only be usable after the corresponding *hard fork*. So there is a
period of time in which the feature must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a feature was introduced in.
- Given the protocol version, check a program for features that should not be usable yet.

To simplify our lives, we pervasively make the assumption that after a feature
is introduced in a particular ledger language and protocol version, it remains
present in the same ledger language in all later protocol versions (but not
necessarily in other ledger languages; there was previously an assumption that
if a feature was available in a given LL then it would also be available in all
later LLs, but this led to complications when we retrospectively introduced
certain features in earlier LLs).

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
      PlutusV1 -- ^ introduced in Alonzo HF
    | PlutusV2 -- ^ introduced in Vasil HF
    | PlutusV3 -- ^ introduced in Chang HF
   deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)
   deriving anyclass (NFData, NoThunks, Serialise)

instance Pretty PlutusLedgerLanguage where
    pretty = viaShow

{-| Query the protocol version that a specific Plutus ledger language was first introduced in.
-}
ledgerLanguageIntroducedIn :: PlutusLedgerLanguage -> MajorProtocolVersion
ledgerLanguageIntroducedIn = \case
    PlutusV1 -> alonzoPV
    PlutusV2 -> vasilPV
    PlutusV3 -> changPV

{-| Which Plutus language versions are available in the given
'MajorProtocolVersion'?
See Note [New builtins/language versions and protocol versions].
Assumes that once a LL is available it remains available in all later
PVs and that if m <= n, PlutusVm is introduced before PlutusVn.
-}
ledgerLanguagesAvailableIn :: MajorProtocolVersion -> Set.Set PlutusLedgerLanguage
ledgerLanguagesAvailableIn searchPv =
  Set.fromList $ takeWhile (\ll -> ledgerLanguageIntroducedIn ll <= searchPv) enumerate

-- | Given a map from PVs to a type `a`, return a `Set a` containing all of the
-- entries with PV <= thisPv
collectUpTo
  :: Ord a
  => Map.Map MajorProtocolVersion (Set.Set a)
  -> MajorProtocolVersion
  -> Set.Set a
collectUpTo m thisPv =
  fold $  -- ie, iterated `union`
  Map.elems $ Map.takeWhileAntitone (<= thisPv) m

-- Batches of builtins which were introduced in the same hard fork (but perhaps
-- not for all LLs): see the Plutus Core specification and
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
-- or fmap toEnum [0..50] etc.

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
 PlutusV3 at PV9, along with batch4a, They were enabled in PlutusV2 at PV10 in
 #6056 and #6065.  They are available on the chain, but they're prohibitively
 expensive because the proposal to update the relevant protocol parameters has
 not (yet) been enacted.  This has left a "gap" in the cost model paramters: for
 PlutusV3, the parameters for Batch 3 are followed those for 4a, then 4b, but
 for PlutusV2 those for Batch3 are followed by those for Batch 4a, and those for
 4b aren't in use yet.  Since you can't actually use the 4b builtins in PlutusV2
 at the moment, it's tempting to insert the 4a parameter before the 4b
 parameters and enable them all at PV11 and with a suitable parameter update.
 However, if we do do this there's a theoretical risk of turning a phase 2
 failure into a phase 1 failure: would that be problematic?
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

{-| Given a ledger language, return a map indicating which builtin functions were
  introduced in which 'MajorProtocolVersion'.  This __must__ be updated when new
  builtins are added.  It is not necessary to add entries for protocol versions
  where no new builtins are added.  See Note [New builtins/language versions and
  protocol versions]
-}
builtinsIntroducedIn :: PlutusLedgerLanguage -> Map.Map MajorProtocolVersion (Set.Set DefaultFun)
builtinsIntroducedIn =
  \case
    PlutusV1 ->
      Map.fromList
      [ (alonzoPV, Set.fromList batch1)
      , (anonPV,   Set.fromList (batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6))
      ]
    PlutusV2 ->
      Map.fromList
      [ (vasilPV,     Set.fromList (batch1 ++ batch2))
      , (valentinePV, Set.fromList batch3)
      , (plominPV,    Set.fromList batch4b)
      , (anonPV ,     Set.fromList (batch4a ++ batch5 ++ batch6))
      ]
    PlutusV3 ->
      Map.fromList
      [ (changPV,  Set.fromList (batch1 ++ batch2 ++ batch3 ++ batch4))
      , (plominPV, Set.fromList batch5)
      , (anonPV,   Set.fromList batch6)
      ]

{- | Return a set containing the builtins which are available in a given LL in a
given PV.  All builtins are available in all LLs from `anonPV` onwards. -}
builtinsAvailableIn :: PlutusLedgerLanguage -> MajorProtocolVersion -> Set.Set DefaultFun
builtinsAvailableIn = collectUpTo . builtinsIntroducedIn


{-| A map indicating which Plutus Core versions were introduced in which
'MajorProtocolVersion' and 'PlutusLedgerLanguage'. Each version should appear at most once.
This __must__ be updated when new versions are added.
See Note [New builtins/language versions and protocol versions]
-}
plcVersionsIntroducedIn :: PlutusLedgerLanguage -> Map.Map MajorProtocolVersion (Set.Set Version)
plcVersionsIntroducedIn =
  \case
    PlutusV1 ->
      Map.fromList
      [ (alonzoPV, Set.fromList [ plcVersion100 ])
      , (anonPV,   Set.fromList [ plcVersion110 ])
      ]
    PlutusV2 ->
      Map.fromList
      [ (alonzoPV, Set.fromList [ plcVersion100 ])
      , (anonPV,   Set.fromList [ plcVersion110 ])
      ]
    PlutusV3 ->
      Map.fromList
      [(changPV, Set.fromList [ plcVersion110 ])
      ]

{-| Which Plutus Core language versions are available in the given 'PlutusLedgerLanguage'
and 'MajorProtocolVersion'? -}
plcVersionsAvailableIn :: PlutusLedgerLanguage -> MajorProtocolVersion -> Set.Set Version
plcVersionsAvailableIn = collectUpTo . plcVersionsIntroducedIn
