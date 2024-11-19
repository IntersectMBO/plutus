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

{-| A map indicating which builtin functions were introduced in which 'MajorProtocolVersion'.

This __must__ be updated when new builtins are added.
See Note [New builtins/language versions and protocol versions]
-}
builtinsIntroducedIn :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set DefaultFun)
builtinsIntroducedIn = Map.fromList [
  ((PlutusV1, alonzoPV), Set.fromList [
          AddInteger, AddInteger1, AddInteger2, AddInteger3, AddInteger4, AddInteger5, AddInteger6, AddInteger7, AddInteger8, AddInteger9, SubtractInteger, SubtractInteger1, SubtractInteger2, SubtractInteger3, SubtractInteger4, SubtractInteger5, SubtractInteger6, SubtractInteger7, SubtractInteger8, SubtractInteger9, MultiplyInteger, MultiplyInteger1, MultiplyInteger2, MultiplyInteger3, MultiplyInteger4, MultiplyInteger5, MultiplyInteger6, MultiplyInteger7, MultiplyInteger8, MultiplyInteger9, DivideInteger, DivideInteger1, DivideInteger2, DivideInteger3, DivideInteger4, DivideInteger5, DivideInteger6, DivideInteger7, DivideInteger8, DivideInteger9, QuotientInteger, QuotientInteger1, QuotientInteger2, QuotientInteger3, QuotientInteger4, QuotientInteger5, QuotientInteger6, QuotientInteger7, QuotientInteger8, QuotientInteger9, RemainderInteger, RemainderInteger1, RemainderInteger2, RemainderInteger3, RemainderInteger4, RemainderInteger5, RemainderInteger6, RemainderInteger7, RemainderInteger8, RemainderInteger9, ModInteger, ModInteger1, ModInteger2, ModInteger3, ModInteger4, ModInteger5, ModInteger6, ModInteger7, ModInteger8, ModInteger9, EqualsInteger, EqualsInteger1, EqualsInteger2, EqualsInteger3, EqualsInteger4, EqualsInteger5, EqualsInteger6, EqualsInteger7, EqualsInteger8, EqualsInteger9, LessThanInteger, LessThanInteger1, LessThanInteger2, LessThanInteger3, LessThanInteger4, LessThanInteger5, LessThanInteger6, LessThanInteger7, LessThanInteger8, LessThanInteger9, LessThanEqualsInteger, LessThanEqualsInteger1, LessThanEqualsInteger2, LessThanEqualsInteger3, LessThanEqualsInteger4, LessThanEqualsInteger5, LessThanEqualsInteger6, LessThanEqualsInteger7, LessThanEqualsInteger8, LessThanEqualsInteger9,
          AppendByteString, AppendByteString1, AppendByteString2, AppendByteString3, AppendByteString4, AppendByteString5, AppendByteString6, AppendByteString7, AppendByteString8, AppendByteString9, ConsByteString, ConsByteString1, ConsByteString2, ConsByteString3, ConsByteString4, ConsByteString5, ConsByteString6, ConsByteString7, ConsByteString8, ConsByteString9, SliceByteString, SliceByteString1, SliceByteString2, SliceByteString3, SliceByteString4, SliceByteString5, SliceByteString6, SliceByteString7, SliceByteString8, SliceByteString9, LengthOfByteString, LengthOfByteString1, LengthOfByteString2, LengthOfByteString3, LengthOfByteString4, LengthOfByteString5, LengthOfByteString6, LengthOfByteString7, LengthOfByteString8, LengthOfByteString9, IndexByteString, IndexByteString1, IndexByteString2, IndexByteString3, IndexByteString4, IndexByteString5, IndexByteString6, IndexByteString7, IndexByteString8, IndexByteString9, EqualsByteString, EqualsByteString1, EqualsByteString2, EqualsByteString3, EqualsByteString4, EqualsByteString5, EqualsByteString6, EqualsByteString7, EqualsByteString8, EqualsByteString9, LessThanByteString, LessThanByteString1, LessThanByteString2, LessThanByteString3, LessThanByteString4, LessThanByteString5, LessThanByteString6, LessThanByteString7, LessThanByteString8, LessThanByteString9, LessThanEqualsByteString, LessThanEqualsByteString1, LessThanEqualsByteString2, LessThanEqualsByteString3, LessThanEqualsByteString4, LessThanEqualsByteString5, LessThanEqualsByteString6, LessThanEqualsByteString7, LessThanEqualsByteString8, LessThanEqualsByteString9,
          Sha2_256, Sha2_2561, Sha2_2562, Sha2_2563, Sha2_2564, Sha2_2565, Sha2_2566, Sha2_2567, Sha2_2568, Sha2_2569, Sha3_256, Sha3_2561, Sha3_2562, Sha3_2563, Sha3_2564, Sha3_2565, Sha3_2566, Sha3_2567, Sha3_2568, Sha3_2569, Blake2b_256, Blake2b_2561, Blake2b_2562, Blake2b_2563, Blake2b_2564, Blake2b_2565, Blake2b_2566, Blake2b_2567, Blake2b_2568, Blake2b_2569, VerifyEd25519Signature, VerifyEd25519Signature1, VerifyEd25519Signature2, VerifyEd25519Signature3, VerifyEd25519Signature4, VerifyEd25519Signature5, VerifyEd25519Signature6, VerifyEd25519Signature7, VerifyEd25519Signature8, VerifyEd25519Signature9,
          AppendString, AppendString1, AppendString2, AppendString3, AppendString4, AppendString5, AppendString6, AppendString7, AppendString8, AppendString9, EqualsString, EqualsString1, EqualsString2, EqualsString3, EqualsString4, EqualsString5, EqualsString6, EqualsString7, EqualsString8, EqualsString9, EncodeUtf8, EncodeUtf81, EncodeUtf82, EncodeUtf83, EncodeUtf84, EncodeUtf85, EncodeUtf86, EncodeUtf87, EncodeUtf88, EncodeUtf89, DecodeUtf8, DecodeUtf81, DecodeUtf82, DecodeUtf83, DecodeUtf84, DecodeUtf85, DecodeUtf86, DecodeUtf87, DecodeUtf88, DecodeUtf89,
          IfThenElse, IfThenElse1, IfThenElse2, IfThenElse3, IfThenElse4, IfThenElse5, IfThenElse6, IfThenElse7, IfThenElse8, IfThenElse9,
          ChooseUnit, ChooseUnit1, ChooseUnit2, ChooseUnit3, ChooseUnit4, ChooseUnit5, ChooseUnit6, ChooseUnit7, ChooseUnit8, ChooseUnit9,
          Trace, Trace1, Trace2, Trace3, Trace4, Trace5, Trace6, Trace7, Trace8, Trace9,
          FstPair, FstPair1, FstPair2, FstPair3, FstPair4, FstPair5, FstPair6, FstPair7, FstPair8, FstPair9, SndPair, SndPair1, SndPair2, SndPair3, SndPair4, SndPair5, SndPair6, SndPair7, SndPair8, SndPair9,
          ChooseList, ChooseList1, ChooseList2, ChooseList3, ChooseList4, ChooseList5, ChooseList6, ChooseList7, ChooseList8, ChooseList9, MkCons, MkCons1, MkCons2, MkCons3, MkCons4, MkCons5, MkCons6, MkCons7, MkCons8, MkCons9, HeadList, HeadList1, HeadList2, HeadList3, HeadList4, HeadList5, HeadList6, HeadList7, HeadList8, HeadList9, TailList, TailList1, TailList2, TailList3, TailList4, TailList5, TailList6, TailList7, TailList8, TailList9, NullList, NullList1, NullList2, NullList3, NullList4, NullList5, NullList6, NullList7, NullList8, NullList9,
          ChooseData, ChooseData1, ChooseData2, ChooseData3, ChooseData4, ChooseData5, ChooseData6, ChooseData7, ChooseData8, ChooseData9, ConstrData, ConstrData1, ConstrData2, ConstrData3, ConstrData4, ConstrData5, ConstrData6, ConstrData7, ConstrData8, ConstrData9, MapData, MapData1, MapData2, MapData3, MapData4, MapData5, MapData6, MapData7, MapData8, MapData9, ListData, ListData1, ListData2, ListData3, ListData4, ListData5, ListData6, ListData7, ListData8, ListData9, IData, IData1, IData2, IData3, IData4, IData5, IData6, IData7, IData8, IData9, BData, BData1, BData2, BData3, BData4, BData5, BData6, BData7, BData8, BData9, UnConstrData, UnConstrData1, UnConstrData2, UnConstrData3, UnConstrData4, UnConstrData5, UnConstrData6, UnConstrData7, UnConstrData8, UnConstrData9, UnMapData, UnMapData1, UnMapData2, UnMapData3, UnMapData4, UnMapData5, UnMapData6, UnMapData7, UnMapData8, UnMapData9, UnListData, UnListData1, UnListData2, UnListData3, UnListData4, UnListData5, UnListData6, UnListData7, UnListData8, UnListData9, UnIData, UnIData1, UnIData2, UnIData3, UnIData4, UnIData5, UnIData6, UnIData7, UnIData8, UnIData9, UnBData, UnBData1, UnBData2, UnBData3, UnBData4, UnBData5, UnBData6, UnBData7, UnBData8, UnBData9, EqualsData, EqualsData1, EqualsData2, EqualsData3, EqualsData4, EqualsData5, EqualsData6, EqualsData7, EqualsData8, EqualsData9,
          MkPairData, MkPairData1, MkPairData2, MkPairData3, MkPairData4, MkPairData5, MkPairData6, MkPairData7, MkPairData8, MkPairData9, MkNilData, MkNilData1, MkNilData2, MkNilData3, MkNilData4, MkNilData5, MkNilData6, MkNilData7, MkNilData8, MkNilData9, MkNilPairData, MkNilPairData1, MkNilPairData2, MkNilPairData3, MkNilPairData4, MkNilPairData5, MkNilPairData6, MkNilPairData7, MkNilPairData8, MkNilPairData9
          ]),
  ((PlutusV2, vasilPV), Set.fromList [
          SerialiseData, SerialiseData1, SerialiseData2, SerialiseData3, SerialiseData4, SerialiseData5, SerialiseData6, SerialiseData7, SerialiseData8, SerialiseData9
          ]),
  ((PlutusV2, valentinePV), Set.fromList [
          VerifyEcdsaSecp256k1Signature, VerifyEcdsaSecp256k1Signature1, VerifyEcdsaSecp256k1Signature2, VerifyEcdsaSecp256k1Signature3, VerifyEcdsaSecp256k1Signature4, VerifyEcdsaSecp256k1Signature5, VerifyEcdsaSecp256k1Signature6, VerifyEcdsaSecp256k1Signature7, VerifyEcdsaSecp256k1Signature8, VerifyEcdsaSecp256k1Signature9, VerifySchnorrSecp256k1Signature, VerifySchnorrSecp256k1Signature1, VerifySchnorrSecp256k1Signature2, VerifySchnorrSecp256k1Signature3, VerifySchnorrSecp256k1Signature4, VerifySchnorrSecp256k1Signature5, VerifySchnorrSecp256k1Signature6, VerifySchnorrSecp256k1Signature7, VerifySchnorrSecp256k1Signature8, VerifySchnorrSecp256k1Signature9
          ]),
  ((PlutusV2, changPlus1PV), Set.fromList [
          IntegerToByteString, IntegerToByteString1, IntegerToByteString2, IntegerToByteString3, IntegerToByteString4, IntegerToByteString5, IntegerToByteString6, IntegerToByteString7, IntegerToByteString8, IntegerToByteString9, ByteStringToInteger, ByteStringToInteger1, ByteStringToInteger2, ByteStringToInteger3, ByteStringToInteger4, ByteStringToInteger5, ByteStringToInteger6, ByteStringToInteger7, ByteStringToInteger8, ByteStringToInteger9
          ]),
  ((PlutusV3, changPV), Set.fromList [
          Bls12_381_G1_add, Bls12_381_G1_add1, Bls12_381_G1_add2, Bls12_381_G1_add3, Bls12_381_G1_add4, Bls12_381_G1_add5, Bls12_381_G1_add6, Bls12_381_G1_add7, Bls12_381_G1_add8, Bls12_381_G1_add9, Bls12_381_G1_neg, Bls12_381_G1_neg1, Bls12_381_G1_neg2, Bls12_381_G1_neg3, Bls12_381_G1_neg4, Bls12_381_G1_neg5, Bls12_381_G1_neg6, Bls12_381_G1_neg7, Bls12_381_G1_neg8, Bls12_381_G1_neg9, Bls12_381_G1_scalarMul, Bls12_381_G1_scalarMul1, Bls12_381_G1_scalarMul2, Bls12_381_G1_scalarMul3, Bls12_381_G1_scalarMul4, Bls12_381_G1_scalarMul5, Bls12_381_G1_scalarMul6, Bls12_381_G1_scalarMul7, Bls12_381_G1_scalarMul8, Bls12_381_G1_scalarMul9,
          Bls12_381_G1_equal, Bls12_381_G1_equal1, Bls12_381_G1_equal2, Bls12_381_G1_equal3, Bls12_381_G1_equal4, Bls12_381_G1_equal5, Bls12_381_G1_equal6, Bls12_381_G1_equal7, Bls12_381_G1_equal8, Bls12_381_G1_equal9, Bls12_381_G1_hashToGroup, Bls12_381_G1_hashToGroup1, Bls12_381_G1_hashToGroup2, Bls12_381_G1_hashToGroup3, Bls12_381_G1_hashToGroup4, Bls12_381_G1_hashToGroup5, Bls12_381_G1_hashToGroup6, Bls12_381_G1_hashToGroup7, Bls12_381_G1_hashToGroup8, Bls12_381_G1_hashToGroup9,
          Bls12_381_G1_compress, Bls12_381_G1_compress1, Bls12_381_G1_compress2, Bls12_381_G1_compress3, Bls12_381_G1_compress4, Bls12_381_G1_compress5, Bls12_381_G1_compress6, Bls12_381_G1_compress7, Bls12_381_G1_compress8, Bls12_381_G1_compress9, Bls12_381_G1_uncompress, Bls12_381_G1_uncompress1, Bls12_381_G1_uncompress2, Bls12_381_G1_uncompress3, Bls12_381_G1_uncompress4, Bls12_381_G1_uncompress5, Bls12_381_G1_uncompress6, Bls12_381_G1_uncompress7, Bls12_381_G1_uncompress8, Bls12_381_G1_uncompress9,
          Bls12_381_G2_add, Bls12_381_G2_add1, Bls12_381_G2_add2, Bls12_381_G2_add3, Bls12_381_G2_add4, Bls12_381_G2_add5, Bls12_381_G2_add6, Bls12_381_G2_add7, Bls12_381_G2_add8, Bls12_381_G2_add9, Bls12_381_G2_neg, Bls12_381_G2_neg1, Bls12_381_G2_neg2, Bls12_381_G2_neg3, Bls12_381_G2_neg4, Bls12_381_G2_neg5, Bls12_381_G2_neg6, Bls12_381_G2_neg7, Bls12_381_G2_neg8, Bls12_381_G2_neg9, Bls12_381_G2_scalarMul, Bls12_381_G2_scalarMul1, Bls12_381_G2_scalarMul2, Bls12_381_G2_scalarMul3, Bls12_381_G2_scalarMul4, Bls12_381_G2_scalarMul5, Bls12_381_G2_scalarMul6, Bls12_381_G2_scalarMul7, Bls12_381_G2_scalarMul8, Bls12_381_G2_scalarMul9,
          Bls12_381_G2_equal, Bls12_381_G2_equal1, Bls12_381_G2_equal2, Bls12_381_G2_equal3, Bls12_381_G2_equal4, Bls12_381_G2_equal5, Bls12_381_G2_equal6, Bls12_381_G2_equal7, Bls12_381_G2_equal8, Bls12_381_G2_equal9, Bls12_381_G2_hashToGroup, Bls12_381_G2_hashToGroup1, Bls12_381_G2_hashToGroup2, Bls12_381_G2_hashToGroup3, Bls12_381_G2_hashToGroup4, Bls12_381_G2_hashToGroup5, Bls12_381_G2_hashToGroup6, Bls12_381_G2_hashToGroup7, Bls12_381_G2_hashToGroup8, Bls12_381_G2_hashToGroup9,
          Bls12_381_G2_compress, Bls12_381_G2_compress1, Bls12_381_G2_compress2, Bls12_381_G2_compress3, Bls12_381_G2_compress4, Bls12_381_G2_compress5, Bls12_381_G2_compress6, Bls12_381_G2_compress7, Bls12_381_G2_compress8, Bls12_381_G2_compress9, Bls12_381_G2_uncompress, Bls12_381_G2_uncompress1, Bls12_381_G2_uncompress2, Bls12_381_G2_uncompress3, Bls12_381_G2_uncompress4, Bls12_381_G2_uncompress5, Bls12_381_G2_uncompress6, Bls12_381_G2_uncompress7, Bls12_381_G2_uncompress8, Bls12_381_G2_uncompress9,
          Bls12_381_millerLoop, Bls12_381_millerLoop1, Bls12_381_millerLoop2, Bls12_381_millerLoop3, Bls12_381_millerLoop4, Bls12_381_millerLoop5, Bls12_381_millerLoop6, Bls12_381_millerLoop7, Bls12_381_millerLoop8, Bls12_381_millerLoop9, Bls12_381_mulMlResult, Bls12_381_mulMlResult1, Bls12_381_mulMlResult2, Bls12_381_mulMlResult3, Bls12_381_mulMlResult4, Bls12_381_mulMlResult5, Bls12_381_mulMlResult6, Bls12_381_mulMlResult7, Bls12_381_mulMlResult8, Bls12_381_mulMlResult9, Bls12_381_finalVerify, Bls12_381_finalVerify1, Bls12_381_finalVerify2, Bls12_381_finalVerify3, Bls12_381_finalVerify4, Bls12_381_finalVerify5, Bls12_381_finalVerify6, Bls12_381_finalVerify7, Bls12_381_finalVerify8, Bls12_381_finalVerify9,
          Keccak_256, Keccak_2561, Keccak_2562, Keccak_2563, Keccak_2564, Keccak_2565, Keccak_2566, Keccak_2567, Keccak_2568, Keccak_2569, Blake2b_224, Blake2b_2241, Blake2b_2242, Blake2b_2243, Blake2b_2244, Blake2b_2245, Blake2b_2246, Blake2b_2247, Blake2b_2248, Blake2b_2249, IntegerToByteString, IntegerToByteString1, IntegerToByteString2, IntegerToByteString3, IntegerToByteString4, IntegerToByteString5, IntegerToByteString6, IntegerToByteString7, IntegerToByteString8, IntegerToByteString9, ByteStringToInteger, ByteStringToInteger1, ByteStringToInteger2, ByteStringToInteger3, ByteStringToInteger4, ByteStringToInteger5, ByteStringToInteger6, ByteStringToInteger7, ByteStringToInteger8, ByteStringToInteger9
          ]),
  ((PlutusV3, changPlus1PV), Set.fromList [
          AndByteString, AndByteString1, AndByteString2, AndByteString3, AndByteString4, AndByteString5, AndByteString6, AndByteString7, AndByteString8, AndByteString9, OrByteString, OrByteString1, OrByteString2, OrByteString3, OrByteString4, OrByteString5, OrByteString6, OrByteString7, OrByteString8, OrByteString9, XorByteString, XorByteString1, XorByteString2, XorByteString3, XorByteString4, XorByteString5, XorByteString6, XorByteString7, XorByteString8, XorByteString9, ComplementByteString, ComplementByteString1, ComplementByteString2, ComplementByteString3, ComplementByteString4, ComplementByteString5, ComplementByteString6, ComplementByteString7, ComplementByteString8, ComplementByteString9,
          ReadBit, ReadBit1, ReadBit2, ReadBit3, ReadBit4, ReadBit5, ReadBit6, ReadBit7, ReadBit8, ReadBit9, WriteBits, WriteBits1, WriteBits2, WriteBits3, WriteBits4, WriteBits5, WriteBits6, WriteBits7, WriteBits8, WriteBits9, ReplicateByte, ReplicateByte1, ReplicateByte2, ReplicateByte3, ReplicateByte4, ReplicateByte5, ReplicateByte6, ReplicateByte7, ReplicateByte8, ReplicateByte9,
          ShiftByteString, ShiftByteString1, ShiftByteString2, ShiftByteString3, ShiftByteString4, ShiftByteString5, ShiftByteString6, ShiftByteString7, ShiftByteString8, ShiftByteString9, RotateByteString, RotateByteString1, RotateByteString2, RotateByteString3, RotateByteString4, RotateByteString5, RotateByteString6, RotateByteString7, RotateByteString8, RotateByteString9, CountSetBits, CountSetBits1, CountSetBits2, CountSetBits3, CountSetBits4, CountSetBits5, CountSetBits6, CountSetBits7, CountSetBits8, CountSetBits9, FindFirstSetBit, FindFirstSetBit1, FindFirstSetBit2, FindFirstSetBit3, FindFirstSetBit4, FindFirstSetBit5, FindFirstSetBit6, FindFirstSetBit7, FindFirstSetBit8, FindFirstSetBit9,
          Ripemd_160, Ripemd_1601, Ripemd_1602, Ripemd_1603, Ripemd_1604, Ripemd_1605, Ripemd_1606, Ripemd_1607, Ripemd_1608, Ripemd_1609
          ]),
  ((PlutusV3, futurePV), Set.fromList [
          ExpModInteger, ExpModInteger1, ExpModInteger2, ExpModInteger3, ExpModInteger4, ExpModInteger5, ExpModInteger6, ExpModInteger7, ExpModInteger8, ExpModInteger9,
          CaseList, CaseData
          ])
  ]

{-| A map indicating which Plutus Core versions were introduced in which
'MajorProtocolVersion' and 'PlutusLedgerLanguage'. Each version should appear at most once.

This __must__ be updated when new versions are added.
See Note [New builtins/language versions and protocol versions]
-}
plcVersionsIntroducedIn :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set Version)
plcVersionsIntroducedIn = Map.fromList [
  ((PlutusV1, alonzoPV), Set.fromList [ plcVersion100 ]),
  ((PlutusV3, changPV), Set.fromList [ plcVersion110 ])
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
plcVersionsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone plcVersionAvailableIn plcVersionsIntroducedIn
    where
      plcVersionAvailableIn :: (PlutusLedgerLanguage, MajorProtocolVersion) -> Bool
      plcVersionAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv

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
