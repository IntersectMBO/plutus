{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Codec.Extras.SerialiseViaFlat
    ( SerialiseViaFlat (..)
    , decodeViaFlatWith
    , DeserialiseFailureInfo (..)
    , DeserialiseFailureReason (..)
    , readDeserialiseFailureInfo
    ) where

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Read qualified as CBOR
import Codec.Serialise (Serialise, decode, encode)
import Data.Either.Extras (fromRightM)
import PlutusCore.Flat qualified as Flat
import PlutusCore.Flat.Decoder qualified as Flat
import Prettyprinter (Pretty (pretty), (<+>))

{- | Newtype to provide 'Serialise' instances for types with a 'Flat' instance
  that just encodes the flat-serialized value as a CBOR bytestring
-}
newtype SerialiseViaFlat a = SerialiseViaFlat { unSerialiseViaFlat :: a }

instance (Flat.Flat a) => Serialise (SerialiseViaFlat a) where
  encode = encode . Flat.flat . unSerialiseViaFlat
  decode = SerialiseViaFlat <$> decodeViaFlatWith Flat.decode

decodeViaFlatWith :: Flat.Get a -> CBOR.Decoder s a
decodeViaFlatWith decoder = do
  bs <- CBOR.decodeBytes
  -- lift any flat's failures to be cborg failures (MonadFail)
  fromRightM (fail . show) $ Flat.unflatWith decoder bs

{- | The errors returned by `cborg` are plain strings (untyped). With this
function we try to map onto datatypes, those cborg error messages that we are
interested in.

Currently we are only interested in error messages returned by the
`CBOR.decodeBytes` decoder;
see `PlutusLedgerApi.Common.SerialisedScript.scriptCBORDecoder`.
-}
readDeserialiseFailureInfo :: CBOR.DeserialiseFailure -> DeserialiseFailureInfo
readDeserialiseFailureInfo (CBOR.DeserialiseFailure byteOffset reason) =
  DeserialiseFailureInfo byteOffset $ interpretReason reason
 where
  -- Note that this is subject to change if `cborg` dependency changes.
  -- Currently: cborg-0.2.10.0
  interpretReason :: String -> DeserialiseFailureReason
  interpretReason = \case
    -- Relevant Sources:
    -- <https://github.com/well-typed/cborg/blob/cborg-0.2.10.0/cborg/src/Codec/CBOR/Read.hs#L226>
    -- <https://github.com/well-typed/cborg/blob/cborg-0.2.10.0/cborg/src/Codec/CBOR/Read.hs#L1424>
    -- <https://github.com/well-typed/cborg/blob/cborg-0.2.10.0/cborg/src/Codec/CBOR/Read.hs#L1441>
    "end of input" -> EndOfInput
    -- Relevant Sources:
    -- <https://github.com/well-typed/cborg/blob/cborg-0.2.10.0/cborg/src/Codec/CBOR/Read.hs#L1051>
    "expected bytes" -> ExpectedBytes
    msg -> OtherReason msg

{- | Similar to `CBOR.DeserialiseFailure`, with the difference that plain
string reason messages are turned into the datatype: `DeserialiseFailureReason`.
-}
data DeserialiseFailureInfo = DeserialiseFailureInfo
  { dfOffset :: CBOR.ByteOffset
  , dfReason :: DeserialiseFailureReason
  }
  deriving stock (Eq, Show)

instance Pretty DeserialiseFailureInfo where
  pretty (DeserialiseFailureInfo offset reason) =
    "CBOR deserialisation failed at the offset"
      <+> pretty offset
      <+> "for the following reason:"
      <+> pretty reason

-- | The reason of the cbor failure as a datatype, not as a plain string.
data DeserialiseFailureReason
  = -- | Not enough input provided
    EndOfInput
  | -- | The bytes inside the input are malformed.
    ExpectedBytes
  | -- | This is either a cbor failure that we (plutus) are not aware of,
    -- or an underlying flat failure. We use whatever message `cborg` or flat returns.
    OtherReason String
  deriving stock (Eq, Show)

instance Pretty DeserialiseFailureReason where
  pretty = \case
    EndOfInput -> "reached the end of input while more data was expected."
    ExpectedBytes -> "the bytes inside the input are malformed."
    OtherReason msg -> pretty msg
