-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
module Codec.CBOR.Extras
    ( SerialiseViaFlat (..)
    , decodeViaFlat
    , DeserialiseFailureInfo (..)
    , DeserialiseFailureReason (..)
    , readDeserialiseFailureInfo
    ) where

import Codec.CBOR.Decoding as CBOR
import Codec.CBOR.Read as CBOR
import Codec.Serialise (Serialise, decode, encode)
import Data.Either.Extras
import Flat qualified
import Flat.Decoder qualified as Flat

-- | Newtype to provide 'Serialise' instances for types with a 'Flat' instance that
-- just encodes the flat-serialized value as a CBOR bytestring
newtype SerialiseViaFlat a = SerialiseViaFlat a
instance Flat.Flat a => Serialise (SerialiseViaFlat a) where
  encode (SerialiseViaFlat a) = encode $ Flat.flat a
  decode = SerialiseViaFlat <$> decodeViaFlat Flat.decode

decodeViaFlat :: Flat.Get a -> CBOR.Decoder s a
decodeViaFlat decoder = do
    bs <- decodeBytes
    -- lift any flat's failures to be cborg failures (MonadFail)
    fromRightM (fail . show) $
        Flat.unflatWith decoder bs

{- | The errors returned by `cborg` are plain strings (untyped). With this function we try to
map onto datatypes, those cborg error messages that we are interested in.

Currently we are only interested in error messages returned by the `CBOR.decodeBytes` decoder;
see `PlutusLedgerApi.Common.SerialisedScript.scriptCBORDecoder`.
-}
readDeserialiseFailureInfo :: CBOR.DeserialiseFailure -> DeserialiseFailureInfo
readDeserialiseFailureInfo (CBOR.DeserialiseFailure byteOffset reason) =
    DeserialiseFailureInfo byteOffset $ interpretReason reason
  where
    -- Note that this is subject to change if `cborg` dependency changes. Currently: cborg-0.2.9.0
    interpretReason :: String -> DeserialiseFailureReason
    interpretReason = \case
        -- Relevant Sources:
        -- <https://github.com/well-typed/cborg/blob/cborg-0.2.9.0/cborg/src/Codec/CBOR/Read.hs#L226>
        -- <https://github.com/well-typed/cborg/blob/cborg-0.2.9.0/cborg/src/Codec/CBOR/Read.hs#L1424>
        -- <https://github.com/well-typed/cborg/blob/cborg-0.2.9.0/cborg/src/Codec/CBOR/Read.hs#L1441>
        "end of input"   -> EndOfInput
        -- Relevant Sources:
        -- <https://github.com/well-typed/cborg/blob/cborg-0.2.9.0/cborg/src/Codec/CBOR/Read.hs#L1051>
        "expected bytes" -> ExpectedBytes
        msg              -> OtherReason msg

-- | Similar to `CBOR.DeserialiseFailure`, with the difference that plain string reason
-- messages are turned into the datatype: `DeserialiseFailureReason`.
data DeserialiseFailureInfo
    = DeserialiseFailureInfo
        { dfOffset :: CBOR.ByteOffset
        , dfReason :: DeserialiseFailureReason
        }
    deriving stock (Eq, Show)

-- | The reason of the cbor failure as a datatype, not as a plain string.
data DeserialiseFailureReason
    = EndOfInput -- ^ Not enough input provided
    | ExpectedBytes -- ^ The bytes inside the input are malformed.
    | OtherReason String -- ^ A failure reason we (plutus) are not aware of, use whatever
                         -- message that `cborg` returns.
    deriving stock (Eq, Show)
