module Codec.Extras.FlatViaSerialise
    ( FlatViaSerialise (..)
    ) where

import Codec.Serialise (Serialise, deserialiseOrFail, serialise)
import Data.ByteString.Lazy qualified as BSL (toStrict)
import PlutusCore.Flat

{- Note [Flat serialisation for strict and lazy bytestrings]
The `flat` serialisation of a bytestring consists of a sequence of chunks, with each chunk preceded
by a single byte saying how long it is.  The end of a serialised bytestring is marked by a
zero-length chunk.  In the Plutus Core specification we recommend that all bytestrings should be
serialised in a canonical way as a sequence of zero or more 255-byte chunks followed by an optional
final chunk of length less than 255 followed by a zero-length chunk (ie, a 0x00 byte). We do allow
the decoder to accept non-canonical encodings.  The `flat` library always encodes strict Haskell
bytestrings in this way, but lazy bytestrings, which are essentially lists of strict bytestrings,
may be encoded non-canonically since it's more efficient just to emit a short chunk as is.  The
Plutus Core `bytestring` type is strict so bytestring values are always encoded canonically.
However, we serialise `Data` objects (and perhaps objects of other types as well) by encoding them
to CBOR and then flat-serialising the resulting bytestring; but the `serialise` method from
`Codec.Serialise` produces lazy bytestrings and if we were to serialise them directly then we could
end up with non-canonical encodings, which would mean that identical `Data` objects might be
serialised into different bytestrings.  To avoid this we convert the output of `serialise` into a
strict bytestring before flat-encoding it.  This may lead to a small loss of efficiency during
encoding, but this doesn't matter because we only ever do flat serialisation off the chain.  We can
convert `Data` objects to bytestrings on the chain using the `serialiseData` builtin, but this
performs CBOR serialisation and the result is always in a canonical form. -}

-- | For deriving 'Flat' instances via 'Serialize'.
newtype FlatViaSerialise a = FlatViaSerialise { unFlatViaSerialise :: a }

instance Serialise a => Flat (FlatViaSerialise a) where
    -- See Note [Flat serialisation for strict and lazy bytestrings]
    encode = encode . BSL.toStrict . serialise . unFlatViaSerialise
    decode = do
        errOrX <- deserialiseOrFail <$> decode
        case errOrX of
            Left err -> fail $ show err  -- Here we embed a 'Serialise' error into a 'Flat' one.
            Right x  -> pure $ FlatViaSerialise x
    size = size . BSL.toStrict . serialise . unFlatViaSerialise
