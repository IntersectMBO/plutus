{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |Encoding and decoding functions
module Flat.Run (
    flat,
    flatRaw,
    unflat,
    unflatWith,
    unflatRaw,
    unflatRawWith,
    unflatRawWithOffset,
) where

import Data.ByteString qualified as B
import Data.ByteString.Convert (AsByteString (..))
import Flat.Class (Flat (decode, encode), getSize)
import Flat.Decoder (Decoded, Get, strictDecoder)
import Flat.Encoder (NumBits)
import Flat.Encoder qualified as E
import Flat.Filler (postAligned, postAlignedDecoder)

-- |Encode padded value.
flat :: Flat a => a -> B.ByteString
flat = flatRaw . postAligned

-- |Decode padded value.
unflat :: (Flat a, AsByteString b) => b -> Decoded a
unflat = unflatWith decode

-- |Decode padded value, using the provided unpadded decoder.
unflatWith :: AsByteString b => Get a -> b -> Decoded a
unflatWith dec = unflatRawWith (postAlignedDecoder dec)

-- |Decode unpadded value.
unflatRaw :: (Flat a, AsByteString b) => b -> Decoded a
unflatRaw = unflatRawWith decode

-- |Unflat unpadded value, using provided decoder
unflatRawWith :: AsByteString b => Get a -> b -> Decoded a
unflatRawWith dec bs = unflatRawWithOffset dec bs 0

unflatRawWithOffset :: AsByteString b => Get a -> b -> NumBits -> Decoded a
unflatRawWithOffset dec bs = strictDecoder dec (toByteString bs)

-- unflatRawWith :: AsByteString b => Get a -> b -> Decoded a
-- unflatRawWith dec bs = unflatRawWithOffset dec bs 0

-- unflatRawWithOffset :: AsByteString b => Get a -> b -> Int -> Decoded a
-- unflatRawWithOffset dec bs = strictDecoder dec (toByteString bs)

-- |Encode unpadded value
flatRaw :: (Flat a, AsByteString b) => a -> b
flatRaw a =
    fromByteString $
        E.strictEncoder
            (getSize a)

#ifdef ETA_VERSION
        (E.trampolineEncoding (encode a))
#else
        (encode a)
#endif

-- #ifdef ETA_VERSION
--   deriving (Show, Eq, Ord, Typeable, Generic, NFData)

-- instance Flat a => Flat (PostAligned a) where
--   encode (PostAligned val fill) = trampolineEncoding (encode val) <> encode fill

-- #else
--   deriving (Show, Eq, Ord, Typeable, Generic, NFData,Flat)
-- #endif
