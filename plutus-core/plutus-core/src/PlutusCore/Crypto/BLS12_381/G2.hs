-- editorconfig-checker-disable
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module PlutusCore.Crypto.BLS12_381.G2
    ( Element (..)
    , add
    , neg
    , scalarMul
    , hashToGroup
    , compress
    , uncompress
    , zero
    , generator
    , compressed_generator
    , memSizeBytes
    , compressedSizeBytes
    ) where

import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal

import PlutusCore.Crypto.BLS12_381.Error
import PlutusCore.Crypto.Utils (byteStringAsHex)
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy)

import Control.DeepSeq (NFData, rnf, rwhnf)
import Data.ByteString (ByteString, length, pack)
import Data.Coerce (coerce)
import Data.Hashable
import Data.Proxy (Proxy (..))
import Flat
import Prettyprinter

{- | See Note [Wrapping the BLS12-381 types in Plutus Core]. -}
newtype Element = Element { unElement :: BlstBindings.Point2 }
    deriving newtype (Eq)
instance Show Element where
    show  = byteStringAsHex . compress
instance Pretty Element where
    pretty = pretty . show
instance PrettyBy ConstConfig Element
{- | We don't support direct flat encoding of G1 elements because of the expense
   of on-chain uncompression.  Users should convert between G1 elements and
   bytestrings using `compress` and `uncompress`: the bytestrings can be
   flat-encoded in the usual way. -}
instance Flat Element where
    -- This might happen on the chain, so `fail` rather than `error`.
    decode = fail "Flat decoding is not supported for objects of type bls12_381_G2_element: use bls12_381_G2_uncompress on a bytestring instead."
    -- This will be a Haskell runtime error, but encoding doesn't happen on chain,
    -- so it's not too bad.
    encode = error "Flat encoding is not supported for objects of type bls12_381_G2_element: use bls12_381_G2_compress to obtain a bytestring instead."
    size _ = id
instance NFData Element where
    rnf (Element x) = rwhnf x  -- Just to be on the safe side.

instance Hashable Element where
    hashWithSalt salt = hashWithSalt salt . compress

-- | Add two G2 group elements
{-# INLINE add #-}
add :: Element -> Element -> Element
add = coerce BlstBindings.blsAddOrDouble

-- | Negate a G2 group element
{-# INLINE neg #-}
neg :: Element -> Element
neg = coerce BlstBindings.blsNeg

{-# INLINE scalarMul #-}
scalarMul :: Integer -> Element -> Element -- Other way round from library function
scalarMul = coerce $ flip BlstBindings.blsMult

{- | Compress a G2 element to a bytestring. This serialises a curve point to its x
 coordinate only, using an extra bit to determine which of two possible y
 coordinates the point has. The compressed bytestring is 96 bytes long. See
 https://github.com/supranational/blst#serialization-format
-}
{-# INLINE compress #-}
compress :: Element -> ByteString
compress = coerce BlstBindings.blsCompress

{- | Uncompress a bytestring to get a G2 point.  This will fail if any of the
   following are true:
     * The bytestring is not exactly 96 bytes long
     * The most significant three bits are used incorrectly
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E2 curve
     * The bytestring does represent a point on the E2 curve, but the
       point is not in the G2 subgroup
-}
{-# INLINE uncompress #-}
uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = coerce BlstBindings.blsUncompress

-- Take an arbitrary bytestring and a Domain Separation Tag and hash them to a
-- get point in G2.  See Note [Hashing and Domain Separation Tags].
hashToGroup :: ByteString -> ByteString -> Either BLS12_381_Error Element
hashToGroup msg dst =
    if Data.ByteString.length dst > 255
    then Left HashToCurveDstTooBig
    else Right . Element $ BlstBindings.blsHash msg (Just dst) Nothing

-- | The zero element of G2
zero :: Element
zero = coerce BlstBindings.Internal.blsZero

-- | The standard generator of G2
generator :: Element
generator = coerce BlstBindings.Internal.blsGenerator

compressed_generator :: ByteString
compressed_generator =
    pack [ 0x93, 0xe0, 0x2b, 0x60, 0x52, 0x71, 0x9f, 0x60
         , 0x7d, 0xac, 0xd3, 0xa0, 0x88, 0x27, 0x4f, 0x65
         , 0x59, 0x6b, 0xd0, 0xd0, 0x99, 0x20, 0xb6, 0x1a
         , 0xb5, 0xda, 0x61, 0xbb, 0xdc, 0x7f, 0x50, 0x49
         , 0x33, 0x4c, 0xf1, 0x12, 0x13, 0x94, 0x5d, 0x57
         , 0xe5, 0xac, 0x7d, 0x05, 0x5d, 0x04, 0x2b, 0x7e
         , 0x02, 0x4a, 0xa2, 0xb2, 0xf0, 0x8f, 0x0a, 0x91
         , 0x26, 0x08, 0x05, 0x27, 0x2d, 0xc5, 0x10, 0x51
         , 0xc6, 0xe4, 0x7a, 0xd4, 0xfa, 0x40, 0x3b, 0x02
         , 0xb4, 0x51, 0x0b, 0x64, 0x7a, 0xe3, 0xd1, 0x77
         , 0x0b, 0xac, 0x03, 0x26, 0xa8, 0x05, 0xbb, 0xef
         , 0xd4, 0x80, 0x56, 0xc8, 0xc1, 0x21, 0xbd, 0xb8 ]

-- Utilities (not exposed as builtins)

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve2)

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve2)
