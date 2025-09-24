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
    , offchain_zero
    , compressed_zero
    , compressed_generator
    , memSizeBytes
    , compressedSizeBytes
    , multiScalarMul
    ) where

import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal

import PlutusCore.Crypto.BLS12_381.Error
import PlutusCore.Crypto.Utils (byteStringAsHex)
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy)

import Control.DeepSeq (NFData, rnf, rwhnf)
import Data.ByteString (ByteString, length)
import Data.Coerce (coerce)
import Data.Hashable
import Data.Proxy (Proxy (..))
import PlutusCore.Flat
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
add :: Element -> Element -> Element
add = coerce (BlstBindings.blsAddOrDouble @BlstBindings.Curve2)
{-# INLINE add #-}

-- | Negate a G2 group element
neg :: Element -> Element
neg = coerce (BlstBindings.blsNeg @BlstBindings.Curve2)
{-# INLINE neg #-}

scalarMul :: Integer -> Element -> Element -- Other way round from library function
scalarMul = coerce $ flip (BlstBindings.blsMult @BlstBindings.Curve2)
{-# INLINE scalarMul #-}

{- | Compress a G2 element to a bytestring. This serialises a curve point to its x
 coordinate only, using an extra bit to determine which of two possible y
 coordinates the point has. The compressed bytestring is 96 bytes long. See
 https://github.com/supranational/blst#serialization-format
-}
compress :: Element -> ByteString
compress = coerce (BlstBindings.blsCompress @BlstBindings.Curve2)
{-# INLINE compress #-}

{- | Uncompress a bytestring to get a G2 point.  This will fail if any of the
   following are true:
     * The bytestring is not exactly 96 bytes long
     * The most significant three bits are used incorrectly
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E2 curve
     * The bytestring does represent a point on the E2 curve, but the
       point is not in the G2 subgroup
-}
uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = coerce (BlstBindings.blsUncompress @BlstBindings.Curve2)
{-# INLINE uncompress #-}

-- Take an arbitrary bytestring and a Domain Separation Tag and hash them to a
-- get point in G2.  See Note [Hashing and Domain Separation Tags].
hashToGroup :: ByteString -> ByteString -> Either BLS12_381_Error Element
hashToGroup msg dst =
    if Data.ByteString.length dst > 255
    then Left HashToCurveDstTooBig
    else Right . Element $ BlstBindings.blsHash @BlstBindings.Curve2 msg (Just dst) Nothing

-- | The zero element of G2.  This cannot be flat-serialised and is provided
-- only for off-chain testing.
offchain_zero :: Element
offchain_zero = coerce (BlstBindings.Internal.blsZero @BlstBindings.Curve2)

-- | The zero element of G2 compressed into a bytestring.  This is provided for
-- convenience in PlutusTx and is not exported as a builtin.
compressed_zero :: ByteString
compressed_zero = compress $ coerce (BlstBindings.Internal.blsZero @BlstBindings.Curve2)

-- | The standard generator of G2 compressed into a bytestring.  This is
-- provided for convenience in PlutusTx and is not exported as a builtin.
compressed_generator :: ByteString
compressed_generator = compress $ coerce (BlstBindings.Internal.blsGenerator @BlstBindings.Curve2)

-- Utilities (not exposed as builtins)

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve2)

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve2)

-- | Multi-scalar multiplication of G2 points.
multiScalarMul :: [Integer] -> [Element] -> Element
multiScalarMul = coerce (\s p -> BlstBindings.blsMSM @BlstBindings.Curve2 (zip s p))
