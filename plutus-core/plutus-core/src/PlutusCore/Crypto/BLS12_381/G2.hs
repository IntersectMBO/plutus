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
import Data.ByteString (ByteString, length)
import Data.Coerce (coerce)
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
instance Flat Element where
    decode = do
        x <- decode
        case uncompress x of
             Left err -> fail $ show err
             Right e  -> pure e
    encode = encode . compress
    size = size . compress
instance NFData Element where
    rnf (Element x) = rwhnf x  -- Just to be on the safe side.

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


-- Utilities (not exposed as builtins)

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve2)

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve2)
