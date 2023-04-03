-- editorconfig-checker-disable
{-# LANGUAGE MultiParamTypeClasses #-}
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
    , memSizeBytes
    , compressedSizeBytes
    ) where

import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal

import PlutusCore.Crypto.Utils (byteStringAsHex)
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Data.ByteString (ByteString, pack)
import Data.Proxy (Proxy (..))
import Flat
import Prettyprinter

{- | See Note [Wrapping the BLS12-381 types]. -}
newtype Element = Element { unElement :: BlstBindings.Point2 }
    deriving newtype (Eq)
instance Show Element where
    show  = byteStringAsHex . compress
instance Pretty Element where
    pretty = pretty . show
instance PrettyBy ConstConfig Element where
    prettyBy _ = pretty
instance Flat Element where
    decode = do
        x <- decode
        case uncompress x of
             Left err -> fail $ show err
             Right e  -> pure e
    encode = encode . compress
    size = size . compress
instance NFData Element where
    rnf _ = ()

-- | Add two G2 group elements
add :: Element -> Element -> Element
add (Element a) (Element b) = Element $ BlstBindings.blsAddOrDouble @BlstBindings.Curve2 a b

-- | Negate a G2group element
neg :: Element -> Element
neg (Element a) = Element $ BlstBindings.blsNeg @BlstBindings.Curve2 a

scalarMul :: Integer -> Element -> Element -- Other way round from library function
scalarMul k (Element a) = Element $ BlstBindings.blsMult @BlstBindings.Curve2 a k

{- | Compress a G2 element to a bytestring. This serialises a curve point to its x
 coordinate only, using an extra bit to determine which of two possible y
 coordinates the point has. The compressed bytestring is 96 bytes long. See
 https://github.com/supranational/blst#serialization-format
-}
compress :: Element -> ByteString
compress (Element a) = BlstBindings.blsCompress @BlstBindings.Curve2 a

{- | Uncompress a bytestring to get a G2 point.  This will fail if any of the
   following are true:
     * The bytestring is not exactly 96 bytes long
     * The most significant three bits are used incorrectly
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E2 curve
     * The bytestring does represent a point on the E2 curve, but the
       point is not in the G2 subgroup
-}
-- TODO: perhaps make this emit the error in the Left case.
uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = second Element . BlstBindings.blsUncompress @BlstBindings.Curve2

-- Take an arbitrary bytestring and hash it to a get point on the curve;
hashToGroup :: ByteString -> Element
hashToGroup s = Element $ BlstBindings.blsHash @BlstBindings.Curve2 s Nothing Nothing


-- Utilities (not exposed as builtins)

-- | The zero element of G2
zero :: Element
zero =
    let b = pack (0xc0 : replicate 95 0x00) -- Compressed serialised G2 points are bytestrings of length 96: see CIP-0381.
    in case uncompress b of
         Left err       -> error $ "Unexpected failure deserialising point at infinity on BLS12_381.G2:  " ++ show err
         Right infinity -> infinity   -- The zero point on this curve is chosen to be the point at infinity.

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve2)

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve2)

