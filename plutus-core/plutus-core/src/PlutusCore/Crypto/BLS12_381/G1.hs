-- editorconfig-checker-disable
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module PlutusCore.Crypto.BLS12_381.G1
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

{- | Note [Wrapping the BLS12-381 types in Plutus Core].  In the Haskell bindings
to the `blst` library, points in G1 and G2 are represented as ForeignPtrs
pointing to C objects, with a phantom type determining which group is
involved. We have to wrap these in a newtype here because otherwise the builtin
machinery spots that they're applications and can't find the relevant type
parameters.  In theory I think we could add a couple of phantom types to the
default universe, but it seemed simpler and safer to use monomorphic types
instead, even though it requires a bit of code duplication between G1 and G2.

See also Note [Wrapping the BLS12-381 types in PlutusTx].
-}
newtype Element = Element { unElement :: BlstBindings.Point1 }
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

-- | Add two G1 group elements
add :: Element -> Element -> Element
add (Element a) (Element b) = Element $ BlstBindings.blsAddOrDouble @BlstBindings.Curve1 a b

-- | Negate a G1 group element
neg :: Element -> Element
neg (Element a) = Element $ BlstBindings.blsNeg @BlstBindings.Curve1 a

-- | Multiplication of group elements by scalars. In the blst library the
-- arguments are the other way round, but scalars acting on the left is more
-- consistent with standard mathematical practice.
scalarMul :: Integer -> Element -> Element
scalarMul k (Element a) = Element $ BlstBindings.blsMult @BlstBindings.Curve1 a k

{- | Compress a G1 element to a bytestring. This serialises a curve point to its
 x coordinate only.  The compressed bytestring is 48 bytes long, with three
 spare bits used to convey extra information about the point, including
 determining which of two possible y coordinates the point has and whether the
 point is the point at infinity. See
 https://github.com/supranational/blst#serialization-format
-}
compress :: Element -> ByteString
compress (Element a) = BlstBindings.blsCompress @BlstBindings.Curve1 a

{- | Uncompress a bytestring to get a G1 point.  This will fail if any of the
   following are true.
     * The bytestring is not exactly 48 bytes long.
     * The most significant three bits are used incorrectly.
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E1 curve.
     * The bytestring does represent a point on the E1 curve, but the
       point is not in the G1 subgroup.
-}
-- TODO: perhaps make this emit the error in the Left case.
uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = second Element . BlstBindings.blsUncompress @BlstBindings.Curve1

-- | Take an arbitrary bytestring and hash it to a get point in G1
hashToGroup :: ByteString -> Element
hashToGroup s = Element $ BlstBindings.blsHash @BlstBindings.Curve1 s Nothing Nothing

-- Utilities (not exposed as builtins)

-- | The zero element of G1
zero :: Element
zero =
    let b = pack (0xc0 : replicate 47 0x00) -- Compressed serialised G1 points are bytestrings of length 48: see CIP-0381.
    in case uncompress b of
         Left err       -> error $ "Unexpected failure deserialising point at infinity on BLS12_381.G1:  " ++ show err
         Right infinity -> infinity  -- The zero point on this curve is chosen to be the point at infinity.

-- | Memory usage of a G1 point (144 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve1)

-- | Compressed size of a G1 point (48 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve1)

