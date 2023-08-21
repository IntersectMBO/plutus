-- editorconfig-checker-disable
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
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

{- | Note [Wrapping the BLS12-381 types in Plutus Core].  In the Haskell bindings
to the `blst` library in cardano-crypto-class, points in G1 and G2 are
represented as ForeignPtrs pointing to C objects, with a phantom type
determining which group is involved. We have to wrap these in a newtype here
because otherwise the builtin machinery spots that they're applications and
can't find the relevant type parameters.  In theory I think we could add a
couple of phantom types to the default universe, but it seemed simpler and safer
to use monomorphic types instead, even though it requires a bit of code
duplication between G1 and G2.  Much of the code here has apparently identical
versions in PlutusCore.Crypto.BLS12_381.G2, but the signatures of the functions
in the two versions are invisibly instantiating the cardano-crypto-class
functions at the appropriate phantom types.

See also Note [Wrapping the BLS12-381 types in PlutusTx].
-}
newtype Element = Element { unElement :: BlstBindings.Point1 }
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

-- | Add two G1 group elements
{-# INLINE add #-}
add :: Element -> Element -> Element
add = coerce BlstBindings.blsAddOrDouble

-- | Negate a G1 group element
{-# INLINE neg #-}
neg :: Element -> Element
neg = coerce BlstBindings.blsNeg

-- | Multiplication of group elements by scalars. In the blst library the
-- arguments are the other way round, but scalars acting on the left is more
-- consistent with standard mathematical practice.
{-# INLINE scalarMul #-}
scalarMul :: Integer -> Element -> Element
scalarMul = coerce $ flip BlstBindings.blsMult

{- | Compress a G1 element to a bytestring. This serialises a curve point to its
 x coordinate only.  The compressed bytestring is 48 bytes long, with three
 spare bits used to convey extra information about the point, including
 determining which of two possible y coordinates the point has and whether the
 point is the point at infinity. See
 https://github.com/supranational/blst#serialization-format
-}
{-# INLINE compress #-}
compress :: Element -> ByteString
compress = coerce BlstBindings.blsCompress

{- | Uncompress a bytestring to get a G1 point.  This will fail if any of the
   following are true.
     * The bytestring is not exactly 48 bytes long.
     * The most significant three bits are used incorrectly.
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E1 curve.
     * The bytestring does represent a point on the E1 curve, but the
       point is not in the G1 subgroup.
-}
{-# INLINE uncompress #-}
uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = coerce BlstBindings.blsUncompress

{- | Note [Hashing and Domain Separation Tags].  The hashToGroup functions take a
   bytestring and hash it to obtain an element in the relevant group, as
   described in

   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve.

   In addition to the input bytestring (the "message"), the hashing function
   also takes another (possibly empty) bytestring argument, a "Domain Separation
   Tag" (DST), which is incorporated in the hashing process; the intention is
   that for security purposes different protocols should use different DSTs to
   ensure that hashes are unique to the protocol in use: see Section 2.2.5 of
   the above specification.  In principle, arbitrary-length DSTs can be used,
   but we only allow DSTs of up to 255 bytes, failing if a larger DST is
   supplied.  If a larger DST is required, it should be hashed beforehand to
   obtain a hash of accpetable size, as described in Section 5.3.3 of the
   specification.

   The hashing functions in the blst library allow a third argument as well (an
   "augmentation string").  We don't support this functionality directly because
   precisely the same effect can be achieved by prepending the augmentation
   string to the message.
-}

-- | Take an arbitrary bytestring and a Domain Separation Tag (DST) and hash
-- them to a get point in G1.
hashToGroup :: ByteString -> ByteString -> Either BLS12_381_Error Element
hashToGroup msg dst =
    if Data.ByteString.length dst > 255
    then Left HashToCurveDstTooBig
    else Right . Element $ BlstBindings.blsHash msg (Just dst) Nothing

-- | The zero element of G1
zero :: Element
zero = coerce BlstBindings.Internal.blsZero

-- | The standard generator of G1
generator :: Element
generator = coerce BlstBindings.Internal.blsGenerator


-- Utilities (not exposed as builtins)

-- | Memory usage of a G1 point (144 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve1)

-- | Compressed size of a G1 point (48 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve1)
