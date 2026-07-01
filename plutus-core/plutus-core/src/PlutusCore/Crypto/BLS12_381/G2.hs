-- editorconfig-checker-disable
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Crypto.BLS12_381.G2
  ( Element (..)
  , add
  , neg
  , scalarMul
  , scalarMulE
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

import PlutusCore.Builtin.Result (BuiltinResult (..))
import PlutusCore.Crypto.Utils (byteStringAsHex)
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy)

import Control.DeepSeq
  ( NFData
  , rnf
  , rwhnf
  )
import Data.ByteString (ByteString)
import Data.Hashable
import PlutusCore.Flat
import Prettyprinter

#ifdef WITH_CRYPTO
import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal
import Data.ByteString (length)
import Data.Coerce (coerce)
import Data.Proxy (Proxy (..))
import PlutusCore.Crypto.BLS12_381.Bounds (msmScalarOutOfBounds)
import PlutusCore.Crypto.BLS12_381.Error (BLS12_381_Error (..))
#else
import Data.ByteString (pack)
import Data.Char (digitToInt)
import PlutusCore.Crypto.BLS12_381.Error (BLS12_381_Error)
import PlutusCore.Crypto.Utils (cryptoDisabled)
#endif

-- | See Note [Wrapping the BLS12-381 types in Plutus Core].
#ifdef WITH_CRYPTO
newtype Element = Element {unElement :: BlstBindings.Point2}
  deriving newtype (Eq)
#else
{- See Note [The with-crypto flag] in PlutusCore.Crypto.Utils. Without the C
cryptography libraries a G2 element is represented by its compressed-point bytes;
this is enough to carry the type through the universe and to compile scripts, but
the group operations below are unavailable. -}
newtype Element = Element {unElement :: ByteString}
  deriving newtype (Eq)
#endif

instance Show Element where
  show = byteStringAsHex . compress
instance Pretty Element where
  pretty = pretty . show
instance PrettyBy ConstConfig Element

{-| We don't support direct flat encoding of G1 elements because of the expense
   of on-chain uncompression.  Users should convert between G1 elements and
   bytestrings using `compress` and `uncompress`: the bytestrings can be
   flat-encoded in the usual way. -}
instance Flat Element where
  -- This might happen on the chain, so `fail` rather than `error`.
  decode =
    fail
      "Flat decoding is not supported for objects of type bls12_381_G2_element: use bls12_381_G2_uncompress on a bytestring instead."

  -- This will be a Haskell runtime error, but encoding doesn't happen on chain,
  -- so it's not too bad.
  encode =
    error
      "Flat encoding is not supported for objects of type bls12_381_G2_element: use bls12_381_G2_compress to obtain a bytestring instead."
  size _ = id

instance NFData Element where
  rnf (Element x) = rwhnf x -- Just to be on the safe side.

instance Hashable Element where
  hashWithSalt salt = hashWithSalt salt . compress

#ifdef WITH_CRYPTO

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

scalarMulE :: Integer -> Element -> BuiltinResult Element
scalarMulE x
  | msmScalarOutOfBounds x = const $ fail "Scalar exceeds 512-byte bound for G2.scalarMul"
  | otherwise = pure . (coerce . flip (BlstBindings.blsMult @BlstBindings.Curve2) $ x)
{-# INLINE scalarMulE #-}

{-| Compress a G2 element to a bytestring. This serialises a curve point to its x
 coordinate only, using an extra bit to determine which of two possible y
 coordinates the point has. The compressed bytestring is 96 bytes long. See
 https://github.com/supranational/blst#serialization-format -}
compress :: Element -> ByteString
compress = coerce (BlstBindings.blsCompress @BlstBindings.Curve2)
{-# INLINE compress #-}

{-| Uncompress a bytestring to get a G2 point.  This will fail if any of the
   following are true:
     * The bytestring is not exactly 96 bytes long
     * The most significant three bits are used incorrectly
     * The bytestring encodes a field element which is not the
       x coordinate of a point on the E2 curve
     * The bytestring does represent a point on the E2 curve, but the
       point is not in the G2 subgroup -}
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

{-| The zero element of G2.  This cannot be flat-serialised and is provided
only for off-chain testing. -}
offchain_zero :: Element
offchain_zero = coerce (BlstBindings.Internal.blsZero @BlstBindings.Curve2)

{-| The zero element of G2 compressed into a bytestring.  This is provided for
convenience in PlutusTx and is not exported as a builtin. -}
compressed_zero :: ByteString
compressed_zero = compress $ coerce (BlstBindings.Internal.blsZero @BlstBindings.Curve2)

{-| The standard generator of G2 compressed into a bytestring.  This is
provided for convenience in PlutusTx and is not exported as a builtin. -}
compressed_generator :: ByteString
compressed_generator = compress $ coerce (BlstBindings.Internal.blsGenerator @BlstBindings.Curve2)

-- Utilities (not exposed as builtins)

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = BlstBindings.Internal.sizePoint (Proxy @BlstBindings.Curve2)

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = BlstBindings.Internal.compressedSizePoint (Proxy @BlstBindings.Curve2)

{-| Multi-scalar multiplication of G2 points.  We limit the allowable size of
scalars to simplify costing. -}
multiScalarMul :: [Integer] -> [Element] -> BuiltinResult Element
multiScalarMul ss p
  | any msmScalarOutOfBounds ss = fail "Scalar exceeds 512-byte bound for G2.multiScalarMul"
  | otherwise = pure . coerce $ BlstBindings.blsMSM @BlstBindings.Curve2 (zip ss (coerce p))

#else

-- C-free stubs. See Note [The with-crypto flag] in PlutusCore.Crypto.Utils.
-- The group operations require the blst C library and are therefore unavailable;
-- 'compress'/'uncompress' remain total so the type can still be carried through
-- the universe, parsed, and compiled.

add :: Element -> Element -> Element
add = cryptoDisabled "bls12_381_G2_add"

neg :: Element -> Element
neg = cryptoDisabled "bls12_381_G2_neg"

scalarMul :: Integer -> Element -> Element
scalarMul = cryptoDisabled "bls12_381_G2_scalarMul"

scalarMulE :: Integer -> Element -> BuiltinResult Element
scalarMulE = cryptoDisabled "bls12_381_G2_scalarMul"

-- | Just exposes the stored bytes: the only G2 operation that stays total in a
-- C-free build, so that 'Show'/'Hashable' keep working.
compress :: Element -> ByteString
compress = unElement

-- | Cannot validate the point without the C library, so it just stores the
-- bytes. This lets the textual parser accept G2 literals when compiling scripts;
-- the bytes are never interpreted as a curve point in a C-free build.
uncompress :: ByteString -> Either BLS12_381_Error Element
uncompress = Right . Element

hashToGroup :: ByteString -> ByteString -> Either BLS12_381_Error Element
hashToGroup = cryptoDisabled "bls12_381_G2_hashToGroup"

-- The compressed zero/generator are fixed constants that PlutusTx lifts at
-- COMPILE time, so they must be real values (not stubs) even in a C-free build.
-- These literals are golden-checked (in a with-crypto build) to equal
-- @compress blsZero@ / @compress blsGenerator@.
offchain_zero :: Element
offchain_zero = Element compressed_zero

compressed_zero :: ByteString
compressed_zero =
  unhex "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

compressed_generator :: ByteString
compressed_generator =
  unhex "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"

-- | Decode a hex string to a 'ByteString'. C-free helper for the constants above.
unhex :: String -> ByteString
unhex = pack . go
  where
    go (a : b : rest) = fromIntegral (digitToInt a * 16 + digitToInt b) : go rest
    go _ = []

-- | Memory usage of a G2 point (288 bytes)
memSizeBytes :: Int
memSizeBytes = 288

-- | Compressed size of a G2 point (96 bytes)
compressedSizeBytes :: Int
compressedSizeBytes = 96

multiScalarMul :: [Integer] -> [Element] -> BuiltinResult Element
multiScalarMul = cryptoDisabled "bls12_381_G2_multiScalarMul"

#endif
