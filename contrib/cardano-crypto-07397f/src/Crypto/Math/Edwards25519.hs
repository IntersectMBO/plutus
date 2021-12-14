-- |
-- Module      : Crypto.Math.Edwards25519
-- Description : Edwards 25519 arithmetics
-- Maintainer  : vincent@typed.io
--
-- Simple module to play with the arithmetics of the twisted edwards curve Ed25519
-- using Extended Twisted Edwards Coordinates. Compared to the normal implementation
-- this allow to use standard DH property:
--
-- for all valid s1 and s2 scalar:
--
-- > scalarToPoint (s1 + s2) = pointAdd (scalarToPoint s1) (scalarToPoint s2)
--
-- For further useful references about Ed25519:
--
-- * RFC 8032
-- * <http://ed25519.cr.yp.to/>
-- * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
-- * <http://eprint.iacr.org/2008/522.pdf>
--
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}

module Crypto.Math.Edwards25519
    (
    -- * Basic types
      Scalar
    , PointCompressed
    , Signature(..)
    -- * smart constructor & destructor
    , scalar
    , scalarP
    , unScalar
    , pointCompressed
    , pointCompressedP
    , unPointCompressed
    , unPointCompressedP
    -- * Arithmetic
    , scalarFromInteger
    , scalarAdd
    , scalarToPoint
    , pointAdd
    -- * Signature & Verify
    , sign
    , verify
    ) where

import           Control.DeepSeq             (NFData)
import           Crypto.Hash
import           Crypto.Number.ModArithmetic
import           Crypto.Number.Serialize
import           Data.Bits
#if MIN_VERSION_memory(0,14,18)
import qualified Data.ByteArray              as B hiding (append, reverse)
#else
import qualified Data.ByteArray              as B hiding (append)
#endif
import           Data.ByteString             (ByteString)
import qualified Data.ByteString             as B (append, reverse)
import           Data.Hashable               (Hashable)
import           GHC.Stack

import           Crypto.Math.Bytes (Bytes)
import qualified Crypto.Math.Bytes as Bytes

-- | Represent a scalar in the base field
newtype Scalar = Scalar { unScalar :: ByteString }

-- | Represent a point on the Edwards 25519 curve
newtype PointCompressed = PointCompressed { unPointCompressed :: ByteString }
    deriving (Show, Eq, Ord, NFData, Hashable)

-- | Represent a signature
newtype Signature = Signature { unSignature :: ByteString }
    deriving (Show, Eq, Ord, NFData, Hashable)

newtype Fq = Fq { unFq :: Integer }
-- newtype Fp = Fp { unFp :: Integer }

{- for debugging
fq :: HasCallStack => Integer -> Fq
fq n
    | n >= 0 && n < q = Fq n
    | otherwise       = error "fq"
-}

fq :: Integer -> Fq
fq = Fq

-- | Create a Ed25519 scalar
--
-- Only check that the length is of expected size (32 bytes), no effort is made for the scalar
-- to be in the right base field range on purpose.
scalar :: ByteString -> Scalar
scalar bs
    | B.length bs /= 32 = error "invalid scalar"
    | otherwise         = Scalar bs

scalarP :: Bytes 32 -> Scalar
scalarP = scalar . B.pack . Bytes.unpack


-- | Check if a scalar is valid and all the bits properly set/cleared
-- scalarValid :: Scalar -> Bool
-- scalarValid _s = True -- TODO

-- | Smart constructor to create a compress point binary
--
-- Check if the length is of expected size
pointCompressed :: HasCallStack => ByteString -> PointCompressed
pointCompressed bs
    | B.length bs /= 32 = error ("invalid compressed point: expecting 32 bytes, got " ++ show (B.length bs) ++ " bytes")
    | otherwise         = PointCompressed bs

pointCompressedP :: Bytes 32 -> PointCompressed
pointCompressedP = pointCompressed . B.pack . Bytes.unpack

unPointCompressedP :: PointCompressed -> Bytes 32
unPointCompressedP (PointCompressed bs) = Bytes.pack $ B.unpack bs

-- | Create a signature using a variant of ED25519 signature
--
-- we don't hash the secret key to derive a key + prefix, but
-- instead we take an explicit salt and compute a prefix
-- using the secret key + salt.
sign :: B.ByteArrayAccess msg => Scalar -> ByteString -> msg -> Signature
sign a salt msg =
    Signature (unPointCompressed pR `B.append` toBytes s)
  where
    prefix = hash ((unScalar a) `B.append` salt) :: Digest SHA512
    pA = scalarToPoint a
    r = sha512_modq (B.convert prefix `B.append` B.convert msg)
    pR = ePointCompress $ ePointMul r pG
    h = sha512_modq (unPointCompressed pR `B.append` unPointCompressed pA `B.append` B.convert msg)
    s = (unFq r + unFq h * (fromBytes (unScalar a))) `mod` q

-- | Verify a signature
verify :: B.ByteArrayAccess msg => PointCompressed -> msg -> Signature -> Bool
verify pA msg (Signature signature) =
    pS `pointEqual` ePointAdd (ePointDecompress pR) hA
  where
    (pR, s) =
        let (sig0, sig1) = B.splitAt 32 signature
         in (PointCompressed sig0, fq $ fromBytes sig1)

    pointEqual (ExtendedPoint pX pY pZ _) (ExtendedPoint qX qY qZ _) =
        ((pX * qZ - qX * pZ) `mod` p == 0) && ((pY * qZ - qY * pZ) `mod` p == 0)

    h = sha512_modq (unPointCompressed pR `B.append` unPointCompressed pA `B.append` B.convert msg)
    pS = ePointMul s pG
    hA = ePointMul h (ePointDecompress pA)

-- | Add 2 scalar in the base field together
scalarAdd :: Scalar -> Scalar -> Scalar
scalarAdd (Scalar s1) (Scalar s2) = Scalar $ toBytes r
  where
    r = (fromBytes s1 + fromBytes s2) `mod` q

-- | Create a scalar from integer. mainly for debugging purpose.
scalarFromInteger :: Integer -> Scalar
scalarFromInteger n = Scalar $ toBytes (n `mod` q)

-- | Add 2 points together
pointAdd :: PointCompressed -> PointCompressed -> PointCompressed
pointAdd p1 p2 = ePointCompress $ ePointAdd (ePointDecompress p1) (ePointDecompress p2)

-- | Lift a scalar to the curve, and returning a compressed point
scalarToPoint :: Scalar -> PointCompressed
scalarToPoint (Scalar sec) = ePointCompress $ ePointMul (fq (fromBytes sec `mod` q)) pG

-- | Point represented by (X, Y, Z, T) in extended twisted edward coordinates.
--
--   x = X/Z
--   y = Y/Z
-- x*y = T/Z
data ExtendedPoint = ExtendedPoint !Integer !Integer !Integer !Integer
    deriving (Show,Eq)

ePointAdd :: ExtendedPoint -> ExtendedPoint -> ExtendedPoint
ePointAdd (ExtendedPoint pX pY pZ pT) (ExtendedPoint qX qY qZ qT) =
    ExtendedPoint (e*f) (g*h) (f*g) (e*h)
  where
    a = ((pY-pX) * (qY-qX)) `mod` p
    b = ((pY+pX) * (qY+qX)) `mod` p
    c = (2 * pT * qT * curveD) `mod` p
    d = (2 * pZ * qZ) `mod` p
    e = b-a
    f = d-c
    g = d+c
    h = b+a

ePointMul :: Fq -> ExtendedPoint -> ExtendedPoint
ePointMul (Fq s) = loop 255 (ExtendedPoint 0 1 1 0)
  where
    loop !i !acc !pP
        | i < 0       = pP `seq` acc
        | testBit s i = loop (i-1) (ePointAdd acc pP)  (ePointAdd pP pP)
        | otherwise   = loop (i-1) (ePointAdd acc acc) (ePointAdd acc pP)

ePointCompress :: ExtendedPoint -> PointCompressed
ePointCompress (ExtendedPoint pX pY pZ _) =
    PointCompressed $ toBytes (y .|. ((x .&. 0x1) `shiftL` 255))
  where
    zinv = modp_inv pZ
    x = (pX * zinv) `mod` p
    y = (pY * zinv) `mod` p

ePointDecompress :: PointCompressed -> ExtendedPoint
ePointDecompress (PointCompressed bs) =
    let cy    = fromBytes bs
        xSign = testBit cy 255
        y     = clearBit cy 255
        x     = recoverX y xSign
     in ExtendedPoint x y 1 ((x*y) `mod` p)

-- | Given y and the sign of x, recover x
recoverX :: Integer -> Bool -> Integer
recoverX y xSign = x''
  where
    x2 = (y*y-1) * modp_inv (curveD*y*y+1)
    x = expFast x2 ((p+3) `div` 8) p

    x'
        | (x*x - x2) `mod` p /= 0 = (x * modp_sqrt_m1) `mod` p
        | otherwise               = x

    x''
        | odd x' /= xSign = p - x'
        | otherwise       = x'

    modp_sqrt_m1 :: Integer
    !modp_sqrt_m1 = expFast 2 ((p-1) `div` 4) p

-- | Unserialize little endian
fromBytes :: ByteString -> Integer
fromBytes = os2ip . B.reverse

-- | Serialize little endian of a given size (32 bytes)
toBytes :: Integer -> ByteString
toBytes = B.reverse . i2ospOf_ 32

-- | Inverse modular p
modp_inv :: Integer -> Integer
modp_inv x = expFast x (p-2) p

-- | Base field 2^255-19 => 25519
p :: Integer
p = 2^(255 ::Int) - 19

-- | Curve constant d
curveD :: Integer
curveD = (-121665 * modp_inv 121666) `mod` p

-- | Group order
q :: Integer
q = 2^(252 ::Int) + 27742317777372353535851937790883648493

-- | Base Point in extended form
pG :: ExtendedPoint
pG = ExtendedPoint g_x g_y 1 ((g_x * g_y) `mod` p)
  where
    !g_y = (4 * modp_inv 5) `mod` p
    !g_x = recoverX g_y False

sha512_modq :: B.ByteArrayAccess ba => ba -> Fq
sha512_modq bs =
    Fq (fromBytes (B.convert (hash bs :: Digest SHA512)) `mod` q)
