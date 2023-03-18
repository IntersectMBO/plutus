--- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}

module Crypto.External.EllipticCurve.BLS12_381.Internal
(
  -- * Unsafe Types
    ScalarPtr
  , PPtr
  , AffinePtr

  , P1Ptr
  , P2Ptr
  , Affine1Ptr
  , Affine2Ptr

  , PTPtr

  -- * Phantom Types
  , Curve1
  , Curve2

  -- * Error codes
  , c_blst_success
  , c_blst_error_bad_encoding
  , c_blst_error_point_not_on_curve
  , c_blst_error_point_not_in_group
  , c_blst_error_aggr_type_mismatch
  , c_blst_error_verify_fail
  , c_blst_error_pk_is_infinity
  , c_blst_error_bad_scalar

  -- * Safe types
  , Affine
  , Affine1
  , Affine2
  , BLSTError (..)
  , P
  , P1
  , P2
  , PT
  , Scalar

  , unsafePFromPPtr

  -- * The period of scalars
  , scalarPeriod

  -- * Curve abstraction

  , BLS

  , BLS_Curve
      ( c_blst_on_curve
      , c_blst_add_or_double
      , c_blst_mult
      , c_blst_cneg
      , c_blst_hash
      , c_blst_compress
      , c_blst_serialize
      , c_blst_uncompress
      , c_blst_deserialize
      , c_blst_in_g
      , c_blst_to_affine
      , c_blst_from_affine
      , c_blst_affine_in_g
      , c_blst_generator
      , c_blst_p_is_equal
      , c_blst_p_is_inf
      )

  -- * Pairing check

  , c_blst_miller_loop

  -- * FP12 functions
  --
  , c_blst_fp12_mul
  , c_blst_fp12_is_equal
  , c_blst_fp12_finalverify

  -- * Scalar functions

  , c_blst_scalar_fr_check

  , c_blst_scalar_from_fr
  , c_blst_fr_from_scalar
  , c_blst_scalar_from_be_bytes
  , c_blst_bendian_from_scalar

  -- * Marshalling functions
  , BLS_P
  , sizeP
  , withP
  , withNewP
  , withNewP_
  , withNewP'
  , cloneP
  , compressedSizeP
  , serializedSizeP

  , sizeAffine
  , withAffine
  , withNewAffine
  , withNewAffine_
  , withNewAffine'

  , sizePT
  , withPT
  , withNewPT
  , withNewPT_
  , withNewPT'

  , sizeScalar
  , withScalar
  , withNewScalar
  , withNewScalar_
  , withNewScalar'
  , cloneScalar

  , sizeFr
  , withFr
  , withNewFr
  , withNewFr_
  , withNewFr'
  , cloneFr

  -- * Utility
  , integerAsCStrL
  , cstrToInteger
  , integerToBS
  , padBS

  -- * P1/G1 operations
  , inGroup
  , addOrDouble
  , mult
  , cneg
  , neg
  , compress
  , serialize
  , uncompress
  , deserialize
  , hash
  , generator
  , isInf

  , toAffine
  , fromAffine
  , affineInG

  -- * PT operations
  , ptMult
  , ptFinalVerify

  -- * Scalar / Fr operations
  , scalarFromFr
  , frFromScalar
  , frFromCanonicalScalar
  , scalarFromBS
  , scalarToBS
  , scalarFromInteger
  , scalarToInteger
  , scalarCanonical

  -- * Pairings
  , miller_loop
)
where

import Data.Bits (shiftL, shiftR, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal qualified as BSI
import Data.ByteString.Unsafe qualified as BSU
import Data.Proxy (Proxy (..))
import Data.Void
import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, nullPtr, plusPtr)
import Foreign.Storable (peek)
import System.IO.Unsafe (unsafePerformIO)

---- Phantom Types

data Curve1
data Curve2

---- Unsafe PPtr types

newtype PPtr curve = PPtr (Ptr Void)

type P1Ptr = PPtr Curve1
type P2Ptr = PPtr Curve2

newtype AffinePtr curve = AffinePtr (Ptr Void)

type Affine1Ptr = AffinePtr Curve1
type Affine2Ptr = AffinePtr Curve2

newtype PTPtr = PTPtr (Ptr Void)

unsafePFromPPtr :: PPtr curve -> P curve
unsafePFromPPtr (PPtr ptr) =
  P . unsafePerformIO $ newForeignPtr_ ptr

eqAffinePtr :: forall curve. BLS_P curve => AffinePtr curve -> AffinePtr curve -> IO Bool
eqAffinePtr (AffinePtr a) (AffinePtr b) =
  (== 0) <$> c_memcmp (castPtr a) (castPtr b) (sizeAffine_ (Proxy @curve))

instance BLS_P curve => Eq (AffinePtr curve) where
  a == b = unsafePerformIO $ eqAffinePtr a b

---- Safe P types / marshalling

-- | A point on an elliptic curve. This type guarantees that the point is part of the
-- | prime order subgroup.
newtype P curve = P (ForeignPtr Void)

type P1 = P Curve1
type P2 = P Curve2

newtype Affine curve = Affine (ForeignPtr Void)

type Affine1 = Affine Curve1
type Affine2 = Affine Curve2

-- | Target element without the final exponantiation. By defining target elements
-- | as such, we save up the final exponantiation when computing a pairing, and only
-- | compute it when necessary (e.g. comparison with another point or serialisation)
newtype PT = PT (ForeignPtr Void)

-- | Sizes of various representations of elliptic curve points.
class BLS_P curve where
  sizeP_ :: Proxy curve -> CSize
  serializedSizeP_ :: Proxy curve -> CSize
  compressedSizeP_ :: Proxy curve -> CSize
  sizeAffine_ :: Proxy curve -> CSize

instance BLS_P curve => Eq (Affine curve) where
  a == b = unsafePerformIO $
    withAffine a $ \aptr ->
      withAffine b $ \bptr ->
        eqAffinePtr aptr bptr

-- | Size of a curve point in memory
sizeP :: forall curve. (BLS_P curve) => Proxy curve -> Int
sizeP = fromIntegral . sizeP_

-- | Size of a curved point when serialized in compressed form
compressedSizeP :: forall curve. (BLS_P curve) => Proxy curve -> Int
compressedSizeP = fromIntegral . compressedSizeP_

-- | Size of a curved point when serialized in uncompressed form
serializedSizeP :: forall curve. (BLS_P curve) => Proxy curve -> Int
serializedSizeP = fromIntegral . serializedSizeP_

-- | In-memory size of the affine representation of a curve point
sizeAffine :: forall curve. (BLS_P curve) => Proxy curve -> Int
sizeAffine = fromIntegral . sizeAffine_

withP :: forall a curve. P curve -> (PPtr curve -> IO a) -> IO a
withP (P p) go = withForeignPtr p (go . PPtr)

withNewP :: forall curve a. (BLS_P curve) => (PPtr curve -> IO a) -> IO (a, P curve)
withNewP go = do
  p <- mallocForeignPtrBytes (sizeP (Proxy @curve))
  x <- withForeignPtr p (go . PPtr)
  return (x, P p)

withNewP_ :: (BLS_P curve) => (PPtr curve -> IO a) -> IO a
withNewP_ = fmap fst . withNewP

withNewP' :: (BLS_P curve) => (PPtr curve -> IO a) -> IO (P curve)
withNewP' = fmap snd . withNewP

cloneP :: forall curve. (BLS_P curve) => P curve -> IO (P curve)
cloneP (P a) = do
  b <- mallocForeignPtrBytes (sizeP (Proxy @curve))
  withForeignPtr a $ \ap ->
    withForeignPtr b $ \bp ->
      copyBytes bp ap (sizeP (Proxy @curve))
  return (P b)

withAffine :: forall a curve. Affine curve -> (AffinePtr curve -> IO a) -> IO a
withAffine (Affine p) go = withForeignPtr p (go . AffinePtr)

withNewAffine :: forall curve a. (BLS_P curve) => (AffinePtr curve -> IO a) -> IO (a, Affine curve)
withNewAffine go = do
  p <- mallocForeignPtrBytes (sizeAffine (Proxy @curve))
  x <- withForeignPtr p (go . AffinePtr)
  return (x, Affine p)

withNewAffine_ :: (BLS_P curve) => (AffinePtr curve -> IO a) -> IO a
withNewAffine_ = fmap fst . withNewAffine

withNewAffine' :: (BLS_P curve) => (AffinePtr curve -> IO a) -> IO (Affine curve)
withNewAffine' = fmap snd . withNewAffine


withPT :: PT -> (PTPtr -> IO a) -> IO a
withPT (PT pt) go = withForeignPtr pt (go . PTPtr)

withNewPT :: (PTPtr -> IO a) -> IO (a, PT)
withNewPT go = do
  p <- mallocForeignPtrBytes sizePT
  x <- withForeignPtr p (go . PTPtr)
  return (x, PT p)

withNewPT_ :: (PTPtr -> IO a) -> IO a
withNewPT_ = fmap fst . withNewPT

withNewPT' :: (PTPtr -> IO a) -> IO PT
withNewPT' = fmap snd . withNewPT

instance BLS_P Curve1 where
  sizeP_ _ = c_size_blst_p1
  compressedSizeP_ _ = 48
  serializedSizeP_ _ = 96
  sizeAffine_ _ = c_size_blst_affine1

instance BLS_P Curve2 where
  sizeP_ _ = c_size_blst_p2
  compressedSizeP_ _ = 96
  serializedSizeP_ _ = 192
  sizeAffine_ _ = c_size_blst_affine2

sizePT :: Int
sizePT = fromIntegral c_size_blst_fp12


---- Curve operations

-- | BLS curve operations. Class methods are low-level; user code will want to
-- use higher-level wrappers such as 'addOrDouble', 'mult', 'cneg', 'neg', etc.
class BLS_Curve curve where
  c_blst_on_curve :: PPtr curve -> IO Bool

  c_blst_add_or_double :: PPtr curve -> PPtr curve -> PPtr curve -> IO ()
  c_blst_mult :: PPtr curve -> PPtr curve -> ScalarPtr -> CSize -> IO ()
  c_blst_cneg :: PPtr curve -> Bool -> IO ()

  c_blst_hash :: PPtr curve -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> IO ()
  c_blst_compress :: Ptr CChar -> PPtr curve -> IO ()
  c_blst_serialize :: Ptr CChar -> PPtr curve -> IO ()
  c_blst_uncompress :: AffinePtr curve -> Ptr CChar -> IO CInt
  c_blst_deserialize :: AffinePtr curve -> Ptr CChar -> IO CInt

  c_blst_in_g :: PPtr curve -> IO Bool
  c_blst_to_affine :: AffinePtr curve -> PPtr curve -> IO ()
  c_blst_from_affine :: PPtr curve -> AffinePtr curve -> IO ()
  c_blst_affine_in_g :: AffinePtr curve -> IO Bool
  c_blst_generator :: PPtr curve

  c_blst_p_is_equal :: PPtr curve -> PPtr curve -> IO Bool
  c_blst_p_is_inf :: PPtr curve -> IO Bool

instance BLS_Curve Curve1 where
  c_blst_on_curve = c_blst_p1_on_curve

  c_blst_add_or_double = c_blst_p1_add_or_double
  c_blst_mult = c_blst_p1_mult
  c_blst_cneg = c_blst_p1_cneg

  c_blst_hash = c_blst_hash_to_g1
  c_blst_compress = c_blst_p1_compress
  c_blst_serialize = c_blst_p1_serialize
  c_blst_uncompress = c_blst_p1_uncompress
  c_blst_deserialize = c_blst_p1_deserialize

  c_blst_in_g = c_blst_p1_in_g1
  c_blst_to_affine = c_blst_p1_to_affine
  c_blst_from_affine = c_blst_p1_from_affine
  c_blst_affine_in_g = c_blst_p1_affine_in_g1

  c_blst_generator = c_blst_p1_generator

  c_blst_p_is_equal = c_blst_p1_is_equal
  c_blst_p_is_inf = c_blst_p1_is_inf

instance BLS_Curve Curve2 where
  c_blst_on_curve = c_blst_p2_on_curve

  c_blst_add_or_double = c_blst_p2_add_or_double
  c_blst_mult = c_blst_p2_mult
  c_blst_cneg = c_blst_p2_cneg

  c_blst_hash = c_blst_hash_to_g2
  c_blst_compress = c_blst_p2_compress
  c_blst_serialize = c_blst_p2_serialize
  c_blst_uncompress = c_blst_p2_uncompress
  c_blst_deserialize = c_blst_p2_deserialize

  c_blst_in_g = c_blst_p2_in_g2
  c_blst_to_affine = c_blst_p2_to_affine
  c_blst_from_affine = c_blst_p2_from_affine
  c_blst_affine_in_g = c_blst_p2_affine_in_g2

  c_blst_generator = c_blst_p2_generator

  c_blst_p_is_equal = c_blst_p2_is_equal
  c_blst_p_is_inf = c_blst_p2_is_inf

---- Safe Scalar types / marshalling

sizeScalar :: Int
sizeScalar = fromIntegral c_size_blst_scalar

newtype Scalar = Scalar (ForeignPtr Void)

withIntScalar :: Integer -> (ScalarPtr -> IO a) -> IO a
withIntScalar i go = do
  s <- scalarFromInteger i
  withScalar s go

withScalar :: Scalar -> (ScalarPtr -> IO a) -> IO a
withScalar (Scalar p2) go = do
  withForeignPtr p2 (go . ScalarPtr)

withNewScalar :: (ScalarPtr -> IO a) -> IO (a, Scalar)
withNewScalar go = do
  p2 <- mallocForeignPtrBytes sizeScalar
  x <- withForeignPtr p2 (go . ScalarPtr)
  return (x, Scalar p2)

withNewScalar_ :: (ScalarPtr -> IO a) -> IO a
withNewScalar_ = fmap fst . withNewScalar

withNewScalar' :: (ScalarPtr -> IO a) -> IO Scalar
withNewScalar' = fmap snd . withNewScalar

cloneScalar :: Scalar -> IO Scalar
cloneScalar (Scalar a) = do
  b <- mallocForeignPtrBytes sizeScalar
  withForeignPtr a $ \ap ->
    withForeignPtr b $ \bp ->
      copyBytes bp ap sizeScalar
  return (Scalar b)

sizeFr :: Int
sizeFr = fromIntegral c_size_blst_fr

newtype Fr = Fr (ForeignPtr Void)

withFr :: Fr -> (FrPtr -> IO a) -> IO a
withFr (Fr p2) go = do
  withForeignPtr p2 (go . FrPtr)

withNewFr :: (FrPtr -> IO a) -> IO (a, Fr)
withNewFr go = do
  p2 <- mallocForeignPtrBytes sizeFr
  x <- withForeignPtr p2 (go . FrPtr)
  return (x, Fr p2)

withNewFr_ :: (FrPtr -> IO a) -> IO a
withNewFr_ = fmap fst . withNewFr

withNewFr' :: (FrPtr -> IO a) -> IO Fr
withNewFr' = fmap snd . withNewFr

cloneFr :: Fr -> IO Fr
cloneFr (Fr a) = do
  b <- mallocForeignPtrBytes sizeFr
  withForeignPtr a $ \ap ->
    withForeignPtr b $ \bp ->
      copyBytes bp ap sizeFr
  return (Fr b)

scalarToInteger :: Scalar -> IO Integer
scalarToInteger scalar = withScalar scalar $ \scalarPtr -> do
  allocaBytes sizeScalar $ \rawPtr -> do
    c_blst_bendian_from_scalar rawPtr scalarPtr
    cstrToInteger rawPtr sizeScalar

cstrToInteger :: Ptr CChar -> Int -> IO Integer
cstrToInteger p l = do
  go l (castPtr p)
  where
    go :: Int -> Ptr CUChar -> IO Integer
    go 0 _ = return 0
    go n ptr = do
      val <- peek ptr
      res <- go (pred n) (plusPtr ptr 1)
      return $ res .|. shiftL (fromIntegral val) (8 * pred n)

integerToBS :: Integer -> ByteString
integerToBS k
  | k < 0 = error "Cannot convert negative Integer to ByteString"
  | otherwise = go 0 [] k
  where
    go !i !acc 0 = BSI.unsafePackLenBytes i acc
    go !i !acc n = go (i + 1) (fromIntegral n : acc) (n `shiftR` 8)

padBS :: Int -> ByteString -> ByteString
padBS i b
  | i > BS.length b
  = BS.replicate (i - BS.length b) 0 <> b
  | otherwise
  = b

integerAsCStrL :: Int -> Integer -> (Ptr CChar -> Int -> IO a) -> IO a
integerAsCStrL i n f = do
  let bs = padBS i $ integerToBS n
  BS.useAsCStringLen bs $ uncurry f

scalarFromInteger :: Integer -> IO Scalar
scalarFromInteger n = do
  withNewScalar' $ \scalarPtr -> do
    integerAsCStrL sizeScalar (n `mod` scalarPeriod) $ \str _length -> do
      c_blst_scalar_from_bendian scalarPtr str

---- Unsafe types

newtype ScalarPtr = ScalarPtr (Ptr Void)
newtype FrPtr = FrPtr (Ptr Void)

---- Raw Scalar / Fr functions

foreign import ccall "size_blst_scalar" c_size_blst_scalar :: CSize
foreign import ccall "size_blst_fr" c_size_blst_fr :: CSize

foreign import ccall "blst_scalar_fr_check" c_blst_scalar_fr_check :: ScalarPtr -> IO Bool

foreign import ccall "blst_scalar_from_fr" c_blst_scalar_from_fr :: ScalarPtr -> FrPtr -> IO ()
foreign import ccall "blst_fr_from_scalar" c_blst_fr_from_scalar :: FrPtr -> ScalarPtr -> IO ()
foreign import ccall "blst_scalar_from_be_bytes" c_blst_scalar_from_be_bytes :: ScalarPtr -> Ptr CChar -> CSize -> IO Bool
foreign import ccall "blst_scalar_from_bendian" c_blst_scalar_from_bendian :: ScalarPtr -> Ptr CChar -> IO ()

---- Raw P1 functions

foreign import ccall "size_blst_p1" c_size_blst_p1 :: CSize
foreign import ccall "blst_p1_on_curve" c_blst_p1_on_curve :: P1Ptr -> IO Bool

foreign import ccall "blst_p1_add_or_double" c_blst_p1_add_or_double :: P1Ptr -> P1Ptr -> P1Ptr -> IO ()
foreign import ccall "blst_p1_mult" c_blst_p1_mult :: P1Ptr -> P1Ptr -> ScalarPtr -> CSize -> IO ()
foreign import ccall "blst_p1_cneg" c_blst_p1_cneg :: P1Ptr -> Bool -> IO ()

foreign import ccall "blst_hash_to_g1" c_blst_hash_to_g1 :: P1Ptr -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> IO ()
foreign import ccall "blst_p1_compress" c_blst_p1_compress :: Ptr CChar -> P1Ptr -> IO ()
foreign import ccall "blst_p1_serialize" c_blst_p1_serialize :: Ptr CChar -> P1Ptr -> IO ()
foreign import ccall "blst_p1_uncompress" c_blst_p1_uncompress :: Affine1Ptr -> Ptr CChar -> IO CInt
foreign import ccall "blst_p1_deserialize" c_blst_p1_deserialize :: Affine1Ptr -> Ptr CChar -> IO CInt

foreign import ccall "blst_p1_in_g1" c_blst_p1_in_g1 :: P1Ptr -> IO Bool

foreign import ccall "blst_p1_generator" c_blst_p1_generator :: P1Ptr

foreign import ccall "blst_p1_is_equal" c_blst_p1_is_equal :: P1Ptr -> P1Ptr -> IO Bool
foreign import ccall "blst_p1_is_inf" c_blst_p1_is_inf :: P1Ptr -> IO Bool

---- Raw P2 functions

foreign import ccall "size_blst_p2" c_size_blst_p2 :: CSize
foreign import ccall "blst_p2_on_curve" c_blst_p2_on_curve :: P2Ptr -> IO Bool

foreign import ccall "blst_p2_add_or_double" c_blst_p2_add_or_double :: P2Ptr -> P2Ptr -> P2Ptr -> IO ()
foreign import ccall "blst_p2_mult" c_blst_p2_mult :: P2Ptr -> P2Ptr -> ScalarPtr -> CSize -> IO ()
foreign import ccall "blst_p2_cneg" c_blst_p2_cneg :: P2Ptr -> Bool -> IO ()

foreign import ccall "blst_hash_to_g2" c_blst_hash_to_g2 :: P2Ptr -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> Ptr CChar -> CSize -> IO ()
foreign import ccall "blst_p2_compress" c_blst_p2_compress :: Ptr CChar -> P2Ptr -> IO ()
foreign import ccall "blst_p2_serialize" c_blst_p2_serialize :: Ptr CChar -> P2Ptr -> IO ()
foreign import ccall "blst_p2_uncompress" c_blst_p2_uncompress :: Affine2Ptr -> Ptr CChar -> IO CInt
foreign import ccall "blst_p2_deserialize" c_blst_p2_deserialize :: Affine2Ptr -> Ptr CChar -> IO CInt

foreign import ccall "blst_p2_in_g2" c_blst_p2_in_g2 :: P2Ptr -> IO Bool

foreign import ccall "blst_p2_generator" c_blst_p2_generator :: P2Ptr

foreign import ccall "blst_p2_is_equal" c_blst_p2_is_equal :: P2Ptr -> P2Ptr -> IO Bool
foreign import ccall "blst_p2_is_inf" c_blst_p2_is_inf :: P2Ptr -> IO Bool

---- Affine operations

foreign import ccall "size_blst_affine1" c_size_blst_affine1 :: CSize
foreign import ccall "size_blst_affine2" c_size_blst_affine2 :: CSize

foreign import ccall "blst_p1_to_affine" c_blst_p1_to_affine :: AffinePtr Curve1 -> PPtr Curve1 -> IO ()
foreign import ccall "blst_p2_to_affine" c_blst_p2_to_affine :: AffinePtr Curve2 -> PPtr Curve2 -> IO ()
foreign import ccall "blst_p1_from_affine" c_blst_p1_from_affine :: PPtr Curve1 -> AffinePtr Curve1 -> IO ()
foreign import ccall "blst_p2_from_affine" c_blst_p2_from_affine :: PPtr Curve2 -> AffinePtr Curve2 -> IO ()

foreign import ccall "blst_p1_affine_in_g1" c_blst_p1_affine_in_g1 :: AffinePtr Curve1 -> IO Bool
foreign import ccall "blst_p2_affine_in_g2" c_blst_p2_affine_in_g2 :: AffinePtr Curve2 -> IO Bool

---- PT operations

foreign import ccall "size_blst_fp12" c_size_blst_fp12 :: CSize
foreign import ccall "blst_fp12_mul" c_blst_fp12_mul :: PTPtr -> PTPtr -> PTPtr -> IO ()
foreign import ccall "blst_fp12_is_equal" c_blst_fp12_is_equal :: PTPtr -> PTPtr -> IO Bool
foreign import ccall "blst_fp12_finalverify" c_blst_fp12_finalverify :: PTPtr -> PTPtr -> IO Bool

---- Pairing

foreign import ccall "blst_miller_loop" c_blst_miller_loop :: PTPtr -> Affine2Ptr -> Affine1Ptr -> IO ()

---- Raw BLST error constants

foreign import ccall "blst_success" c_blst_success :: CInt
foreign import ccall "blst_error_bad_encoding" c_blst_error_bad_encoding :: CInt
foreign import ccall "blst_error_point_not_on_curve" c_blst_error_point_not_on_curve :: CInt
foreign import ccall "blst_error_point_not_in_group" c_blst_error_point_not_in_group :: CInt
foreign import ccall "blst_error_aggr_type_mismatch" c_blst_error_aggr_type_mismatch :: CInt
foreign import ccall "blst_error_verify_fail" c_blst_error_verify_fail :: CInt
foreign import ccall "blst_error_pk_is_infinity" c_blst_error_pk_is_infinity :: CInt
foreign import ccall "blst_error_bad_scalar" c_blst_error_bad_scalar :: CInt

---- Utility functions

foreign import ccall "memcmp" c_memcmp :: Ptr a -> Ptr a -> CSize -> IO CSize
foreign import ccall "blst_bendian_from_scalar" c_blst_bendian_from_scalar :: Ptr CChar -> ScalarPtr -> IO ()

data BLSTError
  = BLST_SUCCESS
  | BLST_BAD_ENCODING
  | BLST_POINT_NOT_ON_CURVE
  | BLST_POINT_NOT_IN_GROUP
  | BLST_AGGR_TYPE_MISMATCH
  | BLST_VERIFY_FAIL
  | BLST_PK_IS_INFINITY
  | BLST_BAD_SCALAR
  | BLST_UNKNOWN_ERROR
  deriving stock (Show, Eq, Ord, Enum, Bounded)

mkBLSTError :: CInt -> BLSTError
mkBLSTError e
  | e == c_blst_success
  = BLST_SUCCESS
  | e == c_blst_error_bad_encoding
  = BLST_BAD_ENCODING
  | e == c_blst_error_point_not_on_curve
  = BLST_POINT_NOT_ON_CURVE
  | e == c_blst_error_point_not_in_group
  = BLST_POINT_NOT_IN_GROUP
  | e == c_blst_error_aggr_type_mismatch
  = BLST_AGGR_TYPE_MISMATCH
  | e == c_blst_error_verify_fail
  = BLST_VERIFY_FAIL
  | e == c_blst_error_pk_is_infinity
  = BLST_PK_IS_INFINITY
  | e == c_blst_error_bad_scalar
  = BLST_BAD_SCALAR
  | otherwise
  = BLST_UNKNOWN_ERROR

-- | This class represents phantom types that can be used as BLS curves.
class (BLS_Curve a, BLS_P a) => BLS a where

instance BLS Curve1 where

instance BLS Curve2 where

---- Curve point operations

instance BLS curve => Eq (P curve) where
  a == b = unsafePerformIO $ do
    withP a $ \aptr ->
      withP b $ \bptr ->
        c_blst_p_is_equal aptr bptr

instance Eq Scalar where
  a == b = scalarToBS a == scalarToBS b

instance Eq Fr where
  a == b = unsafePerformIO $
    (==) <$> scalarFromFr a <*> scalarFromFr b

-- | Check whether a point is in the group corresponding to its elliptic curve
inGroup :: BLS_Curve curve => P curve -> Bool
inGroup p = unsafePerformIO $ withP p c_blst_in_g

-- | Curve point addition.
addOrDouble :: (BLS curve) => P curve -> P curve -> P curve
addOrDouble in1 in2 = unsafePerformIO $ do
  withNewP' $ \outp -> do
    withP in1 $ \in1p -> do
      withP in2 $ \in2p -> do
        c_blst_add_or_double outp in1p in2p

-- | Scalar multiplication of a curve point. The scalar will be brought into
-- the range of modular arithmetic by means of a modulo operation over the
-- 'scalarPeriod'. Negative number will also be brought to the range
-- [0, 'scalarPeriod' - 1] via modular reduction.
mult :: (BLS curve) => P curve -> Integer -> P curve
mult in1 inS = unsafePerformIO $ do
  withNewP' $ \outp -> do
    withP in1 $ \in1p -> do
      withIntScalar inS $ \inSp -> do
        -- Multiply by 8, because blst_mult takes number of *bits*, but
        -- sizeScalar is in *bytes*
        c_blst_mult outp in1p inSp (fromIntegral sizeScalar * 8)

-- | Conditional curve point negation.
-- @cneg x cond = if cond then neg x else x@
cneg :: (BLS curve) => P curve -> Bool -> P curve
cneg in1 cond = unsafePerformIO $ do
  out1 <- cloneP in1
  withP out1 $ \out1p ->
    c_blst_cneg out1p cond
  return out1

-- | Unconditional curve point negation
neg :: (BLS curve) => P curve -> P curve
neg p = cneg p True

uncompress :: forall curve. (BLS_P curve, BLS_Curve curve) => ByteString -> Either BLSTError (P curve)
uncompress bs = unsafePerformIO $ do
  BSU.unsafeUseAsCStringLen bs $ \(bytes, numBytes) ->
    if numBytes == compressedSizeP (Proxy @curve) then do
      (err, affine) <- withNewAffine $ \ap -> c_blst_uncompress ap bytes
      let p = fromAffine affine
      if err /= 0 then
        return $ Left $ mkBLSTError err
      else
        if inGroup p then
         return $ Right p
        else
          return $ Left BLST_POINT_NOT_IN_GROUP
    else do
      return $ Left BLST_BAD_ENCODING

deserialize :: forall curve. (BLS_P curve, BLS_Curve curve) => ByteString -> Either BLSTError (P curve)
deserialize bs = unsafePerformIO $ do
  BSU.unsafeUseAsCStringLen bs $ \(bytes, numBytes) ->
    if numBytes == serializedSizeP (Proxy @curve) then do
      (err, affine) <- withNewAffine $ \ap -> c_blst_deserialize ap bytes
      let p = fromAffine affine
      if err /= 0 then
        return $ Left $ mkBLSTError err
      else
        if inGroup p then
         return $ Right p
        else
          return $ Left BLST_POINT_NOT_IN_GROUP
    else do
      return $ Left BLST_BAD_ENCODING

compress :: forall curve. (BLS_P curve, BLS_Curve curve) => P curve -> ByteString
compress p = BSI.fromForeignPtr0 (castForeignPtr ptr) (compressedSizeP (Proxy @curve))
    where
        ptr = unsafePerformIO $ do
          cstr <- mallocForeignPtrBytes (compressedSizeP (Proxy @curve))
          withForeignPtr cstr $ \cstrp -> do
            withP p $ \pp -> do
              c_blst_compress cstrp pp
          return cstr

serialize :: forall curve. (BLS_P curve, BLS_Curve curve) => P curve -> ByteString
serialize p = BSI.fromForeignPtr0 (castForeignPtr ptr) (serializedSizeP (Proxy @curve))
    where
        ptr = unsafePerformIO $ do
          cstr <- mallocForeignPtrBytes (serializedSizeP (Proxy @curve))
          withForeignPtr cstr $ \cstrp -> do
            withP p $ \pp -> do
              c_blst_serialize cstrp pp
          return cstr

-- | @hash msg mDST mAug@ generates the elliptic curve hash for the given
-- message @msg@; @mDST@ and @mAug@ are the optional @aug@ and @dst@
-- arguments.
hash :: (BLS_P curve, BLS_Curve curve) => ByteString -> Maybe ByteString -> Maybe ByteString -> P curve
hash msg mDST mAug = unsafePerformIO $
  BSU.unsafeUseAsCStringLen msg $ \(msgPtr, msgLen) ->
    withMaybeCStringLen mDST $ \(dstPtr, dstLen) ->
      withMaybeCStringLen mAug $ \(augPtr, augLen) ->
        withNewP' $ \pPtr ->
          c_blst_hash pPtr msgPtr (fromIntegral msgLen) dstPtr (fromIntegral dstLen) augPtr (fromIntegral augLen)

toAffine :: (BLS_P curve, BLS_Curve curve) => P curve -> Affine curve
toAffine p = unsafePerformIO $
  withP p $ \pp ->
    withNewAffine' $ \affinePtr ->
      c_blst_to_affine affinePtr pp

fromAffine :: (BLS_P curve, BLS_Curve curve) => Affine curve -> P curve
fromAffine affine = unsafePerformIO $
  withAffine affine $ \affinePtr ->
    withNewP' $ \pp ->
      c_blst_from_affine pp affinePtr

-- | Infinity check on curve points.
isInf :: (BLS_Curve curve) => P curve -> Bool
isInf p = unsafePerformIO $ withP p c_blst_p_is_inf

affineInG :: (BLS_Curve curve) => Affine curve -> Bool
affineInG affine = unsafePerformIO $
  withAffine affine c_blst_affine_in_g

generator :: (BLS_Curve curve) => P curve
generator = unsafePFromPPtr c_blst_generator

---- Scalar / Fr operations

scalarFromFr :: Fr -> IO Scalar
scalarFromFr fr =
  withNewScalar' $ \scalarPtr ->
    withFr fr $ \frPtr ->
      c_blst_scalar_from_fr scalarPtr frPtr

frFromScalar :: Scalar -> IO Fr
frFromScalar scalar =
    withNewFr' $ \frPtr ->
      withScalar scalar $ \scalarPtr ->
        c_blst_fr_from_scalar frPtr scalarPtr

frFromCanonicalScalar :: Scalar -> IO (Maybe Fr)
frFromCanonicalScalar scalar
  | scalarCanonical scalar
  = Just <$> frFromScalar scalar
  | otherwise
  = return Nothing

scalarFromBS :: ByteString -> Either BLSTError Scalar
scalarFromBS bs = unsafePerformIO $ do
  BSU.unsafeUseAsCStringLen bs $ \(cstr, l) ->
    if l == sizeScalar then do
      (success, scalar) <- withNewScalar $ \scalarPtr ->
        c_blst_scalar_from_be_bytes scalarPtr cstr (fromIntegral l)
      if success then
        return $ Right scalar
      else
        return $ Left BLST_BAD_SCALAR
    else
      return $ Left BLST_BAD_SCALAR

scalarToBS :: Scalar -> ByteString
scalarToBS scalar = BSI.fromForeignPtr0 (castForeignPtr ptr) sizeScalar
   where
       ptr = unsafePerformIO $ do
          cstr <- mallocForeignPtrBytes sizeScalar
          withForeignPtr cstr $ \cstrp -> do
            withScalar scalar $ \scalarPtr -> do
              c_blst_bendian_from_scalar cstrp scalarPtr
          return cstr

scalarCanonical :: Scalar -> Bool
scalarCanonical scalar = unsafePerformIO $
  withScalar scalar c_blst_scalar_fr_check

---- PT operations

ptMult :: PT -> PT -> PT
ptMult a b = unsafePerformIO $
  withPT a $ \ap ->
    withPT b $ \bp ->
      withNewPT' $ \cp ->
        c_blst_fp12_mul cp ap bp

ptEq :: PT -> PT -> Bool
ptEq a b = unsafePerformIO $
  withPT a $ \ap ->
    withPT b $ \bp ->
      c_blst_fp12_is_equal ap bp

ptFinalVerify :: PT -> PT -> Bool
ptFinalVerify a b = unsafePerformIO $
  withPT a $ \ap ->
    withPT b $ \bp ->
      c_blst_fp12_finalverify ap bp

instance Eq PT where
  (==) = ptEq

---- Pairings

miller_loop :: P1 -> P2 -> Either BLSTError PT
miller_loop p1 p2 =
  Right . unsafePerformIO $
    withAffine (toAffine p1) $ \ap1 ->
      withAffine (toAffine p2) $ \ap2 ->
        withNewPT' $ \ppt ->
          c_blst_miller_loop ppt ap2 ap1

---- Utility

withMaybeCStringLen :: Maybe ByteString -> (CStringLen -> IO a) -> IO a
withMaybeCStringLen Nothing go   = go (nullPtr, 0)
withMaybeCStringLen (Just bs) go = BSU.unsafeUseAsCStringLen bs go

-- | The period of scalar modulo operations.
scalarPeriod :: Integer
scalarPeriod = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

