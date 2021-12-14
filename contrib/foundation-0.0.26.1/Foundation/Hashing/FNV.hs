-- |
-- Module      : Foundation.Hashing.FNV.FNV
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : good
--
-- Fowler Noll Vo Hash (1 and 1a / 32 / 64 bits versions)
-- <http://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function>
--
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE BangPatterns               #-}
module Foundation.Hashing.FNV
    (
    -- * types
      FNV1Hash32(..)
    , FNV1Hash64(..)
    , FNV1_32
    , FNV1a_32
    , FNV1_64
    , FNV1a_64
    ) where

import           Basement.Block (Block(..))
import           Basement.Compat.Base
import qualified Basement.UArray as A
import           Basement.Types.OffsetSize
import           Basement.PrimType
import           Basement.IntegralConv
import           Foundation.Numerical
import           Foundation.Hashing.Hasher
import           Data.Bits
import           GHC.ST

-- | FNV1(a) hash (32 bit variants)
newtype FNV1Hash32 = FNV1Hash32 Word32
    deriving (Show,Eq,Ord)

-- | FNV1(a) hash (64 bit variants)
newtype FNV1Hash64 = FNV1Hash64 Word64
    deriving (Show,Eq,Ord)

xor32 :: Word -> Word8 -> Word
xor32 !a !b = a `xor` integralUpsize b
{-# INLINE xor32 #-}

xor64 :: Word64 -> Word8 -> Word64
xor64 !a !b = a `xor` integralUpsize b
{-# INLINE xor64 #-}

-- | FNV1 32 bit state
newtype FNV1_32 = FNV1_32 Word

-- | FNV1 64 bit state
newtype FNV1_64 = FNV1_64 Word64

-- | FNV1a 32 bit state
newtype FNV1a_32 = FNV1a_32 Word

-- | FNV1a 64 bit state
newtype FNV1a_64 = FNV1a_64 Word64

fnv1_32_Mix8 :: Word8 -> FNV1_32 -> FNV1_32
fnv1_32_Mix8 !w (FNV1_32 acc) = FNV1_32 (0x01000193 * acc `xor32` w)
{-# INLINE fnv1_32_Mix8 #-}

fnv1a_32_Mix8 :: Word8 -> FNV1a_32 -> FNV1a_32
fnv1a_32_Mix8 !w (FNV1a_32 acc) = FNV1a_32 (0x01000193 * (acc `xor32` w))
{-# INLINE fnv1a_32_Mix8 #-}

fnv1_64_Mix8 :: Word8 -> FNV1_64 -> FNV1_64
fnv1_64_Mix8 !w (FNV1_64 acc) = FNV1_64 (0x100000001b3 * acc `xor64` w)
{-# INLINE fnv1_64_Mix8 #-}

fnv1a_64_Mix8 :: Word8 -> FNV1a_64 -> FNV1a_64
fnv1a_64_Mix8 !w (FNV1a_64 acc) = FNV1a_64 (0x100000001b3 * (acc `xor64` w))
{-# INLINE fnv1a_64_Mix8 #-}

instance Hasher FNV1_32 where
    type HashResult FNV1_32 = FNV1Hash32
    type HashInitParam FNV1_32 = Word
    hashNew = FNV1_32 0
    hashNewParam w = FNV1_32 w
    hashEnd (FNV1_32 w) = FNV1Hash32 (integralDownsize w)
    hashMix8 = fnv1_32_Mix8
    hashMixBytes = fnv1_32_mixBa

instance Hasher FNV1a_32 where
    type HashResult FNV1a_32 = FNV1Hash32
    type HashInitParam FNV1a_32 = Word
    hashNew = FNV1a_32 0
    hashNewParam w = FNV1a_32 w
    hashEnd (FNV1a_32 w) = FNV1Hash32 (integralDownsize w)
    hashMix8 = fnv1a_32_Mix8
    hashMixBytes = fnv1a_32_mixBa

instance Hasher FNV1_64 where
    type HashResult FNV1_64 = FNV1Hash64
    type HashInitParam FNV1_64 = Word64
    hashNew = FNV1_64 0xcbf29ce484222325
    hashNewParam w = FNV1_64 w
    hashEnd (FNV1_64 w) = FNV1Hash64 w
    hashMix8 = fnv1_64_Mix8
    hashMixBytes = fnv1_64_mixBa

instance Hasher FNV1a_64 where
    type HashResult FNV1a_64 = FNV1Hash64
    type HashInitParam FNV1a_64 = Word64
    hashNew = FNV1a_64 0xcbf29ce484222325
    hashNewParam w = FNV1a_64 w
    hashEnd (FNV1a_64 w) = FNV1Hash64 w
    hashMix8 = fnv1a_64_Mix8
    hashMixBytes = fnv1a_64_mixBa

-- | compute FNV1 (32 bit variant) of a raw piece of memory
fnv1_32_mixBa :: PrimType a => A.UArray a -> FNV1_32 -> FNV1_32
fnv1_32_mixBa baA !initialState = A.unsafeDewrap goVec goAddr ba
  where
    ba :: A.UArray Word8
    ba = A.unsafeRecast baA

    goVec :: Block Word8 -> Offset Word8 -> FNV1_32
    goVec (Block !ma) !start = loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primBaIndex ma idx) acc)
    {-# INLINE goVec #-}

    goAddr :: Ptr Word8 -> Offset Word8 -> ST s FNV1_32
    goAddr (Ptr ptr) !start = return $ loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primAddrIndex ptr idx) acc)
    {-# INLINE goAddr #-}

-- | compute FNV1a (32 bit variant) of a raw piece of memory
fnv1a_32_mixBa :: PrimType a => A.UArray a -> FNV1a_32 -> FNV1a_32
fnv1a_32_mixBa baA !initialState  = A.unsafeDewrap goVec goAddr ba
  where
    ba :: A.UArray Word8
    ba = A.unsafeRecast baA

    goVec :: Block Word8 -> Offset Word8 -> FNV1a_32
    goVec (Block !ma) !start = loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primBaIndex ma idx) acc)
    {-# INLINE goVec #-}

    goAddr :: Ptr Word8 -> Offset Word8 -> ST s FNV1a_32
    goAddr (Ptr ptr) !start = return $ loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primAddrIndex ptr idx) acc)
    {-# INLINE goAddr #-}

-- | compute FNV1 (64 bit variant) of a raw piece of memory
fnv1_64_mixBa :: PrimType a => A.UArray a -> FNV1_64 -> FNV1_64
fnv1_64_mixBa baA !initialState = A.unsafeDewrap goVec goAddr ba
  where
    ba :: A.UArray Word8
    ba = A.unsafeRecast baA

    goVec :: Block Word8 -> Offset Word8 -> FNV1_64
    goVec (Block !ma) !start = loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primBaIndex ma idx) acc)
    {-# INLINE goVec #-}

    goAddr :: Ptr Word8 -> Offset Word8 -> ST s FNV1_64
    goAddr (Ptr ptr) !start = return $ loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primAddrIndex ptr idx) acc)
    {-# INLINE goAddr #-}

-- | compute FNV1a (64 bit variant) of a raw piece of memory
fnv1a_64_mixBa :: PrimType a => A.UArray a -> FNV1a_64 -> FNV1a_64
fnv1a_64_mixBa baA !initialState = A.unsafeDewrap goVec goAddr ba
  where
    ba :: A.UArray Word8
    ba = A.unsafeRecast baA

    goVec :: Block Word8 -> Offset Word8 -> FNV1a_64
    goVec (Block !ma) !start = loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primBaIndex ma idx) acc)
    {-# INLINE goVec #-}

    goAddr :: Ptr Word8 -> Offset Word8 -> ST s FNV1a_64
    goAddr (Ptr ptr) !start = return $ loop start initialState
      where
        !len = start `offsetPlusE` A.length ba
        loop !idx !acc
            | idx >= len = acc
            | otherwise  = loop (idx + Offset 1) (hashMix8 (primAddrIndex ptr idx) acc)
    {-# INLINE goAddr #-}
