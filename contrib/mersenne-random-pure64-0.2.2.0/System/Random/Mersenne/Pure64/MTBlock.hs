{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
--------------------------------------------------------------------
-- |
-- Module     : System.Random.Mersenne.Pure64
-- Copyright  : Copyright (c) 2008, Bertram Felgenhauer <int-e@gmx.de>
-- License    : BSD3
-- Maintainer : Don Stewart <dons@galois.com>
-- Stability  : experimental
-- Portability:
-- Tested with: GHC 6.8.3
--
-- A purely functional binding 64 bit binding to the classic mersenne
-- twister random number generator. This is more flexible than the
-- impure 'mersenne-random' library, at the cost of being a bit slower.
-- This generator is however, many times faster than System.Random,
-- and yields high quality randoms with a long period.
--
module System.Random.Mersenne.Pure64.MTBlock (
    -- * Block type
    MTBlock,

    -- * Block functions
    seedBlock,
    nextBlock,
    lookupBlock,

    -- * Misc functions
    blockLen,
    mixWord64,
) where

import GHC.Exts
#if __GLASGOW_HASKELL__ >= 706
import GHC.IO
#else
import GHC.IOBase
#endif
import GHC.Word
import System.Random.Mersenne.Pure64.Base
import System.Random.Mersenne.Pure64.Internal

allocateBlock :: IO MTBlock
allocateBlock =
    IO $ \s0 -> case newPinnedByteArray# blockSize# s0 of
        (# s1, b0 #) -> case unsafeFreezeByteArray# b0 s1 of
            (# s2, b1 #) -> (# s2, MTBlock b1 #)
  where
    !(I# blockSize#) = blockSize

blockAsPtr :: MTBlock -> Ptr a
blockAsPtr (MTBlock b) = Ptr (byteArrayContents# b)

-- | create a new MT block, seeded with the given Word64 value
seedBlock :: Word64 -> MTBlock
seedBlock seed = unsafeDupablePerformIO $ do
    b <- allocateBlock
    c_seed_genrand64_block (blockAsPtr b) seed
    c_next_genrand64_block (blockAsPtr b) (blockAsPtr b)
    touch b
    return b
{-# NOINLINE seedBlock #-}

-- | step: create a new MTBlock buffer from the previous one
nextBlock :: MTBlock -> MTBlock
nextBlock b = unsafeDupablePerformIO $ do
    new <- allocateBlock
    c_next_genrand64_block (blockAsPtr b) (blockAsPtr new)
    touch b
    touch new
    return new
{-# NOINLINE nextBlock #-}

-- stolen from GHC.ForeignPtr - make sure the argument is still alive.
touch :: a -> IO ()
touch r = IO $ \s0 -> case touch# r s0 of s1 -> (# s1, () #)

-- | look up an element of an MT block
lookupBlock :: MTBlock -> Int -> Word64
lookupBlock (MTBlock b) (I# i) = W64# (indexWord64Array# b i)

-- | MT's word mix function.
--
-- (MT applies this function to each Word64 from the buffer before returning it)
mixWord64 :: Word64 -> Word64
mixWord64 = c_mix_word64

-- Alternative implementation - it's probably faster on 64 bit machines, but
-- on Athlon XP it loses.
{-
mixWord64 (W64# x0) = let
    W64# x1 = W64# x0 `xor` (W64# (x0 `uncheckedShiftRL64#` 28#) .&. 0x5555555555555555)
    W64# x2 = W64# x1 `xor` (W64# (x1 `uncheckedShiftL64#` 17#) .&. 0x71D67FFFEDA60000)
    W64# x3 = W64# x2 `xor` (W64# (x2 `uncheckedShiftL64#` 37#) .&. 0xFFF7EEE000000000)
    W64# x4 = W64# x3 `xor` (W64# (x3 `uncheckedShiftRL64#` 43#))
  in
    W64# x4
-}
