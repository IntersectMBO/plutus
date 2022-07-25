-- editorconfig-checker-disable-file
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MultiWayIf         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE UnboxedSums        #-}

module Bitwise (
  integerToByteString,
  byteStringToInteger,
  andByteString,
  iorByteString,
  xorByteString,
  complementByteString,
  popCountByteString,
  testBitByteString,
  writeBitByteString,
  findFirstSetByteString,
  shiftByteString,
  rotateByteString,
  ) where

import Control.Monad (foldM, when)
import Control.Monad.State.Strict (State, evalState, get, modify, put)
import Data.Bits (FiniteBits, bit, complement, popCount, rotate, shift, shiftL, xor, zeroBits, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCString, unsafeUseAsCStringLen)
import Data.Foldable (foldl', for_)
import Data.Functor (void)
import Data.Kind (Type)
import Data.Text (Text, pack)
import Data.Word (Word64, Word8)
import Foreign.C.Types (CChar, CSize)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (Storable (peek, poke, sizeOf))
import GHC.Exts (fromList, fromListN)
import GHC.IO.Handle.Text (memcpy)
import PlutusCore.Builtin.Emitter (Emitter, emit)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))
import System.IO.Unsafe (unsafeDupablePerformIO)

{-# NOINLINE rotateByteString #-}
rotateByteString :: ByteString -> Integer -> ByteString
rotateByteString bs i
  -- If a ByteString is completely homogenous, rotating won't change it. This
  -- also covers emptiness, since empty ByteStrings are homogenous vacuously.
  | isAllZero bs || isAllOne bs = bs
  -- Rotating by more than the number of bits in a ByteString 'wraps around',
  -- so we're only interested in the rotation modulo the number of bits.
  | otherwise = case i `rem` bitLen of
            -- Means we have a multiple of the bit count, so nothing to do.
            0         -> bs
            magnitude -> overPtrLen bs $ \ptr len -> go ptr len magnitude
  where
    go :: Ptr Word8 -> Int -> Integer -> IO (Ptr Word8)
    go src len displacement = do
      dst <- mallocBytes len
      case len of
        -- If we only have one byte, we an borrow from the Bits instance for
        -- Word8.
        1 -> do
          srcByte <- peek src
          let srcByte' = srcByte `rotate` fromIntegral displacement
          poke dst srcByte'
        -- If we rotate by a multiple of 8, we only need to move around whole
        -- bytes, rather than individual bits. Because we only move contiguous
        -- blocks (regardless of rotation direction), we can do this using
        -- memcpy, which is must faster, especially on larger ByteStrings.
        _ -> case displacement `quotRem` 8 of
          (bigMove, 0) -> do
            let mainLen :: CSize = fromIntegral . abs $ bigMove
            let restLen :: CSize = fromIntegral len - mainLen
            void $ case signum bigMove of
              1 -> memcpy (plusPtr dst . fromIntegral $ restLen) src mainLen >>
                   memcpy dst (plusPtr src . fromIntegral $ mainLen) restLen
              _ -> memcpy (plusPtr dst . fromIntegral $ mainLen) src restLen >>
                   memcpy dst (plusPtr src . fromIntegral $ restLen) mainLen
          -- If we don't rotate by a multiple of 8, we have to construct new
          -- bytes, rather than just copying over old ones. We do this in two
          -- steps:
          --
          -- 1. Compute the 'read offset' into the source ByteString based on
          -- the rotation magnitude and direction.
          -- 2. Use that read offset to perform an (unchecked) bit lookup for an
          -- entire 8-bit block, then construct the byte that results.
          --
          -- We can do the bytes in the result in any order using this method:
          -- we choose to do it in traversal order.
          _ -> for_ [0 .. len - 1] $ \j -> do
                let start = (len - 1 - j) * 8
                let dstByte = foldl' (addBit start displacement) zeroBits [0 .. 7]
                poke (plusPtr dst j) dstByte
      pure dst
    bitLen :: Integer
    bitLen = fromIntegral $ BS.length bs * 8
    addBit :: Int -> Integer -> Word8 -> Integer -> Word8
    addBit start displacement acc offset =
      let oldIx = (offset + fromIntegral start + bitLen - displacement) `rem` bitLen in
        if dangerousRead bs oldIx
        then acc .|. (bit . fromIntegral $ offset)
        else acc

{-# NOINLINE shiftByteString #-}
shiftByteString :: ByteString -> Integer -> ByteString
shiftByteString bs i
  -- Shifting by the number of bits, or more, would zero everything anyway,
  -- regardless of direction. This also covers the empty ByteString case, as its
  -- bit length is zero.
  | abs i >= bitLen = BS.replicate (BS.length bs) zeroBits
  -- Shifting an all-zero ByteString will not change it, regardless of
  -- direction.
  | isAllZero bs = bs
  | otherwise = overPtrLen bs go
  where
    bitLen :: Integer
    bitLen = fromIntegral $ BS.length bs * 8
    go :: Ptr Word8 -> Int -> IO (Ptr Word8)
    go src len = do
      dst <- mallocBytes len
      case len of
        -- If we only have one byte, we an borrow from the Bits instance for
        -- Word8.
        1 -> do
          srcByte <- peek src
          let srcByte' = srcByte `shift` fromIntegral i
          poke dst srcByte'
        -- If we shift by a multiple of 8, we only need to move a contiguous
        -- block of bytes, then clear what remains. This is much more efficient:
        -- it would be nice if we had memset available, but at least the copy
        -- can be done with memcpy.
        _ -> case i `quotRem` 8 of
          (bigMove, 0) -> do
            let mainLen :: CSize = fromIntegral . abs $ bigMove
            let restLen :: CSize = fromIntegral len - mainLen
            case signum bigMove of
              1 -> do
                void . memcpy dst (plusPtr src . fromIntegral $ mainLen) $ restLen
                for_ [fromIntegral restLen, fromIntegral $ restLen + 1 .. len - 1] $ \j ->
                    poke @Word8 (plusPtr dst j) zeroBits
              _ -> do
                for_ [0 .. fromIntegral mainLen - 1] $ \j -> poke @Word8 (plusPtr dst j) zeroBits
                void . memcpy (plusPtr dst . fromIntegral $ mainLen) src $ restLen
          -- If we shift by something other than a multiple of 8, we have to
          -- construct new bytes, similarly to rotations. We use the same
          -- two-step process to construct new bytes, but due to not having the
          -- 'wraparound' behaviour (unlike rotations), we clear any bits that
          -- would be sourced 'out of bounds'.
          _ -> for_ [0 .. len - 1] $ \j -> do
                let start = (len - 1 - j) * 8
                let dstByte = foldl' (addBit start) zeroBits [0 .. 7]
                poke (plusPtr dst j) dstByte
      pure dst
    addBit :: Int -> Word8 -> Integer -> Word8
    addBit start acc offset =
      let possibleIx = offset + fromIntegral start - i in
        if | possibleIx < 0              -> acc
           | possibleIx >= bitLen        -> acc
           | dangerousRead bs possibleIx -> acc .|. (bit . fromIntegral $ offset)
           | otherwise                   -> acc

findFirstSetByteString :: ByteString -> Integer
findFirstSetByteString bs = foldl' go (-1) [0 .. len - 1]
  where
    go :: Integer -> Int -> Integer
    go acc ix
      | acc /= (-1) = acc -- we found one already
      | otherwise = case BS.index bs (len - ix - 1) of
          0  -> (-1) -- keep looking, nothing to find here
          w8 -> fromIntegral $ (ix * 8) + findPosition w8
    len :: Int
    len = BS.length bs

testBitByteString :: ByteString -> Integer -> Emitter (EvaluationResult Bool)
testBitByteString bs i
  | i < 0 || i >= bitLen = indexOutOfBoundsError "testBitByteString" bitLen i
  | otherwise = pure . pure . dangerousRead bs $ i
  where
    bitLen :: Integer
    bitLen = fromIntegral $ BS.length bs * 8

{-# NOINLINE writeBitByteString #-}
writeBitByteString :: ByteString -> Integer -> Bool -> Emitter (EvaluationResult ByteString)
writeBitByteString bs i b
  | i < 0 || i >= bitLen = indexOutOfBoundsError "writeBitByteString" bitLen i
  -- When we write a bit at a location, we have to return a new copy of the
  -- original with the bit modified. We do this as follows:
  --
  -- 1. Compute the byte that has to change. Because _byte_ indexes and _bit_
  -- indexes go in opposite directions, we have to compute the byte by a
  -- combination of modulus and offset from the end.
  -- 2. Use the remainder to construct a mask which 'selects' the bit within the
  -- byte we want to change.
  -- 3. Memcpy everything over.
  -- 4. Use the mask at the computed byte index to modify the result in-place:
  -- we do a different operation depending on whether we're setting or clearing.
  --
  -- We use memcpy plus a single write as this is _much_ faster than going
  -- byte-by-byte and checking if we've reached the index we want each time:
  -- memcpy is highly-optimized using SIMD instructions on every platform, and a
  -- branchy per-byte loop is absolutely horrid everywhere for speed due to the
  -- branch count.
  | otherwise = do
      let (bigOffset, smallOffset) = i `quotRem` 8
      let bigIx = fromIntegral $ byteLen - bigOffset - 1
      let mask = bit 0 `shiftL` fromIntegral smallOffset
      pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ go bigIx mask
  where
    byteLen :: Integer
    byteLen = fromIntegral . BS.length $ bs
    bitLen :: Integer
    bitLen = byteLen * 8
    go :: Int -> Word8 -> (Ptr CChar, Int) -> IO ByteString
    go bigIx mask (src, len) = do
      dst <- mallocBytes len
      void . memcpy dst src . fromIntegral $ len
      byte :: Word8 <- peek . plusPtr src $ bigIx
      let byte' = if b then mask .|. byte else complement mask .&. byte
      poke (castPtr . plusPtr dst $ bigIx) byte'
      unsafePackMallocCStringLen (dst, len)

integerToByteString :: Integer -> ByteString
integerToByteString i = case signum i of
  0    -> BS.singleton zeroBits
  (-1) -> twosCompToNegative . fromList . go . abs $ i
  _    -> fromList . go $ i
  where
    -- We encode into Word8-sized 'limbs', using a stack to ensure that their
    -- ordering is little-endian. Effectively, we encode as a base-256 number,
    -- where the least significant digit is at the end.
    go :: Integer -> [Word8]
    go = \case
      0 -> []
      pos -> case pos `quotRem` 256 of
        (d, r) -> go d <> [fromIntegral r]

byteStringToInteger :: ByteString -> Integer
byteStringToInteger bs = case BS.uncons bs of
  Nothing -> 0
  -- We have to take some care with representations of exact powers of 256, as
  -- the two's complement in such a case is the identity function. Therefore, if
  -- we find an 'unpadded' power, we have to presume that it's positive; if we
  -- find a leading 0x80, but _something_ else is not a zero byte, we assume
  -- it's negative instead.
  Just (w8, bs') ->
    let len = BS.length bs
        f x = evalState (foldM (go x) 0 [len - 1, len - 2 .. 0]) 1 in
      if | isPositivePowerOf256 w8 bs' -> f bs
         | bit 7 .&. w8 == zeroBits    -> f bs
         | otherwise                   -> negate . f . twosCompToPositive $ bs
  where
    -- This is essentially the opposite to encoding. However, because
    -- ByteStrings can be indexed from the end in constant time, we don't need
    -- to use something like a stack: instead, we start from the end, and
    -- accumulate the radix base as we go, increasing the further along we get.
    -- This is more efficient, as we'd otherwise first have to compute the
    -- largest power of 256 we need, then divide down, essentially doing the
    -- work _twice_.
    go :: ByteString -> Integer -> Int -> State Integer Integer
    go bs' acc i = do
      mult <- get
      let byte = BS.index bs' i
      modify (256 *)
      pure $ acc + (fromIntegral byte * mult)

{-# NOINLINE popCountByteString #-}
popCountByteString :: ByteString -> Integer
popCountByteString bs = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ go
  where
    -- We use a standard 'big step, small step' approach. The reason for this is
    -- that bit counting (via a FiniteBits instance) is defined for much larger
    -- types than Word8. We can thus read 8-blocks of bytes as 64-bit words
    -- instead (as we don't care about sign and GHC ensures word alignment),
    -- which gives us potentially up to an 8x speedup.
    --
    -- Thus, our 'big step, small step' approach first walks as much of its
    -- input as it can using steps whose size is Word64, then finishes the job
    -- with steps whose size is Word8. We use a rank-2 polymorphic method to
    -- avoid code duplication, since the only operation we need comes from a
    -- type class, and is thus agnostic to what we're working over. Step size
    -- can also be determined via Storable in a similar way.
    go :: (Ptr CChar, Int) -> IO Integer
    go (ptr, len) = do
      let (bigSteps, smallSteps) = len `quotRem` 8
      let bigPtr :: Ptr Word64 = castPtr ptr
      let smallPtr :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
      bigCount <- countBits bigPtr bigSteps
      smallCount <- countBits smallPtr smallSteps
      pure . fromIntegral $ bigCount + smallCount

-- We use a standard 'big step, small step' construction for all the operators
-- below. The reason for this is that each of these operations are bit-parallel:
-- it doesn't matter what width of bit block you operate on, you'll have the
-- same outcome. As a result, these operations are defined for much larger
-- blocks than Word8. We can thus read 8-blocks of bytes as 64-bit words instead
-- (as we don't care about sign and GHC ensures word alignment), which gives us
-- potentially up to an 8x speedup.
--
-- Thus, our 'big step, small step' approach processes the inputs in two stages:
--
-- 1. Walk lockstep in blocks of Word64 size over both inputs, and set the
-- corresponding place in the output to the result of the bitwise operation on
-- those blocks.
-- 2. For whatever remains, walk lockstep in blocks of Word8 size over both
-- inputs, and set the corresponding place in the output to the result of the
-- bitwise operation on those blocks.
--
-- We use a rank-2 polymorphic method to avoid code duplication, since all of
-- the operations over blocks we are interested in (of either size) come from a
-- type class (Bits) without caring about what specific type we're dealing with.
-- Step size can also be determined via Storable in a similar way.
--
-- We use a mutable construction inside IO instead of something immutable to
-- avoid excessive 'sloshing': on our current version of the 'bytestring'
-- library, there is no way to 'zip together' two ByteStrings directly: your
-- only option was to 'zip out' into a list, then rebuild. This is not only
-- inefficient (as you can't do a 'big step, little step' approach to this in
-- general), it also copies too much.
{-# NOINLINE andByteString #-}
andByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
andByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "andByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild (.&.) ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

{-# NOINLINE iorByteString #-}
iorByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
iorByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "iorByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild (.|.) ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

{-# NOINLINE xorByteString #-}
xorByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
xorByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "xorByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild xor ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

-- Similarly to the above, we use a 'big step, little step' here as well. The
-- only difference is that there is only one input to read from, rather than
-- two. Similar reasoning applies to why we made this choice as to the
-- previous operations.

{-# NOINLINE complementByteString #-}
complementByteString :: ByteString -> ByteString
complementByteString bs = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) -> do
  resPtr <- mallocBytes len
  let (bigSteps, smallSteps) = len `quotRem` 8
  let bigDst :: Ptr Word64 = castPtr resPtr
  let smallDst :: Ptr Word8 = castPtr . plusPtr resPtr $ bigSteps * 8
  let bigSrc :: Ptr Word64 = castPtr ptr
  let smallSrc :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
  go bigDst bigSrc 0 bigSteps
  go smallDst smallSrc 0 smallSteps
  unsafePackMallocCStringLen (resPtr, len)
  where
    go :: forall (a :: Type) .
      (Storable a, FiniteBits a) =>
      Ptr a -> Ptr a -> Int -> Int -> IO ()
    go dst src offset lim
      | offset == lim = pure ()
      | otherwise = do
          let offset' = offset * sizeOf (undefined :: a)
          block :: a <- peek . plusPtr src $ offset'
          poke (plusPtr dst offset') . complement $ block
          go dst src (offset + 1) lim

-- Helpers

isPositivePowerOf256 :: Word8 -> ByteString -> Bool
isPositivePowerOf256 w8 bs = w8 == 0x80 && BS.all (== zeroBits) bs

-- We compute the read similarly to how we determine the change when we write.
-- The only difference is that the mask is used on the input to read it, rather
-- than to modify anything.
dangerousRead :: ByteString -> Integer -> Bool
dangerousRead bs i =
  let (bigOffset, smallOffset) = i `quotRem` 8
      bigIx = BS.length bs - fromIntegral bigOffset - 1
      mask = bit (fromIntegral smallOffset) in
    case mask .&. BS.index bs bigIx of
      0 -> False
      _ -> True

-- Important note: this function is only safe under the following conditions:
--
-- * The IO used in the function argument only performs memory allocations using
-- malloc, as well as reads and writes via the Storable interface;
-- * The pointer argument is only read from, not written to;
-- * The result of the function argument points to freshly-allocated, malloced
-- memory; and
-- * The result of the function argument points to memory whose length matches
-- that of the input ByteString (in bytes)
--
-- Even though a ByteString is represented as Ptr CChar, we can ignore sign (we
-- only treat them as binary data anyway), and on POSIX platforms (which GHC
-- silently assumes, even on Windows), CChar _must_ be exactly a byte. Thus, we
-- allow working over a pointer to Word8 instead, to avoid issues with signs.
overPtrLen :: ByteString -> (Ptr Word8 -> Int -> IO (Ptr Word8)) -> ByteString
overPtrLen bs f = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $
  \(ptr, len) -> f (castPtr ptr) len >>= \p ->
    unsafePackMallocCStringLen (castPtr p, len)

-- Two's complement in a signed, unbounded representation is somewhat
-- problematic: in our particular case, we hit this issue on exact powers of
-- 256. This issue stems from such values (or rather, the ByteString
-- representations of such) having a two's complement identical to themselves,
-- as well as a trailing 1. This means that we can't distinguish between a
-- _negative_ and a _positive_ power from representation alone, and must default
-- one way or the other.
--
-- Thus, when we want to produce a negative representation, we have to ensure
-- that we 'mark' the result in a way that ensures we can detect that it was
-- negative. We do this by padding with trailing ones.
twosCompToNegative :: ByteString -> ByteString
twosCompToNegative bs = case twosComp bs of
  bs' -> if bs == bs'
         then BS.cons (complement zeroBits) bs'
         else bs'

-- If we're taking a two's complement to produce a positive representation,
-- padding doesn't matter, as any trailing ones become trailing zeroes.
twosCompToPositive :: ByteString -> ByteString
twosCompToPositive = twosComp

-- This is a fused version of the 'standard' definition of two's complement:
-- 'flip all bits then add one'. We do this in one pass to avoid having to
-- produce two ByteStrings, only to throw one away. This is done by tracking
-- the add carry manually, and walking over the representation from the highest
-- byte index downward: if the carry is still present, we attempt an 'add one'
-- there and then. This can cause the carry to become 'absorbed', in which case
-- we no longer need to track it; otherwise, we continue on, tracking the carry.
--
-- This operation has to be done byte-wise, as bigger blocks would make carry
-- tracking too difficult, which would probably dwarf any performance
-- improvements. Furthermore, it's not even clear if a 'big step, small step'
-- approach would even help here, as we're reading backwards (against prefetch
-- order), and likely from unaligned memory to boot (as GHC only guarantees
-- alignment from the _start_, not the _end_).
twosComp :: ByteString -> ByteString
twosComp bs = let len = BS.length bs in
  evalState (fromListN len <$> foldM go [] [len - 1, len - 2 .. 0]) False
  where
    go :: [Word8] -> Int -> State Bool [Word8]
    go acc i = do
      let byte = BS.index bs i
      added <- get
      let byte' = if added then complement byte else complement byte + 1
      when (byte /= byte') (put True)
      pure $ byte' : acc

mismatchedLengthError :: forall (a :: Type) .
  Text ->
  ByteString ->
  ByteString ->
  Emitter (EvaluationResult a)
mismatchedLengthError loc bs bs' = do
  emit $ loc <> " failed"
  emit "Reason: mismatched argument lengths"
  emit $ "Length of first argument: " <> (pack . show . BS.length $ bs)
  emit $ "Length of second argument: " <> (pack . show . BS.length $ bs')
  pure EvaluationFailure

indexOutOfBoundsError :: forall (a :: Type) .
  Text ->
  Integer ->
  Integer ->
  Emitter (EvaluationResult a)
indexOutOfBoundsError loc lim i = do
  emit $ loc <> " failed"
  emit "Reason: out of bounds"
  emit $ "Attempted access at index " <> (pack . show $ i)
  emit $ "Valid indexes: from 0 to " <> (pack . show $ lim - 1)
  pure EvaluationFailure

-- A general method for 'zipping together' two ByteString inputs to produce a
-- new ByteString output, assuming the 'zipping function' is bit-parallel. This
-- uses a standard 'big step, little step' construction. We can do this because
-- bit-parallel operations don't change semantics based on the size of the block
-- read; furthermore, as GHC guarantees word alignment and we don't care about
-- sign, we can potentially get up to an 8x speedup.
--
-- We use a mutable construction inside IO instead of something immutable to
-- avoid excessive 'sloshing': on our current version of the 'bytestring'
-- library, there is no way to 'zip together' two ByteStrings directly: your
-- only option was to 'zip out' into a list, then rebuild. This is not only
-- inefficient (as you can't do a 'big step, little step' approach to this in
-- general), it also copies too much.
--
-- Note: the function argument must be bit-parallel. The type guarantees it to
-- some degree, but in general, we can't enforce this in the type system.
zipBuild ::
  (forall (a :: Type) . (FiniteBits a, Storable a) => a -> a -> a) ->
  Ptr CChar ->
  Ptr CChar ->
  Int ->
  IO (Ptr CChar)
zipBuild f ptr ptr' len = do
  resPtr <- mallocBytes len
  let (bigSteps, smallSteps) = len `quotRem` 8
  let bigPtr :: Ptr Word64 = castPtr resPtr
  let smallPtr :: Ptr Word8 = castPtr . plusPtr resPtr $ bigSteps * 8
  go bigPtr (castPtr ptr) (castPtr ptr') 0 bigSteps
  let ptrRest :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
  let ptrRest' :: Ptr Word8 = castPtr . plusPtr ptr' $ bigSteps * 8
  go smallPtr ptrRest ptrRest' 0 smallSteps
  pure resPtr
  where
    go :: forall (b :: Type) .
      (FiniteBits b, Storable b) =>
      Ptr b ->
      Ptr b ->
      Ptr b ->
      Int ->
      Int ->
      IO ()
    go dst src src' offset lim
      | offset == lim = pure ()
      | otherwise = do
          let offset' = sizeOf (undefined :: b) * offset
          block :: b <- peek . plusPtr src $ offset'
          block' :: b <- peek . plusPtr src' $ offset'
          poke (plusPtr dst offset') (f block block')
          go dst src src' (offset + 1) lim

-- Check every bit position in a byte for a set bit, returning its index if we
-- find one. We default return 7, even though this index is valid, as no
-- consumer function ever looks at this value, since that can only happen on
-- zero bytes, which we ignore anyway.
findPosition :: Word8 -> Int
findPosition w8 = foldl' go 7 . fmap (\i -> (i, bit 0 `shiftL` i)) $ [0 .. 7]
  where
    go :: Int -> (Int, Word8) -> Int
    go acc (i, mask) = case mask .&. w8 of
      0 -> acc -- nothing to see here, move along
      _ -> min acc i

-- A polymorphic bit counter in a block, which we can segment by chunks of a
-- type of arbitrary size, provided it is both Storable (so we can read at
-- offsets) and FiniteBits (so we can count it).
countBits :: forall (a :: Type) .
  (FiniteBits a, Storable a) =>
  Ptr a -> Int -> IO Int
countBits ptr len = go 0 0
  where
    go :: Int -> Int -> IO Int
    go total offset
      | offset == len = pure total
      | otherwise = do
          let offset' = offset * sizeOf (undefined :: a)
          block :: a <- peek . plusPtr ptr $ offset'
          let total' = total + popCount block
          go total' (offset + 1)

-- Check if every byte of a ByteString is zero
isAllZero :: ByteString -> Bool
isAllZero = BS.all (== zeroBits)

-- Check if every byte of a ByteString is one
isAllOne :: ByteString -> Bool
isAllOne = BS.all (== complement zeroBits)
