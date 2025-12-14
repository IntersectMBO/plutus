-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}

{-| Implementations for CIP-121, CIP-122 and CIP-123. Grouped because they all operate on
'ByteString's, and require similar functionality. -}
module PlutusCore.Bitwise
  ( integerToByteString
  , byteStringToInteger
  , andByteString
  , orByteString
  , xorByteString
  , complementByteString
  , shiftByteString
  , rotateByteString
  , readBit
  , writeBits
  , replicateByte
  , countSetBits
  , findFirstSetBit
  , IntegerToByteStringError (..)
  , maximumOutputLength
  ) where

import PlutusCore.Builtin (BuiltinResult, builtinResultFailure, emit)

import Control.Exception (Exception, throwIO, try)
import Control.Monad (unless, when)
import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal qualified as BSI
import Data.ByteString.Unsafe qualified as BSU
import Data.Foldable (for_)
import Data.Primitive.ByteArray (ByteArray (ByteArray), copyByteArrayToAddr)
import Data.Text (pack)
import Data.Word (Word16, Word64, byteSwap16, byteSwap64)
import Foreign.Marshal.Utils (copyBytes, fillBytes)
import Foreign.Ptr (castPtr, plusPtr)
import Foreign.Storable (peek, peekByteOff, peekElemOff, poke, pokeByteOff, pokeElemOff)
import GHC.ByteOrder (ByteOrder (BigEndian, LittleEndian))
import GHC.Exts
  ( ByteArray#
  , Int (I#)
  , Int#
  , Ptr (Ptr)
  , clz#
  , indexWord8Array#
  , int2Word#
  , int8ToWord8#
  , intToInt8#
  , isTrue#
  , neWord8#
  , quotInt#
  , quotRemInt#
  , sizeofByteArray#
  , word2Int#
  , wordToWord8#
  , (-#)
  , (<#)
  , (==#)
  )
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import GHC.Num.Integer (Integer (IN, IP, IS), integerFromAddr, integerLog2)
import GHC.Word (Word8 (W8#))

{- Note [Input length limitation for IntegerToByteString].
We make `integerToByteString` and `replicateByte` fail if they're called with arguments which would
cause the length of the result to exceed about 8K bytes because the execution time becomes difficult
to predict accurately beyond this point (benchmarks on a number of different machines show that the
CPU time increases smoothly for inputs up to about 8K then increases sharply, becoming chaotic after
about 14K).  This restriction may be removed once a more efficient implementation becomes available.-}
{- NB: if we do relax the length restriction then we will need two variants of integerToByteString in
   Plutus Core so that we can continue to support the current behaviour for old scripts.-}
maximumOutputLength :: Integer
maximumOutputLength = 8192

-- | Wrapper for 'unsafeIntegerToByteString' to make it more convenient to define as a builtin.
integerToByteString :: Bool -> Integer -> Integer -> BuiltinResult ByteString
integerToByteString endiannessArg lengthArg input
  -- Check that the length is non-negative.
  | lengthArg < 0 = do
      emit "integerToByteString: negative length argument"
      emit $ "Length requested: " <> (pack . show $ input)
      builtinResultFailure
  -- Check that the requested length does not exceed the limit.  *NB*: if we remove the limit we'll
  -- still have to make sure that the length fits into an Int.
  | lengthArg > maximumOutputLength = do
      emit . pack $
        "integerToByteString: requested length is too long (maximum is "
          ++ show maximumOutputLength
          ++ " bytes)"
      emit $ "Length requested: " <> (pack . show $ lengthArg)
      builtinResultFailure
  -- If the requested length is zero (ie, an explicit output size is not
  -- specified) we still have to make sure that the output won't exceed the size
  -- limit.  If the requested length is nonzero and less than the limit,
  -- integerToByteString checks that the input fits.
  | lengthArg == 0 -- integerLog2 n is one less than the number of significant bits in n
      && fromIntegral (integerLog2 input) >= 8 * maximumOutputLength =
      let bytesRequiredFor n = integerLog2 n `div` 8 + 1
       in -- \^ This gives 1 instead of 0 for n=0, but we'll never get that.
          do
            emit . pack $
              "integerToByteString: input too long (maximum is 2^"
                ++ show (8 * maximumOutputLength)
                ++ "-1)"
            emit $ "Length required: " <> (pack . show $ bytesRequiredFor input)
            builtinResultFailure
  | otherwise =
      let endianness = endiannessArgToByteOrder endiannessArg
       in -- We use fromIntegral here, despite advice to the contrary in general when defining builtin
          -- denotations. This is because, if we've made it this far, we know that overflow or truncation
          -- are impossible: we've checked that whatever we got given fits inside a (non-negative) Int.
          case unsafeIntegerToByteString endianness (fromIntegral lengthArg) input of
            Left err -> case err of
              NegativeInput -> do
                emit "integerToByteString: cannot convert negative Integer"
                -- This does work proportional to the size of input. However, we're in a failing case
                -- anyway, and the user's paid for work proportional to this size in any case.
                emit $ "Input: " <> (pack . show $ input)
                builtinResultFailure
              NotEnoughDigits -> do
                emit "integerToByteString: cannot represent Integer in given number of bytes"
                -- This does work proportional to the size of input. However, we're in a failing case
                -- anyway, and the user's paid for work proportional to this size in any case.
                emit $ "Input: " <> (pack . show $ input)
                emit $ "Bytes requested: " <> (pack . show $ lengthArg)
                builtinResultFailure
            Right result -> pure result

{-| Conversion from 'Integer' to 'ByteString', as per
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121). -}
-- | Structured type to help indicate conversion errors.
data IntegerToByteStringError
  = NegativeInput
  | NotEnoughDigits
  deriving stock (Eq, Show)

endiannessArgToByteOrder :: Bool -> ByteOrder
endiannessArgToByteOrder b = if b then BigEndian else LittleEndian

-- For performance and clarity, the endianness argument uses
-- 'ByteOrder', and the length argument is an 'Int'.
-- This may not actually be unsafe, but it shouldn't be used outside this module.
unsafeIntegerToByteString :: ByteOrder -> Int -> Integer -> Either IntegerToByteStringError ByteString
unsafeIntegerToByteString requestedByteOrder requestedLength input = case input of
  IS i# ->
    if
      | isTrue# (i# ==# 0#) -> Right . BS.replicate requestedLength $ 0x00
      | isTrue# (i# <# 0#) -> Left NegativeInput
      | otherwise ->
          -- This is a somewhat long-winded way to do a base-256
          -- logarithm of `i#`. This works because the number of bytes
          -- we need to represent any given (positive) `Int#` will
          -- directly depend on the number of leading zeroes: every full
          -- 8 leading zeroes means a byte we _don't_ need to use. We
          -- can then figure out the number of unused bytes (all-zero)
          -- byt taking the quotient of the leading zero count by 8.
          let counted# = clz# (int2Word# i#)
              minLength = 8 - I# (quotInt# (word2Int# counted#) 8#)
           in if
                | requestedLength == 0 -> Right (mkSmall minLength i#)
                | requestedLength < minLength -> Left NotEnoughDigits
                | otherwise -> Right (mkSmall requestedLength i#)
  IP ba# ->
    -- Because logarithms in base 256 are not (yet) optimized (see
    -- https://hackage-content.haskell.org/package/ghc-bignum-1.3/docs/src/GHC.Num.BigNat.html#bigNatLogBaseWord%23)
    -- and we must have nonzero 64 bit limbs in all positions
    -- (https://hackage-content.haskell.org/package/ghc-bignum-1.3/docs/GHC-Num-BigNat.html#t:BigNat-35-),
    -- it's cheaper for us to count zero bytes at the end, as this loop will
    -- take a maximum of 7 steps ever on every platform we care about,
    -- whereas a logarithm will be Theta(n) on the length of `ba#`.
    let len# = sizeofByteArray# ba#
        zeroesAtEnd = countZeroesAtEnd ba# 0 (len# -# 1#)
        minLength = I# len# - zeroesAtEnd
     in if
          | requestedLength == 0 -> Right (mkLarge minLength minLength ba#)
          | requestedLength < minLength -> Left NotEnoughDigits
          | otherwise -> Right (mkLarge minLength requestedLength ba#)
  IN _ -> Left NegativeInput
  where
    mkSmall :: Int -> Int# -> ByteString
    mkSmall desiredLength i# = BSI.unsafeCreate desiredLength $ \ptr -> do
      fillBytes ptr 0x00 desiredLength
      case requestedByteOrder of
        -- We use manual specialization to ensure as few branches in loop bodies
        -- as we can. See Note [Manual specialization] for details.
        LittleEndian -> goSmallLE ptr 0 i#
        BigEndian -> goSmallBE ptr (desiredLength - 1) i#
    countZeroesAtEnd :: ByteArray# -> Int -> Int# -> Int
    countZeroesAtEnd ba# acc ix# =
      let w8# = indexWord8Array# ba# ix#
       in if isTrue# (neWord8# w8# (wordToWord8# 0##))
            then acc
            else countZeroesAtEnd ba# (acc + 1) (ix# -# 1#)
    mkLarge :: Int -> Int -> ByteArray# -> ByteString
    mkLarge minLength desiredLength ba# = BSI.unsafeCreate desiredLength $ \ptr -> do
      fillBytes ptr 0x00 desiredLength
      -- Because `copyByteArrayToAddr` is essentially `memcpy` or `copyBytes`,
      -- it may as well be a constant-time operation for anything that isn't
      -- at least multiple memory pages in size. Given that memory pages are on
      -- the order of 8KiB on every platform we care about, we're better off
      -- blindly copying over the `Integer` data, then reversing the result in
      -- place if we need it 'big endian'. This is because no backward copying
      -- routine we could write can compete with `memcpy` at no FFI penalty, and
      -- reversing in-place requires only half the iterations that a copy would
      -- in any case.
      copyByteArrayToAddr ptr (ByteArray ba#) 0 minLength
      case requestedByteOrder of
        LittleEndian -> pure ()
        BigEndian -> reverseBuffer ptr desiredLength
    goSmallLE :: Ptr Word8 -> Int -> Int# -> IO ()
    goSmallLE ptr offset remaining#
      | isTrue# (remaining# ==# 0#) = pure ()
      | otherwise = do
          let !(# q#, r# #) = quotRemInt# remaining# 256#
          pokeByteOff ptr offset (W8# (int8ToWord8# (intToInt8# r#)))
          goSmallLE ptr (offset + 1) q#
    goSmallBE :: Ptr Word8 -> Int -> Int# -> IO ()
    goSmallBE ptr offset remaining#
      | isTrue# (remaining# ==# 0#) = pure ()
      | otherwise = do
          let !(# q#, r# #) = quotRemInt# remaining# 256#
          pokeByteOff ptr offset (W8# (int8ToWord8# (intToInt8# r#)))
          goSmallBE ptr (offset - 1) q#
    -- We use loop sectioning here so that we can reverse more quickly.
    -- Specifically, we do two kinds of 'steps':
    --
    -- 1. 'Large' steps, where we reverse 16 bytes at once (8 from each end);
    --     followed by
    -- 2. 'Small' steps, where we reverse 4 bytes at once (2 from each end).
    --
    -- See Note [Loop sectioning] for details on why we do this.
    reverseBuffer :: Ptr Word8 -> Int -> IO ()
    reverseBuffer ptr remainingSpan
      | remainingSpan < 16 = finishUp ptr remainingSpan
      -- We use a standard 'two-finger' technique for reversing a buffer. We
      -- maintain a pair of pointers (or in our case, a pointer and an offset
      -- for easier control), representing the start and end of the
      -- un-reversed region. We then read the 'start pointer' forward a block,
      -- and the 'end pointer' backward a block. Lastly, we swap the byte
      -- order in both blocks, the write the 'start block' to the end and the
      -- 'end block' to the start. We then adjust our pointers forward (or
      -- back) one block.
      | otherwise = do
          let pStart :: Ptr Word64 = castPtr ptr
          let pEnd :: Ptr Word64 = castPtr (plusPtr ptr (remainingSpan - 8))
          wStart <- peek pStart
          wEnd <- peek pEnd
          poke pEnd (byteSwap64 wStart)
          poke pStart (byteSwap64 wEnd)
          reverseBuffer (plusPtr ptr 8) (remainingSpan - 16)
    finishUp :: Ptr Word8 -> Int -> IO ()
    finishUp ptr remaining
      -- If we have exactly zero or exactly one byte left, we've reached the
      -- middle: either our 'fingers' met, or there's one element between them.
      -- In either case, no further action is needed.
      | remaining <= 1 = pure ()
      -- If we have exactly two elements left, we can swap them and stop.
      | remaining == 2 = do
          wLeft <- peek ptr
          wRight <- peek (plusPtr ptr 1)
          poke ptr wRight
          poke (plusPtr ptr 1) wLeft
      -- The special case where we have 3 bytes left to swap bears closer
      -- examination, and is the reason why our 'small steps' can be as large as
      -- they are. Consider the case below, where `...` marks equal-size
      -- 'already reversed' regions:
      --
      -- [..., x, y, z, ...]
      --
      -- Our 'fingers' would read as follows:
      --
      -- 1. The 'left finger' would read `x, y`; and
      -- 2. Our 'right finger' would read `y, z`.
      --
      -- After byteswapping, we have a new 'right side' of `y, x`, and a new
      -- 'left side' of `z, y`. Since the `y` in both sides overlaps, we can
      -- safely have this write overlap, as this will not affect the result.
      | otherwise = do
          let pStart :: Ptr Word16 = castPtr ptr
          let pEnd :: Ptr Word16 = castPtr (plusPtr ptr (remaining - 2))
          wStart <- peek pStart
          wEnd <- peek pEnd
          poke pEnd (byteSwap16 wStart)
          poke pStart (byteSwap16 wEnd)
          finishUp (plusPtr ptr 2) (remaining - 4)

{-| Conversion from 'ByteString' to 'Integer', as per
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121). -}
-- | Wrapper for 'unsafeByteStringToInteger' to make it more convenient to define as a builtin.
byteStringToInteger
  :: Bool -> ByteString -> Integer
byteStringToInteger statedEndiannessArg input =
  let endianness = endiannessArgToByteOrder statedEndiannessArg
   in unsafeByteStringToInteger endianness input

-- For clarity, the stated endianness argument uses 'ByteOrder'.
-- This function may not actually be unsafe, but it shouldn't be used outside this module.
unsafeByteStringToInteger :: ByteOrder -> ByteString -> Integer
unsafeByteStringToInteger statedByteOrder input
  | BS.null input = 0
  | otherwise =
      let bo# = case statedByteOrder of
            LittleEndian -> 0#
            BigEndian -> 1#
       in unsafeDupablePerformIO . BSU.unsafeUseAsCStringLen input $ \(Ptr addr#, I# len#) ->
            integerFromAddr (int2Word# len#) addr# bo#

{- Note [Binary bitwise operation implementation and manual specialization]

   All of the 'binary' bitwise operations (namely `andByteString`,
   `orByteString` and `xorByteString`) operate similarly:

   1. Decide which of their two `ByteString` arguments determines the length
      of the result. For padding semantics, this is the _longer_ argument,
      whereas for truncation semantics, it's the _shorter_ one. If both
      `ByteString` arguments have identical length, it doesn't matter which we
      choose.
   2. Copy the choice made in step 1 into a fresh mutable buffer.
   3. Traverse over each byte of the argument _not_ chosen in step 1, and
      combine each of those bytes with the byte at the corresponding index of
      the fresh mutable buffer from step 2 (`.&.` for `andByteString`,
      `.|.` for `orByteString`, `xor` for `xorByteString`).

  We also make use of loop sectioning to optimize this operation: see Note
  [Loop sectioning] explaining why we do this. Fundamentally, this doesn't
  change the logic of the operation, but means that step 3 is split into
  two smaller sub-steps: we first word 8 bytes at a time, then one byte at a
  time to finish up if necessary. Other than the choice of 'combining
  operation', the structure of the computation is the same, which suggests that
  we want a helper function with a signature like

  helper1 ::
    (Word64 -> Word64 -> Word64) ->
    (Word8 -> Word8 -> Word8) ->
    ByteString ->
    ByteString ->
    Int ->
    ByteString

  or possibly (to avoid duplicate argument passing) like

  helper2 ::
    (forall (a :: Type) . Bits a => a -> a -> a) ->
    ByteString ->
    ByteString ->
    Int ->
    ByteString

  This would allow us to share all this logic, and have each of the 'top-level'
  operations just dispatch to either of the helpers with the appropriate
  function argument(s). Instead, we chose to write a manual copy of this logic
  for each of the 'top-level' operations, substituting only the 'combining
  operation'.

  We made this choice as any design based on either `helper1` or `helper2` is
  significantly slower (at least 50% worse, and the penalty _percentage_ grows
  with argument size). While `helper2` is significantly more penalizing than
  `helper1`, even `helper1` reaches an almost threefold slowdown at the higher
  input sizes we are interested in relative the manual version we use here.
  Due to the 'low-level' nature of Plutus Core primops, we consider these costs
  unacceptable relative the (small) benefits to code clarity and maintainability
  any solution using either style of helper would provide.

  The reason for `helper2` under-performing is unsurprising: any argument whose
  type is rank-2 polymorphic with a dictionary constraint essentially acts as
  a 'program template', which gets interpreted at runtime given some dictionary
  for a `Bits` instance. GHC can do practically nothing to optimize this, as
  there is no way to tell, for any given argument, _which_ definitions of an
  instance would be required here, even if the set of operations we use is
  finite, since any instance can make use of the full power of Haskell, which
  essentially lands us in Rice's Theorem territory. For `helper1`, the reasons
  are similar: it _must_ be able to work regardless of what functions (assuming
  appropriate types) it is given, which means in general, GHC is forced to
  compile mother-may-I-style code involving pointer chasing those arguments at
  runtime. This explains why the 'blowup' becomes worse with argument length.

  While in theory inlining could help with at least the `helper1` case (
  `helper2` is beyond that technique), it doesn't seem like GHC is able to
  figure this out, even with `INLINE` is placed on `helper1`.
  -}

-- | Bitwise logical AND, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122).
andByteString :: Bool -> ByteString -> ByteString -> ByteString
andByteString shouldPad bs1 bs2 =
  let (shorter, longer) = if BS.length bs1 < BS.length bs2 then (bs1, bs2) else (bs2, bs1)
      (toCopy, toTraverse) = if shouldPad then (longer, shorter) else (shorter, longer)
   in go toCopy toTraverse (BS.length shorter)
  where
    go :: ByteString -> ByteString -> Int -> ByteString
    go toCopy toTraverse traverseLen =
      unsafeDupablePerformIO . BS.useAsCStringLen toCopy $ \(copyPtr, copyLen) ->
        BS.useAsCString toTraverse $ \traversePtr -> do
          BSI.create copyLen $ \dstPtr -> do
            copyBytes dstPtr (castPtr copyPtr) copyLen
            let (bigStrides, littleStrides) = traverseLen `quotRem` 8
            let offset = bigStrides * 8
            let bigDstPtr :: Ptr Word64 = castPtr dstPtr
            let bigTraversePtr :: Ptr Word64 = castPtr traversePtr
            for_ [0 .. bigStrides - 1] $ \i -> do
              w64_1 <- peekElemOff bigDstPtr i
              w64_2 <- peekElemOff bigTraversePtr i
              pokeElemOff bigDstPtr i $ w64_1 Bits..&. w64_2
            let smallDstPtr :: Ptr Word8 = plusPtr dstPtr offset
            let smallTraversePtr :: Ptr Word8 = plusPtr traversePtr offset
            for_ [0 .. littleStrides - 1] $ \i -> do
              w8_1 <- peekElemOff smallDstPtr i
              w8_2 <- peekElemOff smallTraversePtr i
              pokeElemOff smallDstPtr i $ w8_1 Bits..&. w8_2
{-# INLINEABLE andByteString #-}

-- | Bitwise logical OR, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122).
orByteString :: Bool -> ByteString -> ByteString -> ByteString
orByteString shouldPad bs1 bs2 =
  let (shorter, longer) = if BS.length bs1 < BS.length bs2 then (bs1, bs2) else (bs2, bs1)
      (toCopy, toTraverse) = if shouldPad then (longer, shorter) else (shorter, longer)
   in go toCopy toTraverse (BS.length shorter)
  where
    go :: ByteString -> ByteString -> Int -> ByteString
    go toCopy toTraverse traverseLen =
      unsafeDupablePerformIO . BS.useAsCStringLen toCopy $ \(copyPtr, copyLen) ->
        BS.useAsCString toTraverse $ \traversePtr -> do
          BSI.create copyLen $ \dstPtr -> do
            copyBytes dstPtr (castPtr copyPtr) copyLen
            let (bigStrides, littleStrides) = traverseLen `quotRem` 8
            let offset = bigStrides * 8
            let bigDstPtr :: Ptr Word64 = castPtr dstPtr
            let bigTraversePtr :: Ptr Word64 = castPtr traversePtr
            for_ [0 .. bigStrides - 1] $ \i -> do
              w64_1 <- peekElemOff bigDstPtr i
              w64_2 <- peekElemOff bigTraversePtr i
              pokeElemOff bigDstPtr i $ w64_1 Bits..|. w64_2
            let smallDstPtr :: Ptr Word8 = plusPtr dstPtr offset
            let smallTraversePtr :: Ptr Word8 = plusPtr traversePtr offset
            for_ [0 .. littleStrides - 1] $ \i -> do
              w8_1 <- peekElemOff smallDstPtr i
              w8_2 <- peekElemOff smallTraversePtr i
              pokeElemOff smallDstPtr i $ w8_1 Bits..|. w8_2
{-# INLINEABLE orByteString #-}

-- | Bitwise logical XOR, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122).
xorByteString :: Bool -> ByteString -> ByteString -> ByteString
xorByteString shouldPad bs1 bs2 =
  let (shorter, longer) = if BS.length bs1 < BS.length bs2 then (bs1, bs2) else (bs2, bs1)
      (toCopy, toTraverse) = if shouldPad then (longer, shorter) else (shorter, longer)
   in go toCopy toTraverse (BS.length shorter)
  where
    go :: ByteString -> ByteString -> Int -> ByteString
    go toCopy toTraverse traverseLen =
      unsafeDupablePerformIO . BS.useAsCStringLen toCopy $ \(copyPtr, copyLen) ->
        BS.useAsCString toTraverse $ \traversePtr -> do
          BSI.create copyLen $ \dstPtr -> do
            copyBytes dstPtr (castPtr copyPtr) copyLen
            let (bigStrides, littleStrides) = traverseLen `quotRem` 8
            let offset = bigStrides * 8
            let bigDstPtr :: Ptr Word64 = castPtr dstPtr
            let bigTraversePtr :: Ptr Word64 = castPtr traversePtr
            for_ [0 .. bigStrides - 1] $ \i -> do
              w64_1 <- peekElemOff bigDstPtr i
              w64_2 <- peekElemOff bigTraversePtr i
              pokeElemOff bigDstPtr i $ Bits.xor w64_1 w64_2
            let smallDstPtr :: Ptr Word8 = plusPtr dstPtr offset
            let smallTraversePtr :: Ptr Word8 = plusPtr traversePtr offset
            for_ [0 .. littleStrides - 1] $ \i -> do
              w8_1 <- peekElemOff smallDstPtr i
              w8_2 <- peekElemOff smallTraversePtr i
              pokeElemOff smallDstPtr i $ Bits.xor w8_1 w8_2
{-# INLINEABLE xorByteString #-}

-- | Bitwise logical complement, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122).
complementByteString :: ByteString -> ByteString
complementByteString bs = unsafeDupablePerformIO . BS.useAsCStringLen bs $ \(srcPtr, len) -> do
  -- We use loop sectioning here; see Note [Loop sectioning] as to why we do this
  let (bigStrides, littleStrides) = len `quotRem` 8
  let offset = bigStrides * 8
  BSI.create len $ \dstPtr -> do
    let bigSrcPtr :: Ptr Word64 = castPtr srcPtr
    let bigDstPtr :: Ptr Word64 = castPtr dstPtr
    for_ [0 .. bigStrides - 1] $ \i -> do
      w64 <- peekElemOff bigSrcPtr i
      pokeElemOff bigDstPtr i . Bits.complement $ w64
    let smallSrcPtr :: Ptr Word8 = plusPtr srcPtr offset
    let smallDstPtr :: Ptr Word8 = plusPtr dstPtr offset
    for_ [0 .. littleStrides - 1] $ \i -> do
      w8 <- peekElemOff smallSrcPtr i
      pokeElemOff smallDstPtr i . Bits.complement $ w8
{-# INLINEABLE complementByteString #-}

-- | Bit read at index, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122)
readBit :: ByteString -> Int -> BuiltinResult Bool
readBit bs ix
  | ix < 0 = do
      emit "readBit: index out of bounds"
      emit $ "Index: " <> (pack . show $ ix)
      builtinResultFailure
  | ix >= len * 8 = do
      emit "readBit: index out of bounds"
      emit $ "Index: " <> (pack . show $ ix)
      builtinResultFailure
  | otherwise = do
      let (bigIx, littleIx) = ix `quotRem` 8
      let flipIx = len - bigIx - 1
      pure $ Bits.testBit (BS.index bs flipIx) littleIx
  where
    len :: Int
    len = BS.length bs
{-# INLINEABLE readBit #-}

-- | Bulk bit write, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122)
writeBits :: ByteString -> [Integer] -> Bool -> BuiltinResult ByteString
writeBits bs ixs bit = case unsafeDupablePerformIO . try $ go of
  Left (WriteBitsException i) -> do
    emit "writeBits: index out of bounds"
    emit $ "Index: " <> (pack . show $ i)
    builtinResultFailure
  Right result -> pure result
  where
    -- This is written in a somewhat strange way. See Note [writeBits and
    -- exceptions], which covers why we did this.
    go :: IO ByteString
    go = BS.useAsCString bs $ \srcPtr ->
      BSI.create len $
        \dstPtr ->
          let go2 (i : is) = setOrClearAtIx dstPtr i *> go2 is
              go2 _ = pure ()
           in do
                copyBytes dstPtr (castPtr srcPtr) len
                go2 ixs
    len :: Int
    len = BS.length bs
    bitLen :: Integer
    bitLen = fromIntegral len * 8
    setOrClearAtIx :: Ptr Word8 -> Integer -> IO ()
    setOrClearAtIx ptr i
      | i < 0 = throwIO $ WriteBitsException i
      | i >= bitLen = throwIO $ WriteBitsException i
      | otherwise = do
          let (bigIx, littleIx) = i `quotRem` 8
          let flipIx = len - fromIntegral bigIx - 1
          w8 :: Word8 <- peekByteOff ptr flipIx
          let toWrite =
                if bit
                  then Bits.setBit w8 . fromIntegral $ littleIx
                  else Bits.clearBit w8 . fromIntegral $ littleIx
          pokeByteOff ptr flipIx toWrite
    {-# INLINEABLE setOrClearAtIx #-}
{-# INLINEABLE writeBits #-}

{-| Byte replication, as per [CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122)
We want to cautious about the allocation of huge amounts of memory so we
impose the same length limit that's used in integerToByteString. -}
replicateByte :: Integer -> Word8 -> BuiltinResult ByteString
replicateByte len w8
  | len < 0 = do
      emit "replicateByte: negative length requested"
      builtinResultFailure
  | len > maximumOutputLength = do
      emit . pack $
        "replicateByte: requested length is too long (maximum is "
          ++ show maximumOutputLength
          ++ " bytes)"
      emit $ "Length requested: " <> (pack . show $ len)
      builtinResultFailure
  | otherwise = pure . BS.replicate (fromIntegral len) $ w8

{-| Wrapper for calling 'unsafesShiftByteString' safely. Specifically, we avoid various edge cases:

* Empty 'ByteString's and zero moves don't do anything
* Bit moves whose absolute value is larger than the bit length produce all-zeroes

This also ensures we don't accidentally hit integer overflow issues. -}
shiftByteString :: ByteString -> Integer -> ByteString
shiftByteString bs bitMove
  | BS.null bs = bs
  | bitMove == 0 = bs
  | otherwise =
      let len = BS.length bs
          bitLen = fromIntegral $ 8 * len
       in if abs bitMove >= bitLen
            then BS.replicate len 0x00
            -- fromIntegral is safe to use here, as the only way this
            -- could overflow (or underflow) an Int is if we had a
            -- ByteString onchain that was over 30 petabytes in size.
            else unsafeShiftByteString bs (fromIntegral bitMove)

{-| Wrapper for calling 'unsafeRotateByteString' safely. Specifically, we avoid various edge cases:

* Empty 'ByteString's and zero moves don't do anything
* Bit moves whose absolute value is larger than the bit length are reduced modulo the length

Furthermore, we can convert all rotations into positive rotations, by noting that a rotation by @b@
is the same as a rotation by @b `mod` bitLen@, where @bitLen@ is the length of the 'ByteString'
argument in bits. This value is always non-negative, and if we get 0, we have nothing to do. This
reduction also helps us avoid integer overflow issues. -}
rotateByteString :: ByteString -> Integer -> ByteString
rotateByteString bs bitMove
  | BS.null bs = bs
  | otherwise =
      let bitLen = fromIntegral $ 8 * BS.length bs
          -- This is guaranteed non-negative
          reducedBitMove = bitMove `mod` bitLen
       in if reducedBitMove == 0
            then bs
            -- fromIntegral is safe to use here since for a bytestring to have a
            -- size that doesn't fit into an `Int` it would have to have a size
            -- exceeding something like 37 petabytes.
            else unsafeRotateByteString bs (fromIntegral reducedBitMove)

{- Note [Shift and rotation implementation]

Both shifts and rotations work similarly: they effectively impose a 'write
offset' to bits in the data argument, then write those bits to the result with
this offset applied. The difference between them is in what should be done if
the resulting offset index would fall out of bounds: shifts just discard the
data (and fill whatever remains with zeroes), while rotations 'wrap around'
modularly. This operation is bit parallel by definition, thus theoretically
making it amenable to the techniques described in Note [Loop sectioning].

However, the naive way of doing this runs into a problem: the byte ordering
on Tier 1 platforms inside `Word64` means that consecutive bit indexes
according to CIP-122 don't remain that way. We could avoid this by using a
byte flip followed by an adjustment in the opposite direction, then a byte flip
back again. However, this is a costly operation, and would also be extremely
fiddly across stride boundaries, making both performance and implementation
clarity suffer. Instead, we use a different observation, namely that both
shifts and rotations on the same input are monoidally homomorphic into
natural number addition (assuming the same 'direction' for shifts). Using
this, combined with Euclidean division, we can decompose any shift or
rotation by `i` into two consecutive shifts and rotations:

1. A 'large' shift or rotation, by `div i 8`; and
2. A 'small' shift or rotation, by `mod i 8`.

While on paper, this seems much less efficient (as our stride is smaller),
we also observe that the 'large' shift moves around whole bytes, while also
keeping consecutive bytes consecutive, assuming their bit indices remain
in-bounds. This means that we can implement step 1 both simply and efficiently:

\* For shifts, we perform a partial copy of all the bytes whose bits remain
  in-bounds, followed by clearing of whatever remains.
\* For rotations, we perform two partial copies: first of all the bytes whose
  bits remain in-bounds, followed by whatever remains, at the 'opposite end'.

These can make use of the bulk copying and clearing operations provided by the
GHC runtime. Not only are these shorter and more readable, they are also _far_
more efficient than anything we could do, as they rely on optimized C called
via the runtime (meaning no FFI penalty). From our experiments, both with
these operations, and others from CIP-122, we note that the cost of these is
essentially constant up to about the size of 1-2 cache lines (64-128 bytes):
since we anticipate smaller inputs are far more likely, this actually runs
_faster_ than our proposed sectioning approach, while being easier to read
and write.

It is arguable that our approach forces 'double writing', as Step 2 has to
possibly overwrite our work in Step 1. However, by avoiding the need to
perform byte flips, as well as benefitting from the huge speedups gained
from our split approach, this cost is essentially negligible, especially
given that we can operate mutably throughout. We also have an additional
benefit: if the requested rotation or shift happens to be an exact multiple
of 8, we can be _much_ faster, as Step 2 becomes unnecessary in that case.
-}

{-| Shifts, as per [CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123).
This may not actually be unsafe, but it shouldn't be used outside this module. -}
unsafeShiftByteString :: ByteString -> Int -> ByteString
unsafeShiftByteString bs bitMove = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr ->
  BSI.create len $ \dstPtr -> do
    -- To simplify our calculations, we work only with absolute values,
    -- letting different functions control for direction, instead of
    -- trying to unify the scheme for both positive and negative shifts.
    let magnitude = abs bitMove
    -- Instead of worrying about partial clearing, we just zero the entire
    -- block of memory, as the cost is essentially negligible and saves us
    -- a bunch of offset arithmetic.
    fillBytes dstPtr 0x00 len
    unless (magnitude >= bitLen) $ do
      let (bigShift, smallShift) = magnitude `quotRem` 8
      case signum bitMove of
        (-1) -> negativeShift (castPtr srcPtr) dstPtr bigShift smallShift
        _ -> positiveShift (castPtr srcPtr) dstPtr bigShift smallShift
  where
    len :: Int
    !len = BS.length bs
    bitLen :: Int
    !bitLen = len * 8
    negativeShift :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> IO ()
    negativeShift srcPtr dstPtr bigShift smallShift = do
      let copyDstPtr = plusPtr dstPtr bigShift
      let copyLen = len - bigShift
      -- Since we already zeroed everything, we only do the partial copy.
      copyBytes copyDstPtr srcPtr copyLen
      when (smallShift > 0) $ do
        -- When working with the small shift, we have to shift bits across
        -- byte boundaries. Thus, we have to make sure that:
        --
        -- 1. We 'save' our first byte from being processed.
        -- 2. We can 'select' the bits that would be shifted over the
        --    boundary and apply them.
        let !invSmallShift = 8 - smallShift
        let !mask = 0xFF `Bits.unsafeShiftR` invSmallShift
        for_ [len - 1, len - 2 .. len - copyLen] $ \byteIx -> do
          -- To handle shifts across byte boundaries, we have to 'read
          -- backwards', mask off the relevant part, then recombine.
          !(currentByte :: Word8) <- peekByteOff dstPtr byteIx
          !(prevByte :: Word8) <- peekByteOff dstPtr (byteIx - 1)
          let !prevOverflowBits = prevByte Bits..&. mask
          let !newCurrentByte =
                (currentByte `Bits.unsafeShiftR` smallShift)
                  Bits..|. (prevOverflowBits `Bits.unsafeShiftL` invSmallShift)
          pokeByteOff dstPtr byteIx newCurrentByte
        !(firstByte :: Word8) <- peekByteOff dstPtr (len - copyLen - 1)
        pokeByteOff dstPtr (len - copyLen - 1) (firstByte `Bits.unsafeShiftR` smallShift)
    -- This works similarly to `negativeShift` above, but in the opposite direction.
    positiveShift :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> IO ()
    positiveShift srcPtr dstPtr bigShift smallShift = do
      let copySrcPtr = plusPtr srcPtr bigShift
      let copyLen = len - bigShift
      copyBytes dstPtr copySrcPtr copyLen
      when (smallShift > 0) $ do
        let !invSmallShift = 8 - smallShift
        let !mask = 0xFF `Bits.unsafeShiftL` invSmallShift
        for_ [0, 1 .. copyLen - 2] $ \byteIx -> do
          !(currentByte :: Word8) <- peekByteOff dstPtr byteIx
          !(nextByte :: Word8) <- peekByteOff dstPtr (byteIx + 1)
          let !nextOverflowBits = nextByte Bits..&. mask
          let !newCurrentByte =
                (currentByte `Bits.unsafeShiftL` smallShift)
                  Bits..|. (nextOverflowBits `Bits.unsafeShiftR` invSmallShift)
          pokeByteOff dstPtr byteIx newCurrentByte
        !(lastByte :: Word8) <- peekByteOff dstPtr (copyLen - 1)
        pokeByteOff dstPtr (copyLen - 1) (lastByte `Bits.unsafeShiftL` smallShift)

{-| Rotations, as per [CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123).
This is defintely unsafe: calling it with bitMove = minBound::Int can cause a
segmentation fault.  It must not be used outside this module. -}
unsafeRotateByteString :: ByteString -> Int -> ByteString
unsafeRotateByteString bs bitMove = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr ->
  BSI.create len $ \dstPtr -> do
    -- The move is guaranteed positive and reduced already. Thus, unlike for
    -- shifts, we don't need two variants for different directions.
    let (bigRotation, smallRotation) = bitMove `quotRem` 8
    go (castPtr srcPtr) dstPtr bigRotation smallRotation
  where
    len :: Int
    !len = BS.length bs
    go :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> IO ()
    go srcPtr dstPtr bigRotate smallRotate = do
      -- Two partial copies are needed here, unlike with shifts, because
      -- there's no point zeroing our data, since it'll all be overwritten
      -- with stuff from the input anyway.
      let copyStartSrcPtr = plusPtr srcPtr bigRotate
      let copyStartLen = len - bigRotate
      copyBytes dstPtr copyStartSrcPtr copyStartLen
      let copyEndDstPtr = plusPtr dstPtr copyStartLen
      copyBytes copyEndDstPtr srcPtr bigRotate
      when (smallRotate > 0) $ do
        -- This works similarly to shifts
        let !invSmallRotate = 8 - smallRotate
        let !mask = 0xFF `Bits.unsafeShiftL` invSmallRotate
        !(cloneFirstByte :: Word8) <- peekByteOff dstPtr 0
        for_ [0, 1 .. len - 2] $ \byteIx -> do
          !(currentByte :: Word8) <- peekByteOff dstPtr byteIx
          !(nextByte :: Word8) <- peekByteOff dstPtr (byteIx + 1)
          let !nextOverflowBits = nextByte Bits..&. mask
          let !newCurrentByte =
                (currentByte `Bits.unsafeShiftL` smallRotate)
                  Bits..|. (nextOverflowBits `Bits.unsafeShiftR` invSmallRotate)
          pokeByteOff dstPtr byteIx newCurrentByte
        !(lastByte :: Word8) <- peekByteOff dstPtr (len - 1)
        let !firstOverflowBits = cloneFirstByte Bits..&. mask
        let !newLastByte =
              (lastByte `Bits.unsafeShiftL` smallRotate)
                Bits..|. (firstOverflowBits `Bits.unsafeShiftR` invSmallRotate)
        pokeByteOff dstPtr (len - 1) newLastByte

-- | Counting the number of set bits, as per [CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123).
countSetBits :: ByteString -> Int
countSetBits bs = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr -> do
  -- See Note [Loop sectioning] for details of why we
  -- define this function the way it is. We make use of the fact that `popCount`
  -- is bit-parallel, and has a constant-time implementation for `Word64` and `Word8`.
  let bigSrcPtr :: Ptr Word64 = castPtr srcPtr
  let smallSrcPtr :: Ptr Word8 = plusPtr srcPtr offset
  goBig bigSrcPtr smallSrcPtr 0 0
  where
    len :: Int
    !len = BS.length bs
    -- We do this as two separate bindings, for similar reasons as for
    -- `integerToByteString`: we take a surprising hit to performance when
    -- using a pair, even though eliminating it should be possible here.
    bigStrides :: Int
    !bigStrides = len `quot` 8
    smallStrides :: Int
    !smallStrides = len `rem` 8
    offset :: Int
    !offset = bigStrides * 8
    goBig :: Ptr Word64 -> Ptr Word8 -> Int -> Int -> IO Int
    goBig !bigSrcPtr !smallSrcPtr !acc !bigIx
      | bigIx == bigStrides = goSmall smallSrcPtr acc 0
      | otherwise = do
          !w64 <- peekElemOff bigSrcPtr bigIx
          goBig bigSrcPtr smallSrcPtr (acc + Bits.popCount w64) (bigIx + 1)
    goSmall :: Ptr Word8 -> Int -> Int -> IO Int
    goSmall !smallSrcPtr !acc !smallIx
      | smallIx == smallStrides = pure acc
      | otherwise = do
          !w8 <- peekElemOff smallSrcPtr smallIx
          goSmall smallSrcPtr (acc + Bits.popCount w8) (smallIx + 1)

-- | Finding the first set bit's index, as per [CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123).
findFirstSetBit :: ByteString -> Int
findFirstSetBit bs = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr -> do
  let bigSrcPtr :: Ptr Word64 = castPtr srcPtr
  goBig bigSrcPtr 0 (len - 8)
  where
    -- We implement this operation in a somewhat unusual way, to try and
    -- benefit from bit paralellism, thus allowing loop sectioning as well:
    -- see Note [Loop sectioning] as to why we choose to
    -- do this.
    --
    -- Finding the first set bit is not (inherently) bit parallel, as there is
    -- a clear 'horizontal dependency'. Thus, we instead 'localize' this
    -- 'horizontal dependency' by noting that the following operations _are_
    -- bit-parallel:
    --
    -- 1. Checking if all bits are zero
    -- 2. Keeping an additive accumulator
    --
    -- Essentially, we begin by taking large steps through our data, checking
    -- whether we only have zeroes. This can be done in strides of 64 bits at a
    -- time, and every time we find that many zeroes, we keep track. After we
    -- encounter a nonzero `Word64`, we 'step down' to `Word8`-sized steps,
    -- continuing to count zero blocks the same way. Once we encounter a
    -- non-zero `Word8`, we can resort to the specialized operation for
    -- counting trailing zeroes from `Data.Bits`, and 'top up' our accumulated
    -- count to produce the index we want. If we ever 'walk off the end', we
    -- know that there's no way we could find any set bits and return -1.
    --
    -- This is complicated slightly by us having to walk the input backwards
    -- instead of forwards, but due to the requirements of the CIP-122 bit
    -- indexing scheme, we don't really have a choice here. This doesn't
    -- affect the description above however: it just complicates the indexing
    -- maths required.
    goBig :: Ptr Word64 -> Int -> Int -> IO Int
    goBig !bigSrcPtr !acc !byteIx
      -- We can do at least one large step. This works because we read
      -- backwards, which means that `byteIx` is the _last_ position we read
      | byteIx >= 0 = do
          !(w64 :: Word64) <- peekByteOff bigSrcPtr byteIx
          -- In theory, we could use the same technique here as we do in
          -- `goSmall`, namely count speculatively and then compare to 64.
          -- However this is not possible for us, as the native byte ordering
          -- on Tier 1 platforms does not keep consecutive bits _across_ bytes
          -- consecutive, which would make this result unreliable. While we
          -- _could_ do a byte order flip before counting (from the opposite
          -- end) to avoid this, the cost of this operation is much larger
          -- than a comparison to zero, and would only benefit us _once_,
          -- instead of once-per-stride. Thus, we instead use the approach
          -- here.
          if w64 == 0x0
            then goBig bigSrcPtr (acc + 64) (byteIx - 8)
            else goSmall (castPtr bigSrcPtr) acc (byteIx + 7)
      -- We've 'walked off the end' and not found anything, so everything
      -- must be zeroes
      | byteIx <= (-8) = pure (-1)
      -- We can end up here in one of two ways:
      --
      -- 1. Our input `ByteString` is 7 bytes long or smaller; or
      -- 2. We have done all the large steps we can, and have between 1
      --    and 7 bytes to go.
      --
      -- In either case, we forward the accumulator (which will be 0 in
      -- case 1) to small stepping. Combining these cases allows us to
      -- avoid separate tests for these conditions.
      | otherwise = goSmall (castPtr bigSrcPtr) acc (8 + byteIx - 1)
    goSmall :: Ptr Word8 -> Int -> Int -> IO Int
    goSmall !smallSrcPtr !acc !byteIx
      | byteIx < 0 = pure (-1)
      | otherwise = do
          !(w8 :: Word8) <- peekByteOff smallSrcPtr byteIx
          -- Instead of redundantly first checking for a zero byte,
          -- then counting, we speculatively count, relying on the behaviour of
          -- `countTrailingZeros` that, on a zero byte, we get 8.
          let !counted = Bits.countTrailingZeros w8
          let !newAcc = acc + counted
          if counted == 8
            then goSmall smallSrcPtr newAcc (byteIx - 1)
            else pure newAcc
    len :: Int
    !len = BS.length bs

-- Helpers

{- Note [writeBits and exceptions]

   As `writeBits` allows us to pass a changelist argument of any length, we
   potentially could have an out-of-bounds index anywhere in the list. As we
   have to fail on such cases (and report them appropriately), we end up needing
   _both_ IO (to do mutable things) as well as a way to signal errors. We can
   do this in two ways:

   1. Pre-scan the changelist for any out-of-bounds indexes, fail if we see any,
      then apply the necessary changes if no out-of-bounds indexes are found.
   2. Speculatively allocate the new `ByteString`, then do the changes in the
      changelist argument one at a time, failing as soon as we see an out-of-bounds
      index.

  Option 1 would require traversing the changelist argument twice, which is
  undesirable, which means that option 2 is the more efficient choice. The
  natural choice for option 2 would be something similar to `ExceptT Int IO`
  (with the `Int` being an out-of-bounds index). However, we aren't able to do
  this, as ultimately, `ByteString`s are implemented as `ForeignPtr`s, forcing
  us to use the following function to interact with them, directly or not:

  withForeignPtr :: forall (a :: Type) . ForeignPtr a -> (Ptr a -> IO b) -> IO b

  Notably, the function argument produces a result of `IO b`, whereas we would
  need `MonadIO m => m b` instead. This means that our _only_ choice is to
  use the exception mechanism, either directly or via some wrappers like
  `MonadUnliftIO`. While this is unusual, and arguably against the spirit of
  the use of `IO` relative `ByteString` construction, we don't have any other
  choice. We decided to use the exception mechanism directly, as while
  `MonadUnliftIO` is a bit cleaner, it ultimately ends up doing the same thing
  anyway, and this method at least makes it clear what we're doing.

  This doesn't pose any problems from the point of view of Plutus Core, as this
  exception cannot 'leak'; we handle it entirely within `writeBits`, and no
  other Plutus Core code can ever see it.
-}
newtype WriteBitsException = WriteBitsException Integer
  deriving stock (Eq, Show)

instance Exception WriteBitsException

{- Note [Manual specialization]
For both integerToByteString and byteStringToInteger, we have to perform very
similar operations, but with small variations:

- Most-significant-first versus most-significant-last (for both)
- Whether we have a size limit or not (for integerToByteString)

Additionally, loop sectioning (see Note [Loop sectioning]) requires us to have
separate 'big-stride' and 'small-stride' operations to ensure universality of
input handling. Lastly, we have several subroutines (digit extraction, for
instance) that may vary in similar ways. In such a case, generalization by
means of abstraction seems like a good idea, as the operations (and
subroutines) vary little.

At the same time, to determine which variation of any given function (or
subroutine) we need, we only have to scrutinize the relevant argument(s) once:
these specifics (such as byte order) don't change during the course of the
operation. Thus, we want to make sure that these checks in the code are _also_
performed only once, ideally at the beginning.

However, if we write such operations naively as so:

> subroutine byteOrder arg1 arg2 = case byteOrder of
>       LittleEndian -> ...
>       BigEndian -> ...

the byteOrder argument will be scrutinized on each call of subroutine. This is
correct in general (as there is no guarantee that the argument will be stable).
Strangely, however, even in a case like this one:

> mainRoutine byteOrder arg1 arg2 = ...
>    where
>       subroutine arg3 = case byteOrder of
>           LittleEndian -> ...
>           BigEndian -> ...

GHC _still_ re-scrutinizes byteOrder in every call of subroutine! This penalty
can be somewhat lessened using a form similar to this:

> mainRoutine byteOrder arg1 arg2 = ...
>     where
>        !subroutine = case byteOrder of
>             LittleEndian -> \arg3 -> ...
>             BigEndian -> \arg3 -> ...

but this is _still_ between 20 and 30% worse than doing something like this:

> mainRoutine byteOrder arg1 arg2 = case byteOrder of
>     LittleEndian -> [code calling subroutineLE where needed]
>     BigEndian -> [code calling subroutineBE where needed]
>     where
>         subroutineLE arg3 = ...
>         subroutineBE arg3 = ...

This form _ensures_ we scrutinize (and branch) only the number of times we have
to, and in a predictable place. Since these are backends for Plutus Core primops,
and performance is thus critical, we choose to use this manually-specialized form
for each combination of relevant arguments. While this is repetitive, and thus
also somewhat error-prone, the performance penalty for not doing this is
unacceptable.
-}

{- Note [Loop sectioning]

Several operations in this module (including binary logical operations,
`integerToByteString` and `byteStringToInteger`) effectively function as loops
over fixed-width binary chunks: these can be bytes (for logical operations),
digits (for conversions) or something else. These chunks have to be read,
written or both, and may also require processing using fixed-width,
constant-time operations over those chunks from the Haskell side, in some
cases effectively 'translating' these fixed-size operations into variable-width
equivalents over `ByteString`s. In all cases, this involves trafficking data
between memory and machine registers (as `ByteString`s and `Integer`s are both
wrappers around counted arrays), as well as the overheads of looping
(involving comparison and branches). This trafficking is necessary not only to
move the memory around, but also to process it, as on modern architectures,
data must first be moved into a register in order to do anything with it.

However, on all architectures of interest (essentially, 64-bit Tier 1),
general-purpose registers (GPRs henceforth) are 64 bits (or 8 bytes).
Furthermore, the primary cost of moving data between memory and registers is
having to overcome the 'memory wall': the exact amount of data being moved
doesn't affect this very much. In addition to this, when we operate on single
bytes, the remaining 56 bits of the GPR holding that data are essentially
'wasted'. In the situation we have (namely, operating over arrays, whose data
is adjacent in memory), we thus get two sources of inefficiency:

\* Despite paying the cost for a memory transfer, we transfer only one-eighth
  the data we could; and
\* Despite transferring data from memory to registers, we utilize the register
  at only one-eighth capacity.

This essentially means we perform _eight times_ more rotations of the loop,
and memory moves, than we need to!

To avoid this, we use a technique known as _loop sectioning_.
Effectively, this transforms our homogenous loop (that always operates one byte at
a time) into a heterogenous loop: first, we operate on a larger section (called
a _stride_) until we can no longer do this, and then we finish up using byte
at a time processing. Essentially, when given an input like this:

[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

the homogeous byte-at-a-time approach would process it like so:

  _   _   _   _   _   _   _   _   _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

for a total of 10 memory transfers and 10 loop spins, whereas a loop-sectioned
approach with a stride of 8 would instead process like so:

  ______________________________  _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

Giving us only _three_ memory transfers and _three_ loop spins instead. This
effectively reduces our work by a factor of 8. In our cases, this is almost
free, as there is no data processing to be done: all we need to do is copy
from one place to another, essentially.

This technique only benefits us because counted arrays are cache-friendly: see
Note [Superscalarity and caching] for a longer explanation of this and why it
matters.

Further information:

- Tier 1 GHC platform list:
    https://gitlab.haskell.org/ghc/ghc/-/wikis/platforms#tier-1-platforms
- Memory wall:
    https://link.springer.com/referenceworkentry/10.1007/978-0-387-09766-4_234
- Loop sectioning in more detail:
    http://physics.ujep.cz/~zmoravec/prga/main_for/mergedProjects/optaps_for/common/optaps_vec_mine.htm
-}

{- Note [Superscalarity and caching]
On modern architectures, in order to process data, it must first be moved from
memory into a register. This operation has some cost (known as the 'memory wall'),
which is largely independent of how much data gets moved (assuming the register
can hold it): moving one byte, or a whole register's worth, costs about the same.
To reduce this cost, CPU manufacturers have introduced _cache hierarchies_,
which are designed to limit the cost of the wall, as long as the data access
matches the cache's optimal usage pattern. Thus, while an idealized view of
the memory hierachy is this:

Registers
---------
Memory

in reality, the view is more like this:

Registers
---------
L1 cache
---------
L2 cache
---------
L3 cache (on some platforms)
---------
Memory

Each 'higher' cache in the hierarchy is smaller, but faster, and when a memory
fetch is requested in code, in addition to moving the requested data to a
register, that data (plus some more) is moved into caches as well. The amount
of data moved into cache (a _cache line_) is typically eight machine words on
modern architectures (and definitely is the case for all Tier 1 GHC platforms):
for the cases concerning Plutus, that is 64 bytes. Therefore, if data we need
soon after a fetch is _physically_ nearby, it won't need to be fetched from
memory: instead, it would come from a cache, which is faster (by a considerable
margin).

To see how this can matter, consider the following ByteString:

[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 ]

The ByteString (being a counted array) has all of its data physically adjacent
to each other. Suppose we wanted to fetch the byte at index 1 (second position).
The naive view of what happens is like this:

Registers: [b2] [ ] [ ] .... [ ]
Memory: [ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 ]

Thus, it would appear that, if we wanted a different position's value, we would
need to fetch from memory again. However, what _actually_ happens is more like this:

Registers: [b2] [ ] [ ] .... [ ]
L1 cache: [ b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 ]
Memory: [ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 ]

We note that b2, as well as its adjacent elements, were _all_ pulled into the L1
cache. This can only work because all these elements are physically adjacent in
memory. The improvement in performance from this cache use is _very_ non-trivial:
an L1 cache is about 200 times faster than a memory access, and an L2 cache about
20 times faster.

To take further advantage of this, modern CPUs (and all Tier 1 GHC platforms have
this capability) are _superscalar_. To explain what this means, let's consider the
naive view of how CPUs execute instructions: namely, it is one-at-a-time, and
synchronous. While CPUs must give the _appearance_ that they behave this way, in
practice, CPU execution is very much asynchronous: due to the proliferation of ALUs
on a single chip, having twice as many processing units is much cheaper than having
processing units run twice as fast. Thus, if there are no data dependencies
between instructions, CPUs can (and do!) execute them simultaneously, stalling to
await results if a data dependency is detected. This can be done automatically
using Tomasulo's algorithm, which ensures no conflicts with maximum throughput.

Superscalarity interacts well with the cache hierarchy, as it makes data more
easily available for processing, provided there is enough 'work to do', and no
data dependencies. In our situation, most of what we do is data _movement_ from
one memory location to another, which by its very nature lacks any data
dependencies.

Further references:

- Numbers for cache and memory transfers: https://gist.github.com/jboner/2841832
- Superscalarity: https://en.wikipedia.org/wiki/Superscalar_processor
- Tomasulo's algorithm: https://en.wikipedia.org/wiki/Tomasulo%27s_algorithm
-}
