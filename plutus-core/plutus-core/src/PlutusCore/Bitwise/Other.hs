-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}

-- | Implementation for shifts, rotation, popcount and find-first-set
module PlutusCore.Bitwise.Other (
  shiftByteString,
  rotateByteString,
  countSetBits,
  findFirstSetBit
  ) where

import Control.Monad (unless, when)
import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal qualified as BSI
import Data.Foldable (for_)
import Data.Word (Word64, Word8)
import Foreign.Marshal.Utils (copyBytes, fillBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peekByteOff, peekElemOff, pokeByteOff)
import System.IO.Unsafe (unsafeDupablePerformIO)

{- Note [Shift and rotation implementation]

Both shifts and rotations work similarly: they effectively impose a 'write
offset' to bits in the data argument, then write those bits to the result
with this offset applied. The difference between them is in what should be
done if the resulting offset index would fall out of bounds: shifts just
discard the data (and fill whatever remains with zeroes), while rotations
'wrap around' modularly. This operation is bit parallel by definition, thus
theoretically making it amenable to the techniques described in Note [Bit
parallelism and loop sectioning].

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

* For shifts, we perform a partial copy of all the bytes whose bits remain
  in-bounds, followed by clearing of whatever remains.
* For rotations, we perform two partial copies: first of all the bytes whose
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

-- | Shifts, as per [this
-- CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md).
shiftByteString :: ByteString -> Int -> ByteString
shiftByteString bs bitMove
  | BS.null bs = bs
  | bitMove == 0 = bs
  | otherwise = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr ->
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
            _    -> positiveShift (castPtr srcPtr) dstPtr bigShift smallShift
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

-- | Rotations, as per [this
-- CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md).
rotateByteString :: ByteString -> Int -> ByteString
rotateByteString bs bitMove
  | BS.null bs = bs
  | otherwise =
      -- To save ourselves some trouble, we work only with absolute shifts
      -- (letting argument sign handle dispatch to dedicated 'directional'
      -- functions, like for shifts), and also simplify rotations larger than
      -- the bit length to the equivalent value modulo the bit length, as
      -- they're equivalent.
      let !magnitude = abs bitMove
          !reducedMagnitude = magnitude `rem` bitLen
       in if reducedMagnitude == 0
            then bs
            else unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr ->
              BSI.create len $ \dstPtr -> do
                let (bigRotation, smallRotation) = reducedMagnitude `quotRem` 8
                case signum bitMove of
                  (-1) -> negativeRotate (castPtr srcPtr) dstPtr bigRotation smallRotation
                  _    -> positiveRotate (castPtr srcPtr) dstPtr bigRotation smallRotation
  where
    len :: Int
    !len = BS.length bs
    bitLen :: Int
    !bitLen = len * 8
    negativeRotate :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> IO ()
    negativeRotate srcPtr dstPtr bigRotate smallRotate = do
      -- Two partial copies are needed here, unlike with shifts, because
      -- there's no point zeroing our data, since it'll all be overwritten
      -- with stuff from the input anyway.
      let copyStartDstPtr = plusPtr dstPtr bigRotate
      let copyStartLen = len - bigRotate
      copyBytes copyStartDstPtr srcPtr copyStartLen
      let copyEndSrcPtr = plusPtr srcPtr copyStartLen
      copyBytes dstPtr copyEndSrcPtr bigRotate
      when (smallRotate > 0) $ do
        -- This works similarly as for shifts.
        let invSmallRotate = 8 - smallRotate
        let !mask = 0xFF `Bits.unsafeShiftR` invSmallRotate
        !(cloneLastByte :: Word8) <- peekByteOff dstPtr (len - 1)
        for_ [len - 1, len - 2 .. 1] $ \byteIx -> do
          !(currentByte :: Word8) <- peekByteOff dstPtr byteIx
          !(prevByte :: Word8) <- peekByteOff dstPtr (byteIx - 1)
          let !prevOverflowBits = prevByte Bits..&. mask
          let !newCurrentByte =
                (currentByte `Bits.unsafeShiftR` smallRotate)
                  Bits..|. (prevOverflowBits `Bits.unsafeShiftL` invSmallRotate)
          pokeByteOff dstPtr byteIx newCurrentByte
        !(firstByte :: Word8) <- peekByteOff dstPtr 0
        let !lastByteOverflow = cloneLastByte Bits..&. mask
        let !newLastByte =
              (firstByte `Bits.unsafeShiftR` smallRotate)
                Bits..|. (lastByteOverflow `Bits.unsafeShiftL` invSmallRotate)
        pokeByteOff dstPtr 0 newLastByte
    positiveRotate :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> IO ()
    positiveRotate srcPtr dstPtr bigRotate smallRotate = do
      let copyStartSrcPtr = plusPtr srcPtr bigRotate
      let copyStartLen = len - bigRotate
      copyBytes dstPtr copyStartSrcPtr copyStartLen
      let copyEndDstPtr = plusPtr dstPtr copyStartLen
      copyBytes copyEndDstPtr srcPtr bigRotate
      when (smallRotate > 0) $ do
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

-- | Counting the number of set bits, as per [this
-- CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md).
countSetBits :: ByteString -> Int
countSetBits bs = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr -> do
  -- See Note [Bit parallelism and loop sectioning] for details of why we
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

-- | Finding the first set bit's index, as per [this
-- CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md).
findFirstSetBit :: ByteString -> Int
findFirstSetBit bs = unsafeDupablePerformIO . BS.useAsCString bs $ \srcPtr -> do
  let bigSrcPtr :: Ptr Word64 = castPtr srcPtr
  goBig bigSrcPtr 0 (len - 8)
  where
    -- We implement this operation in a somewhat unusual way, to try and
    -- benefit from bit paralellism, thus allowing loop sectioning as well:
    -- see Note [Bit parallelism and loop sectioning] as to why we choose to
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
      | byteIx <= (-8) = pure (-1)
      | otherwise = goSmall (castPtr bigSrcPtr) 0 (8 + byteIx - 1)
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

{- Note [Bit parallelism and loop sectioning]
All of the operations defined in this module effectively function as loops
over bits, which have to be read and/or written. In particular, this
involves two operations:

1. Trafficking data between memory and machine registers; and
2. Extraction of individual bits from larger chunks (either bytes or whole
   machine words).

There are also looping overheads as well, which involve comparisons and
branches.

On all architectures of interest (essentially, 64-bit Tier 1), general-purpose
registers (GPRs henceforth) are 64 bits (or 8 bytes). Furthermore, the primary
cost of moving data between memory and registers is having to overcome the
'memory wall': the exact amount of data being moved doesn't affect this very
much. In addition to this, when we operate on single bits, the remaining 63
bits of the GPR holding that data are essentially 'wasted'. In the situation
we have (namely, operating over `ByteString`s, which are packed arrays), we
get two sources of inefficiency:

* Despite paying the cost for a memory transfer, we transfer only
  one-sixty-fourth the data we could; and
* Despite transferring data from memory to registers, we utilize the register
  at only one-sixty-fourth capacity.

This essentially means we perform _sixty-four times_ more rotations of the
loop, and memory moves, than we need to!

We can reduce this inefficiency considerably by using a combination of
techniques. The first of these is _bit parallelism_, which performs operations
on single bits in parallel across larger sections of data. This can only be
done if the operation in question has no 'horizontal dependencies': namely,
that the operation is a homomorphism into a monoid from single bits. To see
why this is possible, consider the following byte, denoted as an array of its
bits:

[1, 0, 1, 1, 0, 1, 0, 1]

Suppose we wanted to count the number of set bits in that byte: this is a
homomorphism into natural numbers under addition, and any given bit value
doesn't change what it is 'morphed' into. Thus, we can count all the bits
in parallel:

1. ((1 + 0) + (1 + 1)) + ((0 + 1) + (0 + 1))
2. (1 + 2) + (1 + 1)
3. (3 + 2)
4. 5

This can be done across any span, whether it is one bit, eight bits, or
sixty-four bits. The largest such span GHC allows us to work on portably is
`Word64` (that is, 64 bits), but our input data is a `ByteString`, which stores
bytes. In theory, this would force us to use at most 8-way bit paralellism,
which would reduce our penalty from a factor of 64 to a factor of 8.

However, we can remove even that inefficiency using an additional technique:
_loop sectioning_. This would turn our homogenous loop (that always operates
one byte at a time) into a heterogenous loop: first, we operate on a larger
section (or _stride_) until we can no longer do this, and then finish up using
byte-at-a-time processing. Essentially, given an input like this:

[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

the homogeous byte-at-a-time approach would process it like so:

  _   _   _   _   _   _   _   _   _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

for a total of 10 memory transfers and 10 loop spins, whereas a loop-sectioned
approach with a stride of 8 would instead process like so:

  ______________________________  _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

Giving us only _three_ memory transfers and _three_ loop spins instead. This
effectively reduces our work by a further factor of 8. Since our operations
(reads, writes and counts of bits primarily, with some others) are all
bit-parallel, this is almost free.

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
