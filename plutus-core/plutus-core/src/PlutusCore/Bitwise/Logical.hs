-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}

-- | Implementations of bitwise logical primops.
module PlutusCore.Bitwise.Logical (
  andByteString,
  orByteString,
  xorByteString,
  complementByteString,
  readBit,
  writeBits,
  replicateByte
  ) where

import Control.Exception (Exception, throw, try)
import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal qualified as BSI
import Data.Foldable (for_, traverse_)
import Data.Text (pack)
import Data.Word (Word64, Word8)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peekByteOff, peekElemOff, pokeByteOff, pokeElemOff)
import PlutusCore.Builtin (BuiltinResult, emit)
import PlutusCore.Evaluation.Result (evaluationFailure)
import System.IO.Unsafe (unsafeDupablePerformIO)

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

-- | Bitwise logical AND, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md).
{-# INLINEABLE andByteString #-}
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

-- | Bitwise logical OR, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md).
{-# INLINEABLE orByteString #-}
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

-- | Bitwise logical XOR, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md).
{-# INLINEABLE xorByteString #-}
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

-- | Bitwise logical complement, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md).
{-# INLINEABLE complementByteString #-}
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

-- | Bit read at index, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md)
{-# INLINEABLE readBit #-}
readBit :: ByteString -> Int -> BuiltinResult Bool
readBit bs ix
  | ix < 0 = do
      emit "readBit: index out of bounds"
      emit $ "Index: " <> (pack . show $ ix)
      evaluationFailure
  | ix >= len * 8 = do
      emit "readBit: index out of bounds"
      emit $ "Index: " <> (pack . show $ ix)
      evaluationFailure
  | otherwise = do
      let (bigIx, littleIx) = ix `quotRem` 8
      let flipIx = len - bigIx - 1
      pure $ Bits.testBit (BS.index bs flipIx) littleIx
  where
    len :: Int
    len = BS.length bs

-- | Bulk bit write, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md)
{-# INLINEABLE writeBits #-}
writeBits :: ByteString -> [(Integer, Bool)] -> BuiltinResult ByteString
writeBits bs changelist = case unsafeDupablePerformIO . try $ go of
  Left (WriteBitsException i) -> do
    emit "writeBits: index out of bounds"
    emit $ "Index: " <> (pack . show $ i)
    evaluationFailure
  Right result -> pure result
  where
    -- This is written in a somewhat strange way. See Note [writeBits and
    -- exceptions], which covers why we did this.
    go :: IO ByteString
    go = BS.useAsCString bs $ \srcPtr ->
          BSI.create len $ \dstPtr -> do
            copyBytes dstPtr (castPtr srcPtr) len
            traverse_ (setAtIx dstPtr) changelist
    len :: Int
    len = BS.length bs
    bitLen :: Integer
    bitLen = fromIntegral len * 8
    setAtIx :: Ptr Word8 -> (Integer, Bool) -> IO ()
    setAtIx ptr (i, b)
      | i < 0 = throw $ WriteBitsException i
      | i >= bitLen = throw $ WriteBitsException i
      | otherwise = do
          let (bigIx, littleIx) = i `quotRem` 8
          let flipIx = len - fromIntegral bigIx - 1
          w8 :: Word8 <- peekByteOff ptr flipIx
          let toWrite = if b
                        then Bits.setBit w8 . fromIntegral $ littleIx
                        else Bits.clearBit w8 . fromIntegral $ littleIx
          pokeByteOff ptr flipIx toWrite

-- | Byte replication, as per [CIP-122](https://github.com/mlabs-haskell/CIPs/blob/koz/logic-ops/CIP-0122/CIP-0122.md)
replicateByte :: Int -> Word8 -> BuiltinResult ByteString
replicateByte len w8
  | len < 0 = do
      emit "replicateByte: negative length requested"
      evaluationFailure
  | otherwise = pure . BS.replicate len $ w8

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

{- Note [Loop sectioning]

Several operations in this module effectively function as loops over bytes,
which have to be read, written, or both. Furthermore, we usually need to
process these bytes somehow, typically using fixed-width bitwise operations
from the Haskell side, thus allowing us to 'translate' these same operations
to the variable-width `ByteString` arguments we are dealing with. This involves
significant trafficking of data between memory and machine registers (as
`ByteString`s are wrapped counted arrays), as well as the overheads of looping
(involving comparisons and branches). This trafficking is necessary not only
to move the memory around, but also to process it, as on modern architectures,
data must first be moved into a register in order to do anything with it.

On all architectures of interest (essentially, 64-bit Tier 1), general-purpose
registers (GPRs henceforth) are 64 bits (or 8 bytes) wide. Furthermore, the
primary cost of moving data between memory and registers is having to overcome
the 'memory wall': the exact amount of data being moved doesn't affect this
much. In addition to this, when we operate on single bytes, the remaining 56
bits of the GPR holding that data are essentially 'wasted'. In the situation
we are in (namely, operating over arrays, whose data is adjacent in memory),
we thus get two sources of inefficiency:

* Despite paying the cost for a memory transfer, we move only one-eighth of
  the data we could; and
* Despite transferring data from memory to registers, we use these registers
  only at one-eighth capacity.

In short, we do _eight times_ more rotations of the loop, and memory moves,
than we need to!

To avoid this, we use a technique called _loop sectioning_. Effectively, this
transforms our homogenous loop (that always works one byte at a time) into a
heterogenous loop: first, we operate on a larger section (called a _stride_)
until we can no longer do this, and then we finish up using byte at a time
processing. Essentially, given an input like this:

[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

the homogeous byte-at-a-time approach would process it like so:

  _   _   _   _   _   _   _   _   _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

for a total of 10 memory transfers and 10 loop spins, whereas a loop-sectioned
approach with a stride of 8 would instead process like so:

  ______________________________  _   _
[ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 ]

This gives us only _three_ memory transfers and _three_ loop spins instead. This
effectively reduces our work by a factor of 8. In our cases, this is significant.

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
