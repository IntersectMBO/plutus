-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}

-- | Implementations for conversion primops from 'Integer' to 'ByteString' and back again.
module PlutusCore.Builtin.Convert (
  -- Wrappers
  integerToByteStringWrapper,
  byteStringToIntegerWrapper,
  -- Implementation details
  IntegerToByteStringError(..),
  integerToByteString,
  byteStringToInteger
  ) where

import ByteString.StrictBuilder (Builder)
import ByteString.StrictBuilder qualified as Builder
import Control.Monad (guard)
import Data.Bits (unsafeShiftL, unsafeShiftR, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (pack)
import Data.Word (Word64)
import GHC.ByteOrder (ByteOrder (BigEndian, LittleEndian))
import PlutusCore.Builtin.Emitter (Emitter, emit)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))

-- | Wrapper for 'integerToByteString' to make it more convenient to define as a builtin.
integerToByteStringWrapper ::
  Bool -> Integer -> Integer -> Emitter (EvaluationResult ByteString)
integerToByteStringWrapper endiannessArg paddingArg input
-- As this builtin hasn't been costed yet, we have to impose a temporary limit of 10KiB on requested
-- sizes via the padding argument. This shouldn't be necessary long-term, as once this function is
-- costed, this won't be a problem.
  | paddingArg > 10240 = do
      emit "builtinIntegerToByteString: padding argument too large"
      emit "If you are seeing this, it is a bug: please report this!"
      pure EvaluationFailure
  | otherwise = let endianness = if endiannessArg then BigEndian else LittleEndian in
    -- We use fromIntegral here, despite advice to the contrary in general when defining builtin
    -- denotations. For why we do this (and why it's both inevitable and not really a concern
    -- anyway), see Note [fromIntegral and padding arguments].
    case integerToByteString (fromIntegral (max 0 paddingArg)) endianness input of
      Left err -> case err of
        NegativeInput -> do
          emit "builtinIntegerToByteString: cannot convert negative Integer"
          emit $ "Input: " <> (pack . show $ input)
          pure EvaluationFailure
        NotEnoughDigits -> do
          emit "builtinIntegerToByteString: cannot represent Integer in given number of digits"
          emit $ "Input: " <> (pack . show $ input)
          emit $ "Digits requested: " <> (pack . show $ paddingArg)
          pure EvaluationFailure
      Right result -> pure . pure $ result

-- | Wrapper for 'byteStringToInteger' to make it more convenient to define as a builtin.
byteStringToIntegerWrapper ::
  Bool -> ByteString -> Emitter (EvaluationResult Integer)
byteStringToIntegerWrapper statedEndiannessArg input =
  let endianness = if statedEndiannessArg then BigEndian else LittleEndian in
    case byteStringToInteger endianness input of
      Nothing -> do
        emit "builtinByteStringToInteger: cannot convert empty ByteString"
        pure EvaluationFailure
      Just result -> pure . pure $ result

-- | Structured type to help indicate conversion errors.
data IntegerToByteStringError =
  NegativeInput |
  NotEnoughDigits
  deriving stock (Eq, Show)

-- | Conversion from 'Integer' to 'ByteString', as per
-- [CIP-0087](https://github.com/cardano-foundation/CIPs/pull/624).
--
-- For performance and clarity, the endianness argument uses
-- 'ByteOrder', and the padding argument is an 'Int'.
integerToByteString ::
  Int -> ByteOrder -> Integer -> Either IntegerToByteStringError ByteString
integerToByteString requestedLength requestedByteOrder i = case signum i of
  (-1) -> Left NegativeInput
  0 -> Right . BS.replicate (max 1 requestedLength) $ 0x00
  _ -> do
      -- We use manual specialization to ensure as few branches in loop bodies
      -- as we can. See Note [Manual specialization] for details.
      let result = case (requestedByteOrder, requestedLength > 0) of
                      (LittleEndian, True)  -> goLELimit mempty i
                      (LittleEndian, False) -> pure $ goLENoLimit mempty i
                      (BigEndian, True)     -> goBELimit mempty i
                      (BigEndian, False)    -> pure $ goBENoLimit mempty i
      case result of
        Nothing -> Left NotEnoughDigits
        Just b  -> pure . Builder.builderBytes $ b
  where
    goLELimit :: Builder -> Integer -> Maybe Builder
    goLELimit acc remaining
      | remaining == 0 = pure $ padLE acc
      | otherwise = do
          guard (Builder.builderLength acc < requestedLength)
          -- This allows extracting eight digits at once. See Note [Loop sectioning] for details on
          -- why we do this. We also duplicate this code in several places: see Note [Manual
          -- specialization] for why.
          --
          -- The code is basically equivalent to remaining `quotRem` 2^64, but more efficient. This
          -- is for two reasons: firstly, GHC does not optimize divisions into shifts for Integer
          -- (even if the divisor is constant), and secondly, the pair generated by `quotRem` costs
          -- us as much as 15% peformance, and GHC seems unable to eliminate it. Thus, we have to do
          -- it like this instead.
          let newRemaining = remaining `unsafeShiftR` 64
          let digitGroup = fromInteger remaining
          case newRemaining of
            0 -> finishLELimit acc digitGroup
            _ -> goLELimit (acc <> Builder.storable digitGroup) newRemaining
    finishLELimit :: Builder -> Word64 -> Maybe Builder
    finishLELimit acc remaining
      | remaining == 0 = pure $ padLE acc
      | otherwise = do
          guard (Builder.builderLength acc < requestedLength)
          -- This is equivalent to 'remaining `quotRem` 256' followed by a conversion of the
          -- remainder, but faster. This is similar to the larger example above, and we do it for
          -- the same reasons.
          let newRemaining = remaining `unsafeShiftR` 8
          let digit = fromIntegral remaining
          finishLELimit (acc <> Builder.word8 digit) newRemaining
    -- By separating the case where we don't need to concern ourselves with a user-specified limit,
    -- we can avoid branching needlessly, or doing a complex expression check on every loop. See
    -- Note [Manual specialization] for why this matters.
    goLENoLimit :: Builder -> Integer -> Builder
    goLENoLimit acc remaining
      | remaining == 0 = padLE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 64
                        digitGroup = fromInteger remaining
          in case newRemaining of
              0 -> finishLENoLimit acc digitGroup
              _ -> goLENoLimit (acc <> Builder.storable digitGroup) newRemaining
    finishLENoLimit :: Builder -> Word64 -> Builder
    finishLENoLimit acc remaining
      | remaining == 0 = padLE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 8
                        digit = fromIntegral remaining
                      in finishLENoLimit (acc <> Builder.word8 digit) newRemaining
    padLE :: Builder -> Builder
    padLE acc = let paddingLength = requestedLength - Builder.builderLength acc
      in acc <> Builder.bytes (BS.replicate paddingLength 0x0)
    -- We manually specialize the big-endian case: see Note [Manual specialization] for why.
    goBELimit :: Builder -> Integer -> Maybe Builder
    goBELimit acc remaining
      | remaining == 0 = pure $ padBE acc
      | otherwise = do
          guard (Builder.builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 64
          let digitGroup = fromInteger remaining
          case newRemaining of
            0 -> finishBELimit acc digitGroup
            _ -> goBELimit (Builder.word64BE digitGroup <> acc) newRemaining
    finishBELimit :: Builder -> Word64 -> Maybe Builder
    finishBELimit acc remaining
      | remaining == 0 = pure $ padBE acc
      | otherwise = do
          guard (Builder.builderLength acc < requestedLength)
          let newRemaining = remaining `unsafeShiftR` 8
          let digit = fromIntegral remaining
          finishBELimit (Builder.word8 digit <> acc) newRemaining
    goBENoLimit :: Builder -> Integer -> Builder
    goBENoLimit acc remaining
      | remaining == 0 = padBE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 64
                        digitGroup = fromInteger remaining
                      in case newRemaining of
                        0 -> finishBENoLimit acc digitGroup
                        _ -> goBENoLimit (Builder.word64BE digitGroup <> acc) newRemaining
    finishBENoLimit :: Builder -> Word64 -> Builder
    finishBENoLimit acc remaining
      | remaining == 0 = padBE acc
      | otherwise = let newRemaining = remaining `unsafeShiftR` 8
                        digit = fromIntegral remaining
                      in finishBENoLimit (Builder.word8 digit <> acc) newRemaining
    padBE :: Builder -> Builder
    padBE acc = let paddingLength = requestedLength - Builder.builderLength acc in
      Builder.bytes (BS.replicate paddingLength 0x0) <> acc

-- | Conversion from 'ByteString' to 'Integer', as per
-- [CIP-0087](https://github.com/cardano-foundation/CIPs/pull/624).
--
-- For clarity, the stated endianness argument uses 'ByteOrder'. Since we only have one failure
-- condition, we work in 'Maybe', and let the wrapper handle the only possible error.
byteStringToInteger :: ByteOrder -> ByteString -> Maybe Integer
byteStringToInteger statedByteOrder bs = do
  guard (not . BS.null $ bs)
  -- We use manual specialization to ensure as few branches in loop bodies as we can. See Note
  -- [Manual specialization] for details.
  pure $ case statedByteOrder of
    -- Since padding bytes in the most-significant-last representation go at the end of the input,
    -- we can skip decoding them, as they won't affect the result in any way.
    LittleEndian -> case BS.findIndexEnd (/= 0x0) bs of
      Nothing  -> 0
      Just end -> goLE 0 end 0 0
    -- Since padding bytes in the most-significant-first representation go at the beginning of the
    -- input, we can skip decoding them, as they won't affect the result in any way.
    BigEndian -> case BS.findIndex (/= 0x0) bs of
      Nothing  -> 0
      Just end -> goBE 0 end 0 (BS.length bs - 1)
  where
    -- Like with toByteString, we use loop sectioning to decode eight digits at once. See Note [Loop
    -- sectioning] for why we do this.
    goLE :: Integer -> Int -> Int -> Int -> Integer
    goLE acc limit shift ix
      | ix <= (limit - 7) =
          let digitGroup = read64LE ix
              newShift = shift + 64
              newIx = ix + 8
           in if digitGroup == 0
                then goLE acc limit newShift newIx
                else
                  -- We use unsafeShiftL to move a group of eight digits into the right position in
                  -- the result, then combine with the accumulator. This is equivalent to a
                  -- multiplication by 2^64*k, but significantly faster, as GHC doesn't optimize
                  -- such multiplications into shifts for Integers.
                  goLE (acc + fromIntegral digitGroup `unsafeShiftL` shift) limit newShift newIx
      | otherwise = finishLE acc limit shift ix
    finishLE :: Integer -> Int -> Int -> Int -> Integer
    finishLE acc limit shift ix
      | ix > limit = acc
      | otherwise =
          let digit = BS.index bs ix
              newShift = shift + 8
              newIx = ix + 1
           in if digit == 0
                then finishLE acc limit newShift newIx
                -- Similarly to before, we use unsafeShiftL to move a single digit into the right
                -- position in the result.
                else finishLE (acc + fromIntegral digit `unsafeShiftL` shift) limit newShift newIx
    -- Technically, ByteString does not allow reading of anything bigger than a single byte.
    -- However, because ByteStrings are counted arrays, caching already brings in adjacent bytes,
    -- which makes fetching them quite cheap. Additionally, GHC appears to optimize this into a
    -- block read of 64 bits at once, which saves memory movement. See Note [Superscalarity and
    -- caching] for details of why this matters.
    read64LE :: Int -> Word64
    read64LE startIx =
      fromIntegral (BS.index bs startIx)
        .|. (fromIntegral (BS.index bs (startIx + 1)) `unsafeShiftL` 8)
        .|. (fromIntegral (BS.index bs (startIx + 2)) `unsafeShiftL` 16)
        .|. (fromIntegral (BS.index bs (startIx + 3)) `unsafeShiftL` 24)
        .|. (fromIntegral (BS.index bs (startIx + 4)) `unsafeShiftL` 32)
        .|. (fromIntegral (BS.index bs (startIx + 5)) `unsafeShiftL` 40)
        .|. (fromIntegral (BS.index bs (startIx + 6)) `unsafeShiftL` 48)
        .|. (fromIntegral (BS.index bs (startIx + 7)) `unsafeShiftL` 56)
    -- We manually specialize the big-endian cases: see Note [Manual specialization] for why.
    goBE :: Integer -> Int -> Int -> Int -> Integer
    goBE acc limit shift ix
      | ix >= (limit + 7) =
          let digitGroup = read64BE ix
              newShift = shift + 64
              newIx = ix - 8
           in if digitGroup == 0
                then goBE acc limit newShift newIx
                else goBE (acc + fromIntegral digitGroup `unsafeShiftL` shift) limit newShift newIx
      | otherwise = finishBE acc limit shift ix
    finishBE :: Integer -> Int -> Int -> Int -> Integer
    finishBE acc limit shift ix
      | ix < limit = acc
      | otherwise =
          let digit = BS.index bs ix
              newShift = shift + 8
              newIx = ix - 1
           in if digit == 0
                then finishBE acc limit newShift newIx
                else finishBE (acc + fromIntegral digit `unsafeShiftL` shift) limit newShift newIx
    read64BE :: Int -> Word64
    read64BE endIx =
      fromIntegral (BS.index bs endIx)
        .|. (fromIntegral (BS.index bs (endIx - 1)) `unsafeShiftL` 8)
        .|. (fromIntegral (BS.index bs (endIx - 2)) `unsafeShiftL` 16)
        .|. (fromIntegral (BS.index bs (endIx - 3)) `unsafeShiftL` 24)
        .|. (fromIntegral (BS.index bs (endIx - 4)) `unsafeShiftL` 32)
        .|. (fromIntegral (BS.index bs (endIx - 5)) `unsafeShiftL` 40)
        .|. (fromIntegral (BS.index bs (endIx - 6)) `unsafeShiftL` 48)
        .|. (fromIntegral (BS.index bs (endIx - 7)) `unsafeShiftL` 56)

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
Both integerToByteString and byteStringToInteger effectively function as loops
over digits (and thus, individual bytes), which either have to be read or
extracted. In particular, this involves trafficking data between memory and
machine registers (both ByteString and Integer are wrappers around counted
arrays), as well as the overhead of looping (involving comparisons and branches).

However, on all architectures of interest (essentially, 64-bit Tier 1),
general-purpose registers (GPRs henceforth) are 64 bits (or 8 bytes).
Furthermore, the primary cost of moving data between memory and registers is
having to overcome the 'memory wall': the exact amount of data being moved
doesn't affect this very much. In addition to this, when we operate on single
bytes, the remaining 56 bits of the GPR holding that data are essentially
'wasted'. In the situation we have (namely, operating over arrays, whose data
is adjacent in memory), we thus get two sources of inefficiency:

* Despite paying the cost for a memory transfer, we transfer only one-eighth
  the data we could; and
* Despite transferring data from memory to registers, we utilize the register
  at only one-eighth capacity.

This essentially means we perform eight times _more_ rotations of the loop
than we need to!

To avoid this inefficiency, we use a technique known as _loop sectioning_.
Effectively, this turns our homogenous loop (that always operates one byte at
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

{- Note [fromIntegral and padding arguments]

As described in Note [How to add a built-in function: simple cases], we should
not normally use a function like fromIntegral to convert arguments into more
amenable forms, as it runs the risk of truncation. In the case of the padding
argument given to integerToByteString (which is an Int) as opposed to how the
builtin it implements is called (which passes an Integer), we use fromIntegral
in spite of this. This is for two reasons: we are more-or-less forced to do so
anyway (for reasons of efficiency if nothing else), and even if truncation
does occur, we have much bigger issues. We elaborate on these points in this note.

It is a fact that ByteString lengths are measured as Ints: while there are good
reasons to disagree with this policy, it is forced on us, and can't really be
changed. Furthermore, certain auxilliary tools we use to define
integerToByteString (specifically, Builder) also uses Int to track its
allocation size. As part of integerToByteString, we are in some cases required
to compare one, or both, of these against the padding argument, possibly as
often as once _per digit_. If we wanted to avoid fromIntegral, we would have
to promote either the length of a ByteString, or the size of a Builder, to
Integer, each time, only to then throw that value away. This would create
unacceptable inefficiencies, not only due to the needless allocations (which
would actually exceed the size of what is being generated by the function, as
each Integer costs a minimum of _four_ machine words!), but also because
Integer equality is far costlier (and far harder to optimize out) than Int
equality. As an alternative, we could 'demote' the padding argument to an Int,
but the only way we can do this is by using fromIntegral: this means that we
have to do it _somewhere_, and the only real difference is location. By
placing this conversion in a wrapper, we reduce the work the implementation
has to do, and avoid cluttering it with yet more code.

Furthermore, if truncation _would_ occur, then we have much bigger problems.
On all supported platforms (which all use 64-bit Int representations),
truncation in the padding argument would require passing an argument that is
either larger than 2^62 - 1, or smaller than 2^63 - 1. In the first case,
the cost of allocating something even half of that size would blow through any
and all execution and memory limits long before anyone could even realize that
the result they received is shorter than what they requested; in the second
case, it wouldn't matter anyway, as no number that could reasonably fit on-chain
would even come close to requiring such a number of digits at a minimum. In any
reasonable situation, the padding argument would be much, _much_ smaller than
any Int, and in cases where it isn't, the rest of the system prevents anything
untoward being noticed.

On the basis of both of these, we consider that this truncating conversion is
completely safe, and sensible.
-}
