-- | Benchmarks for string builtins.  Remember that "strings" are actually Text.
module Benchmarks.Strings (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.Text qualified as T
import System.Random (StdGen)

{- Plutus strings are implemented as Text objects.  Since text-2.x, Text uses
 UTF-8 encoding internally (text-1.x used UTF-16).  Each Unicode codepoint
 requires 1-4 bytes in UTF-8 depending on its plane.

 All Text benchmarks use 4-byte-only characters (the worst case for costing).
 With 4-byte chars, @ceil(bytes\/4) = char_count@ exactly, so the same fitted
 parameters work for both char-count sizing (A/B/C) and byte-length sizing
 (D/E).  The only runtime difference is how the CEK machine measures text size:
 O(n) character traversal (A/B/C) vs O(1) byte-length lookup (D/E).

 For simpler characters (like ASCII), the byte-based measure naturally gives a
 smaller size (@ceil(1*chars\/4)@ instead of @chars@), so they get charged less,
 which correctly reflects that there is less actual work.
-}

{- Note [Unicode encodings and Data.Text] Unicode characters are organised into
17 'planes', each containing 65536 'codepoints'.  Only some of the codepoints in
each plane represent actual characters: some code points are permanently
unavailable, some are used for non-printing operations like forming ligatures or
adding accents, and some are used for other administrative purposes.  To
complicate matters, an actual rendered character (grapheme) may be constructed
from multiple codepoints, but that shouldn't concern us here.

Plane 0 is called the Basic Multilingual Plane (BMP) and contains most commonly
used characters from most human languages.

Since text-2.x, Text is internally a UTF-8 encoded byte array.  UTF-8 uses 1
to 4 bytes per codepoint: ASCII (0x00-0x7F) requires 1 byte, Latin/Cyrillic
etc. require 2 bytes, the rest of the BMP 3 bytes, and supplementary planes 4
bytes.  Data.Text.length reports the number of codepoints, which requires a
full traversal since UTF-8 is variable-width.  The raw byte length is available
in O(1) via the internal array length.

We provide builtins for the encodeUtf8 and decodeUtf8 functions, which convert
Text objects to UTF-8 encoded ByteStrings and back.

In practice we'll probably mostly encounter ASCII strings (which are cheap to
process and encode), but for costing purposes we have to consider the most
expensive operations.  Thus we benchmark 'encodeUtf8' with inputs produced by
Hedgehog's 'unicode' generator, which produces characters uniformly distributed
across all planes.  With the 'ascii' generator a Text string of n characters
requires exactly n bytes; with 'unicode' the average is about 2.7 bytes per
character.
-}

{- Note [Choosing the inputs for costing benchmarks].  We carried out some
   preliminary benchmarking to determine the execution times for encodeUtf8 and
   decodeUtf8 with different kinds of input to check which gave the worst case,
   and we use the worst-case inputs for the costing benchmarks above.

   encodeUtf8: we looked at two different types of input generated with
   Hedgehog's 'text' generator:

     (A) inputs using the 'ascii' generator for characters: n characters
         requiring n bytes in UTF-8 (1 byte per character).

     (B) inputs using the 'unicode' generator for characters: n characters
         requiring ~2.7n bytes in UTF-8 on average (mix of 1-4 byte encodings).

   Encoding inputs of both types is linear in the size of the input, but type B
   takes 2.5-3 times as long as inputs of type A, so we use B as the benchmark
   inputs to cover the worst case.  The strings we're likely to see in practice
   will be of type A, so we'll overestimate the cost of encoding them.

   decodeUtf8: similarly to encodeUtf8, we looked at two different types of
   UTF-8 encoded inputs generated with the 'utf8' generator, each requiring 8n
   bytes (ie size n in words):

     (A) inputs generated with the 'ascii' generator for characters: these
         contain 8n characters (each encoded using one byte).

     (B) inputs generated with the 'unicode' generator for characters: these
         contain ~2n characters (mostly encoded using 3-4 bytes).

   Decoding both types of input was linear in the size of the input, but inputs
   of type B took about 3.5 times as long as type A (despite the fact that
   inputs of type A contain 4 times as many characters as B), so we use inputs
   of type B for the costing benchmarks.

   For the other string functions (appendString and equalsString) the time taken
   depended only on the size of the input, with the contents not mattering.
   AppendString was linear in the sum of the input sizes (except that it was
   anomalously fast when one of the inputs was empty, presumably because the
   underlying Haskell function has to do less work in this case) and
   equalsString (applied to strings with identical contents) was linear in the
   input size.
-}

oneArgumentSizes :: [Integer]
oneArgumentSizes = [0, 200 .. 20000] -- 101 entries

twoArgumentSizes :: [Integer]
twoArgumentSizes = [0, 500 .. 10000] -- 21 entries

{- This is for benchmarking DecodeUtf8.  That fails if the encoded data is
   invalid, so we make sure that the input data is valid data for it by using
   data produced by G.utf8 (see above). -}
benchOneUtf8ByteString :: DefaultFun -> Benchmark
benchOneUtf8ByteString name =
  createOneTermBuiltinBench name [] $ makeSizedUtf8ByteStrings seedA oneArgumentSizes

benchOneTextString :: DefaultFun -> Benchmark
benchOneTextString name =
  createOneTermBuiltinBench name [] $ makeSized4ByteTextStrings seedA oneArgumentSizes

benchTwoTextStrings :: DefaultFun -> Benchmark
benchTwoTextStrings name =
  let s1 = makeSized4ByteTextStrings seedA twoArgumentSizes
      s2 = makeSized4ByteTextStrings seedB twoArgumentSizes
   in createTwoTermBuiltinBench name [] s1 s2

-- Benchmark times for a function applied to equal arguments.  This is used for
-- benchmarking EqualsString on the diagonal.  Copy the string here, because
-- otherwise it'll be exactly the same and the equality will short-circuit.
benchSameTwoTextStrings :: DefaultFun -> Benchmark
benchSameTwoTextStrings name =
  createTwoTermBuiltinBenchElementwise name [] $ pairWith T.copy inputs
  where
    inputs = makeSized4ByteTextStrings seedA oneArgumentSizes

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =
  [ benchOneTextString EncodeUtf8
  , benchOneUtf8ByteString DecodeUtf8
  , benchTwoTextStrings AppendString
  , benchSameTwoTextStrings EqualsString
  ]
