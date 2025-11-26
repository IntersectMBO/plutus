-- | Benchmarks for string builtins.  Remember that "strings" are actually Text.
module Benchmarks.Strings (makeSizedTextStrings, makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.Text qualified as T
import System.Random (StdGen)

{- The memory usage of a string is defined to be four bytes per character.  Plutus
 strings are implemented as Text objects, which are UTF-16 encoded sequences of
 Unicode characters.  For characters (by which Text means codepoints) in the
 Basic Multilingual Plane, UTF-16 requires two bytes, and for other planes four
 bytes (and the actual codepoint for these is obtained by extracting certain
 bits from the two 16-bit parts of the encoding).  The characters we'll
 encounter in practice will probably all be in the BMP (perhaps with the
 exception of emoji), but we still allow one word per character, the number of
 characters being given by 'Data.Text.length'.  For benchmarking it's not
 entirely clear what sort of strings we should provide as input: strings of
 two-byte characters or strings of four-byte characters.  Four-byte characters
 may require some extra processing by certain functions, so we use those as
 input in order to get worst-case behaviour.  This may overestimate costs for
 the strings we encounter in practice.
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

Plutus Strings are implemented as Text objects, which are UTF-16 encoded
sequences of Unicode characters (Text refers to characters, but really means
codepoints).  In UTF-16, characters in the BMP are encoded using two bytes, and
characters from other planes require four bytes (encoded using 'surrogate'
codepoints in the ranges 0xD800-0xDBFF and 0xDC00-0xDFFF, the actual character
being encoded using the lower-order bits).  Text strings internally contain an
Array of 16-byte values, but the length reported by Data.Text.length s is the
number of Unicode characters.  Thus a Text string containing n characters will
require between 2*n and 4*n bytes of memory, the latter case occurring when
every character in s lies outside the BMP (Data.Text.Foreign.lengthWord16 tells
you the number of 16-bit words in the internal representation). Calculating the
character length of a Text string requires traversal of the entire string, so is
O(n).

We provide builtins for the encodeUtf8 and decodeUtf8 functions, which convert
Text objects to UTF-8 encoded Strings and back.  UTF-8 uses 1 to four bytes for
each character: ASCII characters (0x00-0x7F) require one byte, 1920 characters
in various common scripts (Latin-1, Cyrillic, ...) require two bytes, three bytes
are required for everything else in the BMP, and four bytes for codepoints from
the other planes.

In practice we'll probably mostly encounter ASCII strings (which are cheap to
process and encode), but for costing purposes we have to consider the most
expensive operations.  Thus we benchmark 'encodeUtf8' with inputs produced by
Hedgehog's 'unicode' generator, which produces characters uniformly distributed
over the entire set of planes.  Typically, over 9% of the characters generated
by this require four bytes in UTF-8 (and two in UTF-16).  If we use the 'ascii'
generator instead then a Text string of length n requires exactly n bytes,
and if we use 'latin1' then about 3n/2 bytes are required (the characters
in 0x00-0x7F need one byte in UTF-8, those in 0x80-0xFF require two, so the
average number of bytes per character is 3/2).
-}

{- Note [Choosing the inputs for costing benchmarks].  We carried out some
   preliminary benchmarking to determine the execution times for encodeUtf8 and
   decodeUtf8 with different kinds of input to check which gave the worst case,
   and we use the worst-case inputs for the costing benchmarks above.

   encodeUtf8: we looked at two different types of input, both containing n
   64-bit words and generated with Hedgehog's 'text' generator:

     (A) inputs using the 'ascii' generator for characters: these contain 4n
         characters (one 16-bit codepoint per character) and produce a 4n-byte
         UTF-8 output (4n characters, each encoded using 1 byte).

     (B) inputs using the 'unicode' generator for characters: these contain 2n
         characters (the majority (> 98%)requiring 16-bit codepoints per
         character) and produce a UTF-8 output of size about 8n bytes (n words:
         2n characters, mostly encoded using 4 bytes).

   Encoding inputs of both types is linear in the size of the input, but type B
   takes 2.5-3 times as long as inputs of type A, so we use B as the benchmark
   inputs to covert the worst case.  The strings we're likely to see in practice
   will be of type A, so we'll overestimate the cost of encoding them.

   decodeUtf8: similarly to encodeUtf8, we looked at two different types of
   UTF-8 encoded inputs generated with the 'utf8' generator, each requiring 8n
   bytes (ie size n in words):

     (A) inputs generated with the 'ascii' generator for characters: these
         contain 8n characters (each encoded using one byte) and produce a
         UTF-16 output of size 16n bytes (2n words: 8n characters, each encoded
         using one 16-bit codepoint).

     (B) inputs generated with the 'unicode' generator for characters: these
         contain 2n characters (mostly encoded using four bytes) and produce a
         UTF-16 output of size about 8n bytes (n words: 2n characters, each
         encoded using two 16-bit codepoints).

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
oneArgumentSizes = [0, 100 .. 10000] -- 101 entries

twoArgumentSizes :: [Integer]
twoArgumentSizes = [0, 250 .. 5000] -- 21 entries

{- This is for benchmarking DecodeUtf8.  That fails if the encoded data is
   invalid, so we make sure that the input data is valid data for it by using
   data produced by G.utf8 (see above). -}
benchOneUtf8ByteString :: DefaultFun -> Benchmark
benchOneUtf8ByteString name =
  createOneTermBuiltinBench name [] $ makeSizedUtf8ByteStrings seedA oneArgumentSizes

benchOneTextString :: DefaultFun -> Benchmark
benchOneTextString name =
  createOneTermBuiltinBench name [] $ makeSizedTextStrings seedA oneArgumentSizes

benchTwoTextStrings :: DefaultFun -> Benchmark
benchTwoTextStrings name =
  let s1 = makeSizedTextStrings seedA twoArgumentSizes
      s2 = makeSizedTextStrings seedB twoArgumentSizes
   in createTwoTermBuiltinBench name [] s1 s2

-- Benchmark times for a function applied to equal arguments.  This is used for
-- benchmarking EqualsString on the diagonal.  Copy the string here, because
-- otherwise it'll be exactly the same and the equality will short-circuit.
benchSameTwoTextStrings :: DefaultFun -> Benchmark
benchSameTwoTextStrings name =
  createTwoTermBuiltinBenchElementwise name [] $ pairWith T.copy inputs
  where
    inputs = makeSizedTextStrings seedA oneArgumentSizes

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen =
  [ benchOneTextString EncodeUtf8
  , benchOneUtf8ByteString DecodeUtf8
  , benchTwoTextStrings AppendString
  , benchSameTwoTextStrings EqualsString
  ]
