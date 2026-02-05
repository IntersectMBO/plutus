-- |  Generators for various types of data for benchmarking built-in functions
module Generators where

import PlutusCore.Data
import PlutusCore.Evaluation.Machine.CostStream (sumCostStream)
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( ExMemoryUsage (..)
  , flattenCostRose
  )

import Control.Monad
import Data.Bits
import Data.ByteString (ByteString)
import Data.Int (Int64)
import Data.List as List (foldl')
import Data.Text (Text)
import Data.Word (Word64)

import Hedgehog qualified as H
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import Hedgehog.Internal.Tree qualified as T
import System.IO.Unsafe (unsafePerformIO)
import System.Random (StdGen, randomR)
import Test.QuickCheck
import Test.QuickCheck.Instances.ByteString ()

{- TODO: we're using Hedgehog for some things, QuickCheck for others, and
   System.Random for others.  We should rationalise this.  Pehaps Hedgehog is
   more future-proof since it can produce random instances of a wide variety of
   types.  On the other hand, you have to be careful with Hedgehog Ranges since
   they don't necessarily do what you might expect.  It might be a bit tricky to
   use Hedgehog everywhere because we'd need a lot of monadic code to take care
   of generator states. -}

---------------- Creating things of a given size ----------------

-- Generate a random n-word (ie, 64n-bit) integer
{- In principle a random 5-word integer (for example) might only occupy 4 or
   fewer words, but we're generating uniformly distributed values so the
   probability of that happening should be at most 1 in 2^64. -}
randNwords :: Int -> StdGen -> (Integer, StdGen)
randNwords n gen = randomR (lb, ub) gen
  where
    lb = -2 ^ (64 * n - 1)
    ub = 2 ^ (64 * n - 1) - 1

-- Generate a random Bool (just here for consistency)
randBool :: StdGen -> (Bool, StdGen)
randBool gen = randomR (False, True) gen

-- Hedgehog generators
seedA :: H.Seed
seedA = H.Seed 42 43

seedB :: H.Seed
seedB = H.Seed 44 45

genSample :: H.Seed -> G.Gen a -> a
genSample seed gen =
  Prelude.maybe
    (Prelude.error "Couldn't create a sample")
    T.treeValue
    $ G.evalGen (H.Size 1) seed gen

-- Given a list [n_1, n_2, ...] create a list [m_1, m_2, ...] where m_i is an n_i-word random
-- integer
makeSizedIntegers :: StdGen -> [Int] -> ([Integer], StdGen)
makeSizedIntegers g [] = ([], g)
makeSizedIntegers g (n : ns) =
  let (m, g1) = randNwords n g
      (ms, g2) = makeSizedIntegers g1 ns
   in (m : ms, g2)

-- Create a bytestring whose memory usage is n.  Since we measure memory usage
-- in 64-bit words we have to create a bytestring containing 8*n bytes.
makeSizedByteString :: H.Seed -> Int -> ByteString
makeSizedByteString seed n = genSample seed (G.bytes (R.singleton (8 * n)))

-- FIXME: this is terrible
makeSizedByteStrings :: H.Seed -> [Int] -> [ByteString]
makeSizedByteStrings seed l = map (makeSizedByteString seed) l

-- TODO: don't use Hedgehog's 'sample' below: it silently resizes the generator
-- to size 30, so listOfByteStringsOfLength and listOfByteStrings are biased
-- towards low byte values.

-- Create a list containing m bytestrings of length n (also terrible)
listOfByteStringsOfLength :: Int -> Int -> [ByteString]
listOfByteStringsOfLength m n =
  unsafePerformIO . G.sample $ G.list (R.singleton m) (G.bytes (R.singleton n))

-- Create a list containing m bytestrings of random lengths
listOfByteStrings :: Int -> [ByteString]
listOfByteStrings m =
  unsafePerformIO . G.sample $ G.list (R.singleton m) (G.bytes (R.linear 0 10000))

---------------- Strings (Hedgehog) ----------------

{- This makes a Text string containing n unicode characters.  We use the unicode
 generator since that mostly produces 4 bytes per character, which is the worst
 case. If we were to use the ascii generator that would give us two bytes per
 character.  See Note [Choosing the inputs for costing benchmarks] in Strings.hs. -}
makeSizedTextString :: H.Seed -> Int -> Text
makeSizedTextString seed n = genSample seed (G.text (R.singleton (2 * n)) G.unicode)

makeSizedTextStrings :: H.Seed -> [Integer] -> [Text]
makeSizedTextStrings seed sizes = fmap (makeSizedTextString seed . fromInteger) sizes

{-| Generate a valid UTF-8 bytestring with memory usage approximately n for
   benchmarking decodeUtf8.  We use the 'unicode' generator beacuse that gives
   the worst-case behaviour: see Note [Choosing the inputs for costing
   benchmarks] in Strings.hs). -}
makeSizedUtf8ByteString :: H.Seed -> Int -> ByteString
makeSizedUtf8ByteString seed n = genSample seed (G.utf8 (R.singleton (2 * n)) G.unicode)

makeSizedUtf8ByteStrings :: H.Seed -> [Integer] -> [ByteString]
makeSizedUtf8ByteStrings seed sizes = (makeSizedUtf8ByteString seed . fromInteger) <$> sizes

---------------- Data (QuickCheck) ----------------

{- Create a large Integer.  QuckCheck doesn't provide this by default (and
 arbitrary :: Gen Integer behaves oddly if you resize it to large values like
 2^62 ("negative size" error ), 2^63 (never terminates), or 2^64 or larger
 (always returns 0).  We need really big integers, so we generate a (signed
 64-bit) Int and list of unsigned Word64 values and make them into an Integer
 using bit operations. This is designed so that arbitraryBigInteger n returns
 integers with memoryUsage equal to n.
 -}
genBigInteger :: Int -> Gen Integer
genBigInteger n = do
  body :: [Word64] <- vectorOf (n - 1) arbitrary
  first :: Int64 <- arbitrary
  pure $ List.foldl' go (fromIntegral first) body
  where
    go :: Integer -> Word64 -> Integer
    go acc w = acc `shiftL` 64 + fromIntegral w

-- | Generate an arbitrary integer of size n (words)
genI :: Int -> Gen Data
genI n = do
  I <$> genBigInteger n

-- | Generate an arbitrary bytestring of size n (words)
genB :: Int -> Gen Data
genB n = do
  let size = 4 * n
  B <$> resize size arbitrary

{-| Generate an arbitrary Data object of depth at most n containing btyrestrings
   with memory usage bmem and integers with memory usage imem.  The `memUsage`
   instance for Data can only return a single number, and we could have for
   example a deep tree containing small bytsetrings/integers which has exactly
   the same memory usage as an object consisting of a single B constructor with
   a very large bytestring.  The costing function for certain operations
   (specifically 'equalsData') would assign the same cost to processing both
   objects even though they have very different structures.  This generator
   allows us to explore a large space of objects to see how the costs of
   operations vary with the size.  For size 5 we generally get trees of depth 3
   and up to 4000 nodes in total (although skewed towards smaller numbers of
   nodes); for size 10 we get trees of depth 4 and up to about 20000 nodes; for
   size 20, depth 5 and up to about one million nodes. -}
genBoundedData :: Int -> Int -> Int -> Gen Data
genBoundedData imem bmem size = genD size
  where
    genD n =
      if n <= 1
        then
          Test.QuickCheck.oneof [genI imem, genB bmem]
        else
          Test.QuickCheck.oneof
            [ Constr <$> choose (1, 100) <*> resize 5 (listOf (genD (n `div` 2)))
            , -- Constr is unilkely to have very many arguments.
              List <$> listOf' (genD (n `div` 2))
            , Map <$> (listOf' $ (,) <$> genD (n `div` 2) <*> genD (n `div` 2))
            ]
      where
        listOf' g =
          frequency
            [ (800, resize 10 (listOf g))
            , (200, resize 100 (listOf g))
            , (2, resize 1000 (listOf g))
            ]

-- We probably will get large lists occasionally in practice,
-- but if we generate them too often we get enormous objects.
-- listOf' attempts to give us very occasional large lists.

{-| Given a list [(n1, (i1, b1, s1)), (n2, (i2, b2, s2)), ...], return a list
 containing n1 samples generated by genBoundedData i1 b1 s1 followed by n2
 samples from genBoundedData i2 b2 s2, and so on. -}
genDataSample :: [(Int, (Int, Int, Int))] -> [Data]
genDataSample l =
  unsafePerformIO $ concat <$> mapM gen1 l
  where
    gen1 (count, (imem, bmem, size)) =
      replicateM count . generate $ genBoundedData imem bmem size

-- A list of parameters for genDataSample
dataParams :: [(Int, (Int, Int, Int))]
dataParams =
  [ (10, (10, 10, 1))
  , (10, (5, 10, 2))
  , (10, (100, 100, 2))
  , (10, (1, 1, 3))
  , (10, (2, 4, 4))
  , (30, (10, 7, 5))
  , (20, (1, 1, 10))
  , (20, (30, 30, 10))
  , (10, (4, 6, 15))
  , (10, (5, 5, 20))
  , (10, (1, 10, 25))
  ] -- 150 entries in all

-- We want a list of random data, but for benchmarking purposes we also want to
-- be able to filter out sublists for various constructors.  To do this we
-- generate a large number of samples and always take some sublist for the
-- inputs to the benchmarks.
dataSample :: [Data]
dataSample = genDataSample (take 500 $ cycle dataParams)

-- A list of data for EqualsData, which is difficult to cost. We want some very
-- small objects in here to give us an idea of what the intercept of regression
-- line should be (but note tht the minimum ExMemoryUsage of a Data object is
-- currently 4, since each node costs that much).  We also exclude really large
-- objects.
dataSampleForEq :: [Data]
dataSampleForEq =
  take 400 . filter (\d -> budgetUsage d < 1000000) . genDataSample . take 1000 $
    cycle ((20, (1, 1, 1)) : dataParams)
  where
    budgetUsage = sumCostStream . flattenCostRose . memoryUsage
