{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Benchmarks.Arrays (makeBenchmarks) where

import Prelude

import Common
import Control.Monad (replicateM, replicateM_)
import Criterion.Main (Benchmark)
import Data.Bits (bit)
import Data.ByteString (ByteString)
import Data.Set qualified as Set
import Data.Traversable (for)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import GHC.Compact (compact, compactAdd, getCompact)
import PlutusCore.Arrays qualified as Arrays
import PlutusCore.Builtin (mkTyBuiltin)
import PlutusCore.Core (Type)
import PlutusCore.Default
  ( DefaultFun (IndexArray, LengthOfArray, ListToArray, MultiIndexArray)
  , DefaultUni
  )
import PlutusCore.Name.Unique (TyName)
import System.Random (mkStdGen, randomRs)
import System.Random.Stateful
  ( StatefulGen
  , StdGen
  , UniformRange (uniformRM)
  , runStateGen_
  , uniformByteStringM
  )

--------------------------------------------------------------------------------
-- Benchmarks ------------------------------------------------------------------

makeBenchmarks :: StdGen -> IO [Benchmark]
makeBenchmarks gen =
  sequence
    [ pure (benchLengthOfArray gen)
    , pure (benchListToArray gen)
    , pure (benchIndexArray gen)
    , benchMultiIndexArray gen
    ]

benchLengthOfArray :: StdGen -> Benchmark
benchLengthOfArray gen =
  createOneTermBuiltinBench LengthOfArray [tyArrayOfBS] listOfArrays
  where
    listOfArrays :: [Vector ByteString] =
      runStateGen_ gen \g -> replicateM 100 do
        arraySize <- uniformRM (1, 100) g
        Vector.replicateM arraySize do
          bsSize <- uniformRM (0, 10_000) g
          uniformByteStringM bsSize g

benchListToArray :: StdGen -> Benchmark
benchListToArray gen =
  createOneTermBuiltinBench ListToArray [tyListOfBS] listOfLists
  where
    listOfLists :: [[ByteString]] =
      runStateGen_ gen \g -> replicateM 100 do
        listSize <- uniformRM (1, 5000) g
        replicateM listSize do
          bsSize <- uniformRM (0, 10_000) g
          uniformByteStringM bsSize g

benchIndexArray :: StdGen -> Benchmark
benchIndexArray gen =
  createTwoTermBuiltinBenchElementwise
    IndexArray
    [tyArrayOfBS]
    (zip arrays idxs)
  where
    (arrays :: [Vector ByteString], idxs :: [Integer]) =
      unzip $ runStateGen_ gen \g -> replicateM 100 do
        arraySize <- uniformRM (1, 100) g
        vec <- Vector.replicateM arraySize do
          bsSize <- uniformRM (0, 10_000) g
          uniformByteStringM bsSize g
        idx <- uniformRM (0, arraySize - 1) g
        pure (vec, fromIntegral idx)

{- The cost of `multiIndexArray` is expected to depend on the number of indices
   (y) and not on the array size (x) or the element size, since each lookup is a
   constant-time read.  The inputs are chosen so that the benchmark data can also
   demonstrate that independence rather than assume it:

   * a full grid of array sizes crossed with index counts, so that x and y vary
     independently; array sizes are log-spaced up to 131072 to cover all cache
     regimes (131072 elements is already at the practical limit of what
     `listToArray` can build within one transaction budget);
   * indices drawn uniformly over the whole array, with replacement -- random
     access is the cache-adversarial pattern;
   * off-grid random points supporting residual diagnostics;
   * two cells with ~1 KiB elements (64 bytes elsewhere) as an empirical check
     that element size does not affect the cost; their index counts are offset
     from the grid values so that benchmark names stay unique.

   See Note [Scattered index lists] for why the index lists are allocated the
   way they are. -}
benchMultiIndexArray :: StdGen -> IO Benchmark
benchMultiIndexArray gen = do
  pairs <- for inputs \(vec, indices, widths) -> (vec,) <$> mkScatteredList widths indices
  pure (createTwoTermBuiltinBenchElementwise MultiIndexArray [tyArrayOfBS] pairs)
  where
    arraySizes :: [Int]
    arraySizes = [1, 8, 64, 512, 4096, 32_768, 131_072]

    -- The top of the range is 'Arrays.maximumIndexCount', so that the model is
    -- fitted over exactly the domain the denotation accepts.
    indexCounts :: [Int]
    indexCounts = [1, 10, 25, 50, 100, 250, 500, 750, Arrays.maximumIndexCount]

    inputs :: [(Vector ByteString, [Integer], [Int])]
    inputs = dedupeOnSizes $ runStateGen_ gen \g -> do
      grid <-
        concat <$> for arraySizes \arraySize -> do
          vec <- mkArray g 64 arraySize
          for indexCounts (fmap (withGaps vec) . mkIndices g arraySize)
      cloud <- replicateM 37 do
        arraySize <- (2 ^) <$> uniformRM (0 :: Int, 17) g
        indexCount <- uniformRM (1, Arrays.maximumIndexCount) g
        vec <- mkArray g 64 arraySize
        withGaps vec <$> mkIndices g arraySize indexCount
      control <- for [999, 1001] \indexCount -> do
        vec <- mkArray g 1024 4096
        withGaps vec <$> mkIndices g 4096 indexCount
      -- A distinct array size, so these get benchmark names of their own.
      spread <- for spreadCounts \indexCount -> do
        vec <- mkArray g 64 2048
        withBudgetGaps vec <$> mkIndices g 2048 indexCount
      pure (grid <> control <> cloud <> spread)

    mkArray :: StatefulGen g m => g -> Int -> Int -> m (Vector ByteString)
    mkArray g maxElemSize arraySize =
      Vector.replicateM arraySize do
        bsSize <- uniformRM (0, maxElemSize) g
        uniformByteStringM bsSize g

    mkIndices :: StatefulGen g m => g -> Int -> Int -> m [Integer]
    mkIndices g arraySize indexCount =
      replicateM indexCount (fromIntegral <$> uniformRM (0, arraySize - 1) g)

    -- Index counts that additionally get the wider spacing described in Note
    -- [Scattered index lists]; the top of the range is among them because the
    -- fit takes the slowest observation at each end.
    spreadCounts :: [Int]
    spreadCounts = [250, 500, Arrays.maximumIndexCount]

    withGaps vec indices = (vec, indices, gapWidths)

    withBudgetGaps vec indices =
      (vec, indices, repeat (max 1 (budgetScatterBytes `div` (length indices * spacerBytes))))

    -- Number of spacer objects per gap.  Varied rather than fixed: a constant
    -- stride is picked up by the hardware prefetcher, which makes a regularly
    -- spaced list measurably faster than an irregularly spaced one.  The mean
    -- is 16, so 4 KiB per gap.
    gapWidths :: [Int]
    gapWidths = randomRs (2, 30) (mkStdGen 7)

-- | Bytes of one spacer object, an integer of 2048 bits plus its header.
spacerBytes :: Int
spacerBytes = 256

{-| Total scatter for the widely spaced inputs, of the order a transaction's
memory budget allows. -}
budgetScatterBytes :: Int
budgetScatterBytes = 100_000_000

{- Note [Scattered index lists]
The time to walk a list depends on where its cons cells sit in memory, not only
on how many there are, and a list built by a plain `replicateM` is allocated
contiguously, which is the favourable end of that range rather than a
representative point.  These lists are therefore built with the cells some way
apart, and by varying amounts, so that the model is fitted to the unfavourable
end.  Most inputs get gaps of about a page; a few, including the largest index
count, get gaps of the width that a whole transaction's memory budget would
allow, because that is what sets the slope.  Without this treatment the
benchmark would measure only the favourable layout, and the model would sit
below what the walk can cost on inputs a script is free to construct.  See
also Note [Index count limitation for multiIndexArray] in PlutusCore.Arrays.

Three implementation details are needed for that layout to hold, and removing
any of them silently returns the benchmark to measuring contiguous lists:

  * the list is built inside a compact region, because the ordinary heap is
    re-laid by every major GC and the layout would not survive;
  * `compactAdd` appends in call order, so the cells and the spacers between
    them are interleaved as written;
  * each gap is filled with several small objects rather than one large one,
    because a large object is given a block of its own and the cells would end
    up adjacent. -}
mkScatteredList :: [Int] -> [Integer] -> IO [Integer]
mkScatteredList gapWidths values = do
  region <- compact ()
  let go _ acc [] = pure acc
      go (width : widths) acc (v : vs) = do
        replicateM_ width (compactAdd region spacer)
        acc' <- getCompact <$> compactAdd region (v : acc)
        go widths acc' vs
      go [] acc _ = pure acc
  go gapWidths [] (reverse values)
  where
    spacer = bit 2048 :: Integer

-- Benchmark names are derived from the argument sizes; drop the rare random
-- point that collides with another point on both sizes.
dedupeOnSizes
  :: [(Vector ByteString, [Integer], [Int])] -> [(Vector ByteString, [Integer], [Int])]
dedupeOnSizes = go Set.empty
  where
    go _ [] = []
    go seen (input@(vec, indices, _) : rest)
      | Set.member key seen = go seen rest
      | otherwise = input : go (Set.insert key seen) rest
      where
        key = (Vector.length vec, length indices)

--------------------------------------------------------------------------------
-- Helpers ---------------------------------------------------------------------

tyArrayOfBS :: Type TyName DefaultUni ()
tyArrayOfBS = mkTyBuiltin @_ @(Vector ByteString) ()

tyListOfBS :: Type TyName DefaultUni ()
tyListOfBS = mkTyBuiltin @_ @[ByteString] ()
