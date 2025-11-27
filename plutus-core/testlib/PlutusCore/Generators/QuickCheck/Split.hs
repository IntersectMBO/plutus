{-# LANGUAGE TypeApplications #-}

module PlutusCore.Generators.QuickCheck.Split where

import Control.Monad
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.List (sortBy)
import Data.Ord (comparing)
import Test.QuickCheck

-- | Up to what length a list is considered \"short\".
smallLength :: Int
smallLength = 6

-- | Generate a sublist of the given size of the given list. Preserves the order of elements.
sublistN :: Int -> [a] -> Gen [a]
sublistN lenRes =
  fmap (map snd . sortBy (comparing fst) . take lenRes)
    . shuffle
    . zip [0 :: Int ..]

-- | Calculate the maximum number of chunks to split a list of the given list into.
toMaxChunkNumber :: Int -> Int
toMaxChunkNumber len
  -- For short lists we take the maximum number of chunks to be the length of the list,
  -- i.e. the maximum number of chunks grows at a maximum speed for short lists.
  | len <= smallLength = len
  -- For longer lists the maximum number of chunks grows slower. We don't really want to split a
  -- 50-element list into each of 1..50 number of chunks.
  | len <= smallLength ^ (2 :: Int) = smallLength + len `div` smallLength
  -- For long lists it grows even slower.
  | otherwise = smallLength + round @Double (sqrt $ fromIntegral len)

{-| Calculate the number of ways to divide a list of length @len@ into @chunkNum@ chunks.
Equals to @C(len - 1, chunksNum - 1)@. -}
toChunkNumber :: Int -> Int -> Int
toChunkNumber len chunkNum =
  product [len - 1, len - 2 .. len - chunkNum + 1]
    `div` product [chunkNum - 1, chunkNum - 2 .. 2]

{-| Return a list of pairs, each of which consists of

1. the frequency at which a chunk length needs to be picked by the generation machinery
2. the chunk length itself

>>> toChunkFrequencies (-1)
[]
>>> toChunkFrequencies 0
[]
>>> toChunkFrequencies 1
[(1,1)]
>>> toChunkFrequencies 5
[(1,1),(4,2),(6,3),(4,4),(1,5)]
>>> toChunkFrequencies 10
[(3,1),(6,2),(9,3),(12,4),(15,5),(18,6),(21,7)]
>>> toChunkFrequencies 50
[(3,1),(4,2),(5,3),(6,4),(7,5),(8,6),(9,7),(10,8),(11,9),(12,10),(13,11),(14,12),(15,13)] -}
toChunkFrequencies :: Int -> [(Int, Int)]
toChunkFrequencies len
  -- For short lists we calculate exact chunk numbers and use those as frequencies in order to get
  -- uniform distribution of list lengths (which does not lead to uniform distribution of lengths
  -- of subtrees, since subtrees with small total count of elements get generated much more often
  -- than those with a big total count of elements, particularly because the latter contain the
  -- former).
  | len <= smallLength = map (\num -> (toChunkNumber len num, num)) chunks
  | otherwise =
      let
        -- The probability of "splitting" a list into a single sublist (i.e. simply 'pure') is
        -- about 3%.
        singleElemProb = 3
        -- Computing @delta@ in order for each subsequent chunk length to get picked a bit more
        -- likely, so that we generate longer forests more often when we can. For not-too-long
        -- lists the frequencies add up to roughly 100. For long lists the sum of frequencies
        -- can be significantly greater than 100 making the chance of generating a single
        -- sublist less than 3%.
        deltaN = chunkMax * (chunkMax - 1) `div` 2
        delta = max 1 $ (100 - chunkMax * singleElemProb) `div` deltaN
       in
        zip (iterate (+ delta) singleElemProb) chunks
  where
    chunkMax = toMaxChunkNumber len
    chunks = [1 .. chunkMax]

{-| Split the given list in chunks. The length of each chunk, apart from the final one, is taken
from the first argument.

>>> toChunks [3, 1] "abcdef"
["abc","d","ef"] -}
toChunks :: [Int] -> [a] -> [[a]]
toChunks [] xs = [xs]
toChunks (n : ns) xs = chunk : toChunks ns xs'
  where
    (chunk, xs') = splitAt n xs

{-| Split a list into the given number of chunks. Concatenating the resulting lists gives back the
original one. Doesn't generate empty chunks. -}
multiSplit1In :: Int -> [a] -> Gen [NonEmptyList a]
multiSplit1In _ [] = pure []
multiSplit1In chunkNum xs = do
  let len = length xs
  -- Pick a list of breakpoints.
  breakpoints <- sublistN (chunkNum - 1) [1 .. len - 1]
  -- Turn the list of breakpoints into a list of chunk lengths.
  let chunkLens = zipWith (-) breakpoints (0 : breakpoints)
  -- Chop the argument into chunks according to the list of chunk lengths.
  pure . coerce $ toChunks chunkLens xs

{-| Split a list into chunks at random. Concatenating the resulting lists gives back the original
one. Doesn't generate empty chunks. -}
multiSplit1 :: [a] -> Gen [NonEmptyList a]
multiSplit1 xs = do
  -- Pick a number of chunks.
  chunkNum <- frequency . map (fmap pure) . toChunkFrequencies $ length xs
  multiSplit1In chunkNum xs

{-| Return the left and the right halves of the given list. The first argument controls whether
the middle element of a list having an odd length goes into the left half or the right one.

>>> halve True [1 :: Int]
([1],[])
>>> halve True [1, 2 :: Int]
([1],[2])
>>> halve True [1, 2, 3 :: Int]
([1,2],[3])
>>> halve False [1 :: Int]
([],[1])
>>> halve False [1, 2 :: Int]
([1],[2])
>>> halve False [1, 2, 3 :: Int]
([1],[2,3]) -}
halve :: Bool -> [a] -> ([a], [a])
halve isOddToLeft xs0 = go xs0 xs0
  where
    go (_ : _ : xsFast) (x : xsSlow) = first (x :) $ go xsFast xsSlow
    go [_] (x : xsSlow) | isOddToLeft = ([x], xsSlow)
    go _ xsSlow = ([], xsSlow)

{-| Insert a value into a list an arbitrary number of times. The first argument controls whether
to allow inserting at the beginning of the list, the second argument is the probability of
inserting an element at the end of the list. -}
insertManyPreferRight :: forall a. Bool -> Double -> a -> [a] -> Gen [a]
insertManyPreferRight keepPrefix lastProb y xs0 = go keepPrefix initWeight xs0
  where
    -- The weight of the "insert @y@ operation" operation at the beginning of the list.
    initWeight = 10
    -- How more likely we're to insert an element when moving one element forward in the list.
    -- Should we make it dependent on the length of the list? Maybe it's fine.
    scaling = 1.1
    -- The weight of the "insert @y@ operation" operation at the end of the list.
    topWeight = scaling ** fromIntegral (length xs0) * initWeight
    -- The weight of the "do nothing" operation.
    noopWeight = floor $ topWeight * (1 / lastProb - 1)

    go :: Bool -> Double -> [a] -> Gen [a]
    go keep weight xs = do
      doCons <- frequency [(floor weight, pure True), (noopWeight, pure False)]
      if doCons
        -- If we don't want to insert elements into the head of the list, then we simply ignore
        -- the generated one and carry on. Ugly, but works.
        then ([y | keep] ++) <$> go keep weight xs
        else case xs of
          [] -> pure []
          x : xs' -> (x :) <$> go True (weight * scaling) xs'

{-| Insert a value into a list an arbitrary number of times. The first argument controls whether
to allow inserting at the end of the list, the second argument is the probability of
inserting an element at the beginning of the list. -}
insertManyPreferLeft :: Bool -> Double -> a -> [a] -> Gen [a]
insertManyPreferLeft keepSuffix headProb y =
  fmap reverse . insertManyPreferRight keepSuffix headProb y . reverse

{-| Insert a value into a list an arbitrary number of times. The first argument is the probability
of inserting an element at an end of the list (i.e. either the beginning or the end, not
combined). See 'multiSplit1' for what this function allows us to do. -}
insertManyPreferEnds :: Double -> a -> [a] -> Gen [a]
-- Cut the list in half, insert into the left half skewing generation towards the beginning, insert
-- into the right half skewing generation towards the end, then append the results of those two
-- operations, so that we get a list where additional elements are more likely to occur close to
-- the sides.
insertManyPreferEnds endProb y xs = do
  -- In order not to get skewed results we sometimes put the middle element of the list into its
  -- first half and sometimes into its second half.
  isOddToLeft <- arbitrary
  let (xsL, xsR) = halve isOddToLeft xs
  -- If the list has even length, then it was cut into two halves of equal length meaning one slot
  -- for to put an element in appears twice: at the end of the left half and at the beginning of
  -- the right one. Hence in order to avoid skeweness we don't put anything into this slot at the
  -- end of the left half.
  -- Maybe we do want to skew generation to favor the middle of the list like we do for its ends,
  -- but then we need to do that intentionally and systematically, not randomly and a little bit.
  xsL' <- insertManyPreferLeft (length xsL /= length xsR) endProb y xsL
  xsR' <- insertManyPreferRight True endProb y xsR
  pure $ xsL' ++ xsR'

{-| Split a list into chunks at random. Concatenating the resulting lists gives back the original
one. Generates empty chunks. The first argument is the probability of generating at least one
empty chunk as the first element of the resulting list. It is also the probability of generating
an empty chunk as the last element of the resulting list. The probability of generating empty
chunks decreases as we go from either of the ends of the resulting list (this is so that we are
more likely to hit a corner case related to handling elements at the beginning or the end of a
list). -}
multiSplit0 :: Double -> [a] -> Gen [[a]]
multiSplit0 endProb = multiSplit1 >=> insertManyPreferEnds endProb [] . coerce
