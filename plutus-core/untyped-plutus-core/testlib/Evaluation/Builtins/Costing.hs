-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-dodgy-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Evaluation.Builtins.Costing where

import PlutusCore
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Generators.QuickCheck.Builtin (magnitudesPositive)
import PlutusCore.Generators.QuickCheck.Utils

import Data.Bifunctor
import Data.Int
import Data.List
import Data.Maybe
import Data.SatInt
import Test.QuickCheck.Gen
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Some (..))

deriving newtype instance Foldable NonEmptyList -- QuickCheck...

{-| Direct equality of two 'CostStream's. Same as @deriving stock Eq@. We don't want to do the
latter, because the semantics of a 'CostStream' are those of the sum of its elements and the
derived 'Eq' instance would conflict with that. -}
eqCostStream :: CostStream -> CostStream -> Bool
eqCostStream (CostLast cost1) (CostLast cost2) = cost1 == cost2
eqCostStream (CostCons cost1 costs1) (CostCons cost2 costs2) =
  cost1 == cost2 && eqCostStream costs1 costs2
eqCostStream _ _ = False

fromCostList :: NonEmptyList CostingInteger -> CostStream
fromCostList (NonEmpty []) = error "Panic: an empty non-empty list"
fromCostList (NonEmpty (cost0 : costs0)) = go cost0 costs0
  where
    go cost [] = CostLast cost
    go cost (cost' : costs) = CostCons cost $ go cost' costs

toCostList :: CostStream -> NonEmptyList CostingInteger
toCostList = NonEmpty . go
  where
    go (CostLast cost) = [cost]
    go (CostCons cost costs) = cost : go costs

toExBudgetList :: ExBudgetStream -> NonEmptyList ExBudget
toExBudgetList = NonEmpty . go
  where
    go (ExBudgetLast budget) = [budget]
    go (ExBudgetCons budget budgets) = budget : go budgets

-- | A list of ranges: @(0, 0), (1, 10) : (11, 100) : (101, 1000) : ... : [(10^18, maxBound)]@.
magnitudes :: [(SatInt, SatInt)]
magnitudes =
  map (bimap fromInteger fromInteger)
    . ((0, 0) :)
    . magnitudesPositive (* 10)
    $ fromSatInt (maxBound :: SatInt)

{-| Return the range (in the sense of 'magnitudes') in which the given 'SatInt' belongs. E.g.

>>> toRange 42
(11,100)
>>> toRange 1234
(1001,10000) -}
toRange :: SatInt -> (SatInt, SatInt)
toRange cost =
  fromMaybe (error $ "Panic: an unexpected cost: " ++ show cost) $
    find ((>= cost) . snd) magnitudes

-- | Generate a 'SatInt' in the given range.
chooseSatInt :: (SatInt, SatInt) -> Gen SatInt
chooseSatInt = fmap unsafeToSatInt . choose . bimap unSatInt unSatInt

{-| Generate asymptotically bigger 'SatInt's with exponentially lower chance. This is in order to
make the generator of 'CostStream' produce streams whose sums are more or less evenly distributed
across 'magnitudes'. -}
instance Arbitrary SatInt where
  arbitrary = frequency . zip freqs . reverse $ map chooseSatInt magnitudes
    where
      freqs = map floor $ iterate (* 1.3) (2 :: Double)

  -- See Note [QuickCheck and integral types].
  shrink = map fromIntegral . shrink @Int64 . fromSatInt

instance Arbitrary CostStream where
  arbitrary =
    frequency
      [ -- Single-element streams an important enough corner-case to justify tilting the
        -- generator.
        (1, CostLast <$> arbitrary)
      , (6, fromCostList <$> arbitrary)
      ]

  shrink (CostLast cost) = map CostLast $ shrink cost
  shrink (CostCons cost costs) =
    CostLast cost : costs : do
      -- Shrinking the recursive part first.
      (costs', cost') <- shrink (costs, cost)
      pure $ CostCons cost' costs'

instance CoArbitrary SatInt where
  -- See Note [QuickCheck and integral types]. No idea what kind of coverages we get here though.
  coarbitrary = coarbitrary . fromSatInt @Int64

instance Function SatInt where
  -- See Note [QuickCheck and integral types]. No idea what kind of coverages we get here though.
  function = functionMap fromSatInt $ fromIntegral @Int64

-- | Same as '(===)' except accepts a custom equality checking function.
checkEqualsVia :: Show a => (a -> a -> Bool) -> a -> a -> Property
checkEqualsVia eq x y =
  counterexample (show x ++ interpret res ++ show y) res
  where
    res = eq x y
    interpret True = " === "
    interpret False = " =/= "

-- | A value to use in tests to make sure what's not supposed to be forced isn't forced.
bottom :: a
bottom = error "this value wasn't supposed to be forced"

-- | Test that 'magnitudes' has the correct bounds.
test_magnitudes :: TestTree
test_magnitudes =
  testProperty "magnitudes" $
    let check (0, 0) (1, 10) = True
        check (_, hi1) (lo2, hi2) = hi1 + 1 == lo2 && hi1 * 10 == hi2
     in and
          [ fst (head magnitudes) == 0
          , snd (last magnitudes) == maxBound
          , and . zipWith check magnitudes $ tail magnitudes
          ]

-- | Show the distribution of generated 'CostStream's as a diagnostic.
test_CostStreamDistribution :: TestTree
test_CostStreamDistribution =
  testProperty "distribution of the generated CostStream values" . withMaxSuccess 10000 $
    \costs ->
      let costsSum = sumCostStream costs
          (low, high) = toRange costsSum
       in label (show low ++ " - " ++ show high) True

-- | Test that @fromCostList . toCostList@ is identity.
test_toCostListRoundtrip :: TestTree
test_toCostListRoundtrip =
  testProperty "fromCostList cancels toCostList" . withMaxSuccess 5000 $ \costs ->
    checkEqualsVia
      eqCostStream
      (fromCostList $ toCostList costs)
      costs

-- | Test that @toCostList . fromCostList@ is identity.
test_fromCostListRoundtrip :: TestTree
test_fromCostListRoundtrip =
  testProperty "toCostList cancels fromCostList" . withMaxSuccess 5000 $ \costs ->
    toCostList (fromCostList costs)
      === costs

-- | Test that @uncurry reconsCost . unconsCost@ is identity.
test_unconsCostRoundtrip :: TestTree
test_unconsCostRoundtrip =
  testProperty "reconsCost cancels unconsCost" . withMaxSuccess 5000 $ \costs ->
    checkEqualsVia
      eqCostStream
      (uncurry reconsCost $ unconsCost costs)
      costs

-- | Test that 'sumCostStream' returns the sum of the elements of a 'CostStream'.
test_sumCostStreamIsSum :: TestTree
test_sumCostStreamIsSum =
  testProperty "sumCostStream is sum" . withMaxSuccess 5000 $ \costs ->
    sumCostStream costs
      === sum (toCostList costs)

-- | Test that 'mapCostStream' applies a function to each element of a 'CostStream'.
test_mapCostStreamIsMap :: TestTree
test_mapCostStreamIsMap =
  testProperty "mapCostStream is map" . withMaxSuccess 500 $ \(Fun _ f) costs ->
    checkEqualsVia
      eqCostStream
      (mapCostStream f $ fromCostList costs)
      (fromCostList $ fmap f costs)

{-| Test that the sum of a stream returned by 'addCostStream' equals the sum of the sums of its two
arguments. -}
test_addCostStreamIsAdd :: TestTree
test_addCostStreamIsAdd =
  testProperty "addCostStream is add" . withMaxSuccess 5000 $ \costs1 costs2 ->
    sumCostStream (addCostStream costs1 costs2)
      === sumCostStream costs1
        + sumCostStream costs2

{-| Test that the sum of a stream returned by 'minCostStream' equals the minimum of the sums of its
two arguments. -}
test_minCostStreamIsMin :: TestTree
test_minCostStreamIsMin =
  testProperty "minCostStream is min" . withMaxSuccess 5000 $ \costs1 costs2 ->
    sumCostStream (minCostStream costs1 costs2)
      === min (sumCostStream costs1) (sumCostStream costs2)

{-| Test that the sum of a stream returned by 'zipCostStream' equals an 'ExBudget' containing the
sums of its two arguments. -}
test_zipCostStreamIsZip :: TestTree
test_zipCostStreamIsZip =
  testProperty "zipCostStream is zip" . withMaxSuccess 5000 $ \costs1 costs2 ->
    sumExBudgetStream (zipCostStream costs1 costs2)
      === ExBudget (ExCPU $ sumCostStream costs1) (ExMemory $ sumCostStream costs2)

-- | Test that 'mapCostStream' preserves the length of the stream.
test_mapCostStreamReasonableLength :: TestTree
test_mapCostStreamReasonableLength =
  testProperty "mapCostStream: reasonable length" . withMaxSuccess 500 $ \(Fun _ f) costs ->
    length (toCostList (mapCostStream f costs))
      === length (toCostList costs)

{-| Test that the length of the stream returned by 'addCostStream' equals the sum of the lengths of
its two arguments. -}
test_addCostStreamReasonableLength :: TestTree
test_addCostStreamReasonableLength =
  testProperty "addCostStream: reasonable length " . withMaxSuccess 5000 $ \costs1 costs2 ->
    max 2 (length (toCostList (addCostStream costs1 costs2)))
      === length (toCostList costs1)
        + length (toCostList costs2)

{-| Test that the length of the stream returned by 'addCostStream' is

1. greater than or equal to the minimum of the lengths of its two arguments
2. smaller than or equal to the sum of the lengths of its two arguments. -}
test_minCostStreamReasonableLength :: TestTree
test_minCostStreamReasonableLength =
  testProperty "minCostStream: reasonable length " . withMaxSuccess 5000 $ \costs1 costs2 ->
    let len1 = length $ toCostList costs1
        len2 = length $ toCostList costs2
        lenMin = length . toCostList $ minCostStream costs1 costs2
     in lenMin >= min len1 len2 && lenMin <= len1 + len2

{-| Test that the length of the stream returned by 'zipCostStream' equals the maximum of the
lengths of its two arguments. -}
test_zipCostStreamReasonableLength :: TestTree
test_zipCostStreamReasonableLength =
  testProperty "zipCostStream: reasonable length " . withMaxSuccess 5000 $ \costs1 costs2 ->
    length (toExBudgetList (zipCostStream costs1 costs2))
      === max (length (toCostList costs1)) (length (toCostList costs2))

-- | Test that 'mapCostStream' preserves the laziness of its argument.
test_mapCostStreamHandlesBottom :: TestTree
test_mapCostStreamHandlesBottom =
  testProperty "mapCostStream handles bottom suffixes" . withMaxSuccess 500 $ \(Fun _ f) xs ->
    let n = length xs
        -- 'fromCostList' forces an additional element, so we account for that here.
        suff = 0 : bottom
        costs = fromCostList . NonEmpty $ xs ++ suff
     in length (take n . getNonEmpty . toCostList $ mapCostStream f costs) === n

-- | Test that 'mapCostStream' preserves the laziness of its two arguments.
test_addCostStreamHandlesBottom :: TestTree
test_addCostStreamHandlesBottom =
  testProperty "addCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \(Positive n) ->
    let interleave xs ys = concat $ transpose [xs, ys]
        zeroToN = map (unsafeToSatInt . fromIntegral) [0 .. n] ++ bottom
        nPlus1To2NPlus1 = map (unsafeToSatInt . fromIntegral) [n + 1 .. n * 2 + 1] ++ bottom
        taken =
          take n . getNonEmpty . toCostList $
            addCostStream
              (fromCostList $ NonEmpty zeroToN)
              (fromCostList $ NonEmpty nPlus1To2NPlus1)
     in -- Every element in the resulting stream comes from one of the generated lists.
        all (\cost -> cost `elem` interleave zeroToN nPlus1To2NPlus1) taken
          .&&.
          -- No element is duplicated.
          length (map head . group $ sort taken)
            === length taken

-- | Test that 'minCostStream' preserves the laziness of its two arguments.
test_minCostStreamHandlesBottom :: TestTree
test_minCostStreamHandlesBottom =
  testProperty "minCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \xs ys ->
    let m = min (sum xs) (sum ys)
        -- 'minCostStream' can force only a single extra element of the stream.
        suff = 0 : bottom
        xsYsMin =
          minCostStream
            (fromCostList . NonEmpty $ xs ++ suff)
            (fromCostList . NonEmpty $ ys ++ suff)
     in -- Rolling '(+)' over a list representing the minimum of two streams eventually
        -- gives us the sum of the minimum stream before triggering any of the bottoms.
        elem m . scanl' (+) 0 . getNonEmpty $ toCostList xsYsMin

{-| Pad the shortest of the given lists by appending the given element to it until the length of
the result matches the length of the other list.

>>> postAlignWith 'a' "bcd" "e"
("bcd","eaa")
>>> postAlignWith 'a' "b" "cdef"
("baaa","cdef") -}
postAlignWith :: a -> [a] -> [a] -> ([a], [a])
postAlignWith z xs ys = (align xs, align ys)
  where
    align zs = take (length xs `max` length ys) $ zs ++ repeat z

-- | Test that 'zipCostStream' preserves the laziness of its two arguments.
test_zipCostStreamHandlesBottom :: TestTree
test_zipCostStreamHandlesBottom =
  testProperty "zipCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \xs ys ->
    let z = ExBudget (ExCPU $ sum xs) (ExMemory $ sum ys)
        (xsA, ysA) = postAlignWith 0 xs ys
        -- 'fromCostList' forces an additional element, so we account for that here.
        suff = 0 : bottom
        xys =
          zipCostStream
            (fromCostList . NonEmpty $ xsA ++ suff)
            (fromCostList . NonEmpty $ ysA ++ suff)
     in -- Rolling '(<>)' over a list representing the zipped cost streams eventually
        -- gives us an 'ExBudget' containing the sums of the streams computed separately.
        elem z . scanl' (<>) mempty . getNonEmpty $ toExBudgetList xys

-- | The size 'sierpinskiRose' of the given depth.
sierpinskiSize :: Int -> Int
sierpinskiSize n
  | n <= 1 = 1
  | otherwise = sierpinskiSize (n - 1) * 3 + 1

{-| Return a finite balanced tree with each node (apart from the leaves) having exactly 3 children.
The parameter is the depth of the tree.
Named after https://en.wikipedia.org/wiki/Sierpi%C5%84ski_triangle -}
sierpinskiRose :: Int -> CostRose
sierpinskiRose n0
  | n0 <= 1 = singletonRose 1
  | otherwise = CostRose (fromIntegral n0) . map sierpinskiRose . replicate 3 $ n0 - 1

{-| Traverse a 'sierpinskiRose' of the given depth and display the total amount of elements
processed. See 'test_flattenCostRoseIsLinear' for why we do this. -}
test_flattenCostRoseIsLinearForSierpinskiRose :: Int -> TestTree
test_flattenCostRoseIsLinearForSierpinskiRose depth =
  let size = sierpinskiSize depth
   in testProperty ("sierpinski rose: taking " ++ show size ++ " elements") $
        withMaxSuccess 1 $
          length (toCostList . flattenCostRose $ sierpinskiRose depth)
            === size

{-| Test that traversing a larger 'CostRose' takes _linearly_ more time. The actual test can only
be done with eyes unfortunately, because the tests are way too noisy for evaluation times to be
reported even remotely accurately. -}
test_flattenCostRoseIsLinear :: TestTree
test_flattenCostRoseIsLinear =
  testGroup
    "flattenCostRose is linear"
    [ test_flattenCostRoseIsLinearForSierpinskiRose 12
    , test_flattenCostRoseIsLinearForSierpinskiRose 13
    , test_flattenCostRoseIsLinearForSierpinskiRose 14
    ]

{- Note [Generating a CostRose]
We use an overly pedantic approach for generating 'CostRose's. The idea is simple: generate a list
of costs, chop it into chunks and turn each of those into its own 'CostRose' recursively, then
assemble them together to get the resulting 'CostRose'. We do it this way, because that makes it
trivial to ensure that the generator is not exponential as each generated 'CostRose' only has those
(and only those) elements in it that came from the generated list and the generator for lists isn't
exponential. It also makes it easy to control the distribution of the shapes of generated
'CostRose's. Do we want long forests? Do we want to cover all possible trees up to a certain depth?
All of that is easy to tweak, although the actual logic can get complicated pretty quickly. But at
least all this complicated logic is fairly local unlike with the usual approach when generation is
size-driven and minor tweaks in size handling at any step can result in major changes in the overall
generation strategy such as exponential growth of the generated objects.
-}

-- See Note [Generating a CostRose].
{-| Generate a 'CostRose' from the given list by splitting the list into sublists and generating
a 'CostRose' for each of them recursively. -}
genCostRose :: NonEmptyList SatInt -> Gen CostRose
genCostRose (NonEmpty []) = error "Panic: an empty non-empty list"
genCostRose (NonEmpty (cost : costs)) =
  CostRose cost <$> (traverse genCostRose =<< multiSplit1 costs)

fromCostRose :: CostRose -> NonEmptyList SatInt
fromCostRose (CostRose cost costs) =
  NonEmpty $ cost : concatMap (getNonEmpty . fromCostRose) costs

instance Arbitrary CostRose where
  -- By default the lengt of generated lists is capped at 100, which would give us too small of
  -- 'CostRose's, so we scale the size parameter.
  arbitrary = scale (* 10) arbitrary >>= genCostRose

  shrink (CostRose cost costs) = do
    -- Shrinking the recursive part first.
    (costs', cost') <- shrink (costs, cost)
    pure $ CostRose cost' costs'

-- | Return the lengths of all the forests in a 'CostRose'.
collectListLengths :: CostRose -> [Int]
collectListLengths (CostRose _ costs) = length costs : concatMap collectListLengths costs

-- | Show the distribution of forest lengths in generated 'CostRose' values as a diagnostic.
test_CostRoseListLengthsDistribution :: TestTree
test_CostRoseListLengthsDistribution =
  testProperty "distribution of list lengths in CostRose values" $
    withMaxSuccess 1000 $ \rose ->
      let render n
            | n <= 10 = show n
            | otherwise = show m ++ " < n <= " ++ show (m + 10)
            where
              m = head $ dropWhile (< n) [10, 20 ..]
       in tabulate "n" (map render . filter (/= 0) $ collectListLengths rose) True

-- | Test that 'genCostRose' only takes costs from its argument when generating a 'CostRose'.
test_genCostRoseSound :: TestTree
test_genCostRoseSound =
  testProperty "genCostRose puts 100% of its input and nothing else into the output" $
    withMaxSuccess 1000 $ \costs ->
      forAll (genCostRose costs) $ \rose ->
        fromCostRose rose
          === costs

-- | Test that 'flattenCostRose' returns the elements of its argument.
test_flattenCostRoseSound :: TestTree
test_flattenCostRoseSound =
  testProperty "flattenCostRose puts 100% of its input and nothing else into the output" $
    withMaxSuccess 1000 $ \rose ->
      -- This assumes that 'flattenCostRose' is left-biased, which isn't really necessary, but
      -- it doesn't seem like we're giving up on the assumption any time soon anyway, so why
      -- not keep it simple instead of sorting the results.
      checkEqualsVia
        eqCostStream
        (flattenCostRose rose)
        (fromCostList $ fromCostRose rose)

-- | Test that 'flattenCostRose' is lazy.
test_flattenCostRoseHandlesBottom :: TestTree
test_flattenCostRoseHandlesBottom =
  testProperty "flattenCostRose handles bottom subtrees" . withMaxSuccess 5000 $ \xs ys ->
    -- Create a 'CostRose' with a negative cost somewhere in it, then replace the subtree after
    -- that cost with 'bottom' and check that we can get to the negative cost without forcing
    -- the bottom. We could've implemented generation of 'CostRose's with bottoms in them, but
    -- 'genCostRose' is already complicated enough, so it's easier to put a magical number into
    -- its input and postprocess the generated rose.
    forAll (genCostRose . NonEmpty $ xs ++ (-1) : ys) $ \rose ->
      let spoilCostRose (CostRose cost forest) =
            CostRose cost $
              if cost == -1
                -- 'flattenCostRose' forces an additional constructor, which is why 'bottom'
                -- is put into a list.
                then [bottom]
                else map spoilCostRose forest
       in elem (-1) . toCostList . flattenCostRose $ spoilCostRose rose

{-| Test that 'memoryUsage' called over a value of a built-in type never returns a stream
containing a negative cost. -}
test_costsAreNeverNegative :: TestTree
test_costsAreNeverNegative =
  testProperty "costs coming from 'memoryUsage' are never negative" $
    withMaxSuccess 1000 $ \(val :: Some (ValueOf DefaultUni)) ->
      all (>= 0) . toCostList . flattenCostRose $ memoryUsage val

test_costing :: TestTree
test_costing =
  testGroup
    "costing"
    [ test_magnitudes
    , test_CostStreamDistribution
    , test_toCostListRoundtrip
    , test_fromCostListRoundtrip
    , test_unconsCostRoundtrip
    , test_sumCostStreamIsSum
    , test_mapCostStreamIsMap
    , test_addCostStreamIsAdd
    , test_minCostStreamIsMin
    , test_zipCostStreamIsZip
    , test_mapCostStreamReasonableLength
    , test_addCostStreamReasonableLength
    , test_minCostStreamReasonableLength
    , test_zipCostStreamReasonableLength
    , test_mapCostStreamHandlesBottom
    , test_addCostStreamHandlesBottom
    , test_minCostStreamHandlesBottom
    , test_zipCostStreamHandlesBottom
    , test_flattenCostRoseIsLinear
    , test_CostRoseListLengthsDistribution
    , test_genCostRoseSound
    , test_flattenCostRoseSound
    , test_flattenCostRoseHandlesBottom
    , test_costsAreNeverNegative
    ]
