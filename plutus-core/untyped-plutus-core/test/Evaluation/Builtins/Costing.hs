-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Evaluation.Builtins.Costing where

import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Data.Bifunctor
import Data.Coerce
import Data.Int
import Data.List
import Data.Maybe
import Data.SatInt
import Test.QuickCheck.Gen
import Test.Tasty
import Test.Tasty.QuickCheck

deriving newtype instance Foldable NonEmptyList  -- QuickCheck...

sumExBudgetStream :: ExBudgetStream -> ExBudget
sumExBudgetStream (ExBudgetLast budget)         = budget
sumExBudgetStream (ExBudgetCons budget budgets) = budget <> sumExBudgetStream budgets

eqCostStream :: CostStream -> CostStream -> Bool
eqCostStream (CostLast cost1) (CostLast cost2) = cost1 == cost2
eqCostStream (CostCons cost1 costs1) (CostCons cost2 costs2) =
    cost1 == cost2 && eqCostStream costs1 costs2
eqCostStream _ _ = False

eqExBudgetStream :: ExBudgetStream -> ExBudgetStream -> Bool
eqExBudgetStream (ExBudgetLast budget1) (ExBudgetLast budget2) = budget1 == budget2
eqExBudgetStream (ExBudgetCons budget1 budgets1) (ExBudgetCons budget2 budgets2) =
    budget1 == budget2 && eqExBudgetStream budgets1 budgets2
eqExBudgetStream _ _ = False

fromCostList :: NonEmptyList CostingInteger -> CostStream
fromCostList (NonEmpty [])               = error "cannot be empty"
fromCostList (NonEmpty (cost0 : costs0)) = go cost0 costs0 where
    go cost []              = CostLast cost
    go cost (cost' : costs) = CostCons cost $ go cost' costs

toCostList :: CostStream -> NonEmptyList CostingInteger
toCostList = NonEmpty . go where
    go (CostLast cost)       = [cost]
    go (CostCons cost costs) = cost : go costs

toExBudgetList :: ExBudgetStream -> NonEmptyList ExBudget
toExBudgetList = NonEmpty . go where
    go (ExBudgetLast budget)         = [budget]
    go (ExBudgetCons budget budgets) = budget : go budgets

-- >>> magnitudes
-- [(0,10),(11,100),(101,1000),(1001,10000),(10001,100000),(100001,1000000),(1000001,10000000),(10000001,100000000),(100000001,1000000000),(1000000001,10000000000),(10000000001,100000000000),(100000000001,1000000000000),(1000000000001,10000000000000),(10000000000001,100000000000000),(100000000000001,1000000000000000),(1000000000000001,10000000000000000),(10000000000000001,100000000000000000),(100000000000000001,1000000000000000000),(1000000000000000001,9223372036854775807)]
magnitudes :: [(SatInt, SatInt)]
magnitudes = zipWith (\low high -> (low + 1, high)) borders (tail borders)
  where
    borders :: [SatInt]
    borders = -1 : tail (takeWhile (< maxBound) $ iterate (* 10) 1) ++ [maxBound]

toRange :: SatInt -> (SatInt, SatInt)
toRange cost = fromMaybe (error $ "an unexpected cost: " ++ show cost) $
    find ((>= cost) . snd) magnitudes

chooseSatInt :: (SatInt, SatInt) -> Gen SatInt
chooseSatInt
    = fmap (toSatInt . fromIntegral)
    . chooseInt64
    . bimap (fromIntegral . unSatInt) (fromIntegral . unSatInt)

instance Arbitrary SatInt where
    arbitrary = frequency . zip freqs . reverse $ map chooseSatInt magnitudes where
        freqs = map floor $ iterate (* 1.3) (2 :: Double)
    shrink = map fromIntegral . shrink @Int64 . fromIntegral . unSatInt

instance Arbitrary CostStream where
    arbitrary = frequency
        [ (1, CostLast <$> arbitrary)
        , (6, fromCostList <$> arbitrary)
        ]

    shrink (CostLast cost)       = map CostLast $ shrink cost
    shrink (CostCons cost costs) = CostLast cost : costs : do
        (costs', cost') <- shrink (costs, cost)
        pure $ CostCons cost' costs'

instance CoArbitrary SatInt where
    coarbitrary = coarbitrary . fromIntegral @Int @Int64 . unSatInt

instance Function SatInt where
    function = functionMap (fromIntegral . unSatInt) $ fromIntegral @Int64

checkEqualsVia :: Show a => (a -> a -> Bool) -> a -> a -> Property
checkEqualsVia eq x y =
    counterexample (show x ++ interpret res ++ show y) res
  where
    res = eq x y
    interpret True  = " === "
    interpret False = " =/= "

bottom :: a
bottom = error "this value wasn't supposed to be forced"

test_SatIntDistribution :: TestTree
test_SatIntDistribution =
    testProperty "distribution of the generated values" . withMaxSuccess 10000 $
        \cost ->
            let (low, high) = toRange cost
            in label (show low ++ " - " ++ show high) $ cost >= 0

test_CostStreamDistribution :: TestTree
test_CostStreamDistribution =
    testProperty "distribution of the generated CostStream values" . withMaxSuccess 10000 $
        \costs ->
            let costsSum = sumCostStream costs
                (low, high) = toRange costsSum
            in label (show low ++ " - " ++ show high) $ costsSum >= 0

test_toCostListRoundtrip :: TestTree
test_toCostListRoundtrip =
    testProperty "fromCostList cancels toCostList" . withMaxSuccess 5000 $ \costs ->
        checkEqualsVia eqCostStream
            (fromCostList $ toCostList costs)
            costs

test_fromCostListRoundtrip :: TestTree
test_fromCostListRoundtrip =
    testProperty "toCostList cancels fromCostList" . withMaxSuccess 5000 $ \costs ->
        toCostList (fromCostList costs) ===
            costs

test_unconsCostRoundtrip :: TestTree
test_unconsCostRoundtrip =
    testProperty "reconsCost cancels unconsCost" . withMaxSuccess 5000 $ \costs ->
        checkEqualsVia eqCostStream
            (uncurry reconsCost $ unconsCost costs)
            costs

test_sumCostStreamIsSum :: TestTree
test_sumCostStreamIsSum =
    testProperty "sumCostStream is sum" . withMaxSuccess 5000 $ \costs ->
        sumCostStream costs ===
            sum (toCostList costs)

test_mapCostStreamIsMap :: TestTree
test_mapCostStreamIsMap =
    testProperty "mapCostStream is map" . withMaxSuccess 500 $ \(Fun _ f) costs ->
        checkEqualsVia eqCostStream
            (mapCostStream f $ fromCostList costs)
            (fromCostList $ fmap f costs)

test_addCostStreamIsAdd :: TestTree
test_addCostStreamIsAdd =
    testProperty "addCostStream is add" . withMaxSuccess 5000 $ \costs1 costs2 ->
        sumCostStream (addCostStream costs1 costs2) ===
            sumCostStream costs1 + sumCostStream costs2

test_minCostStreamIsMin :: TestTree
test_minCostStreamIsMin =
    testProperty "minCostStream is min" . withMaxSuccess 5000 $ \costs1 costs2 ->
        sumCostStream (minCostStream costs1 costs2) ===
            min (sumCostStream costs1) (sumCostStream costs2)

test_zipCostStreamIsZip :: TestTree
test_zipCostStreamIsZip =
    testProperty "zipCostStream is zip" . withMaxSuccess 5000 $ \costs1 costs2 ->
        sumExBudgetStream (zipCostStream costs1 costs2) ===
            ExBudget (ExCPU $ sumCostStream costs1) (ExMemory $ sumCostStream costs2)

test_mapCostStreamReasonableSize :: TestTree
test_mapCostStreamReasonableSize =
    testProperty "mapCostStream: reasonable size" . withMaxSuccess 500 $ \(Fun _ f) costs ->
        length (toCostList (mapCostStream f costs)) ===
            length (toCostList costs)

test_addCostStreamReasonableSize :: TestTree
test_addCostStreamReasonableSize =
    testProperty "addCostStream: reasonable size " . withMaxSuccess 5000 $ \costs1 costs2 ->
        max 2 (length (toCostList (addCostStream costs1 costs2))) ===
            length (toCostList costs1) + length (toCostList costs2)

test_minCostStreamReasonableSize :: TestTree
test_minCostStreamReasonableSize =
    testProperty "minCostStream: reasonable size " . withMaxSuccess 5000 $ \costs1 costs2 ->
        let len1   = length $ toCostList costs1
            len2   = length $ toCostList costs2
            lenMin = length . toCostList $ minCostStream costs1 costs2
        in lenMin >= min len1 len2 && lenMin <= len1 + len2

test_zipCostStreamReasonableSize :: TestTree
test_zipCostStreamReasonableSize =
    testProperty "zipCostStream: reasonable size " . withMaxSuccess 5000 $ \costs1 costs2 ->
        length (toExBudgetList (zipCostStream costs1 costs2)) ===
            max (length (toCostList costs1)) (length (toCostList costs2))

test_mapCostStreamHandlesBottom :: TestTree
test_mapCostStreamHandlesBottom =
    testProperty "mapCostStream handles bottom suffixes" . withMaxSuccess 500 $ \(Fun _ f) xs ->
        let n = length xs
            -- 'fromCostList' forces an additional element, so we account for that here.
            suff = 0 : bottom
            costs = fromCostList . NonEmpty $ xs ++ suff
        in length (take n . getNonEmpty . toCostList $ mapCostStream f costs) === n

test_addCostStreamHandlesBottom :: TestTree
test_addCostStreamHandlesBottom =
    testProperty "addCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \(Positive n) ->
        let interleave xs ys = concat $ transpose [xs, ys]
            zeroToN = map toSatInt [0 .. n] ++ bottom
            nPlus1To2NPlus1 = map toSatInt [n + 1 .. n * 2 + 1] ++ bottom
            taken = take n . getNonEmpty . toCostList $ addCostStream
                (fromCostList $ NonEmpty zeroToN)
                (fromCostList $ NonEmpty nPlus1To2NPlus1)
        in  -- Every element in the resulting stream comes from one of the generated lists.
            all (\cost -> cost `elem` interleave zeroToN nPlus1To2NPlus1) taken .&&.
            -- No element is duplicated.
            length (map head . group $ sort taken) === length taken

test_minCostStreamHandlesBottom :: TestTree
test_minCostStreamHandlesBottom =
    testProperty "minCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \xs ys ->
        let m = min (sum xs) (sum ys)
            -- 'minCostStream' can force only a single extra element of the stream.
            suff = 0 : bottom
            xsYsMin = minCostStream
                (fromCostList . NonEmpty $ xs ++ suff)
                (fromCostList . NonEmpty $ ys ++ suff)
        in -- Rolling '(+)' over a list representing the minimum of two streams eventually
           -- gives us the sum of the minimum stream before triggering any of the bottoms.
           not . null . dropWhile (/= m) . scanl' (+) 0 . getNonEmpty $ toCostList xsYsMin

postAlignWith :: a -> [a] -> [a] -> ([a], [a])
postAlignWith z xs ys = (align xs, align ys) where
    align zs = take (length xs `max` length ys) $ zs ++ repeat z

test_zipCostStreamHandlesBottom :: TestTree
test_zipCostStreamHandlesBottom =
    testProperty "zipCostStream handles bottom suffixes" . withMaxSuccess 5000 $ \xs ys ->
        let z = ExBudget (ExCPU $ sum xs) (ExMemory $ sum ys)
            (xsA, ysA) = postAlignWith 0 xs ys
            -- 'fromCostList' forces an additional element, so we account for that here.
            suff = 0 : bottom
            xys = zipCostStream
                (fromCostList . NonEmpty $ xsA ++ suff)
                (fromCostList . NonEmpty $ ysA ++ suff)
        in  -- Rolling '(<>)' over a list representing the zipped cost streams eventually
            -- gives us an 'ExBudget' containing the sums of the streams computed separately.
            not . null . dropWhile (/= z) . scanl' (<>) mempty . getNonEmpty $
                toExBudgetList xys

cndSize :: Int -> Int
cndSize n0
    | n0 <= 1   = 1
    | otherwise = cndSize (n0 - 1) * 3 + 1

-- | Return a finite balanced tree with each node (apart from the leaves) having exactly 3 children.
-- The parameter is the depth of the tree.
cndRose :: Int -> CostRose
cndRose n0
    | n0 <= 1   = CostRose 1 []
    | otherwise = CostRose (fromIntegral n0) . go . replicate 3 $ n0 - 1
  where
    -- Inlining the definition of @map cndRose@ manually to make sure subtrees are definitely
    -- not shared, so that we don't retain them in memory unnecessarily.
    go :: [Int] -> [CostRose]
    go []       = []
    go (n : ns) = cndRose n : go ns

test_flattenCostRoseIsLinearForCndRose :: Int -> TestTree
test_flattenCostRoseIsLinearForCndRose depth =
    let size = cndSize depth
    in testProperty ("cnd rose: taking " ++ show size ++ " elements") $
        withMaxSuccess 1 $
            length (toCostList . flattenCostRose $ cndRose depth) ===
                size

test_flattenCostRoseIsLinear :: TestTree
test_flattenCostRoseIsLinear = testGroup "flattenCostRose is linear"
    [ test_flattenCostRoseIsLinearForCndRose 12
    , test_flattenCostRoseIsLinearForCndRose 13
    , test_flattenCostRoseIsLinearForCndRose 14
    ]

uniqueVectorOf :: Eq a => Int -> Gen a -> Gen [a]
uniqueVectorOf i0 genX = go [] i0 where
    go acc i
        | i <= 0    = pure acc
        | otherwise = do
              x <- genX `suchThat` (`notElem` acc)
              go (x : acc) (i - 1)

-- >>> map (\i -> (i, toMaxChunkNumber i)) [1..10]
-- [(1,1),(2,2),(3,3),(4,3),(5,3),(6,3),(7,3),(8,4),(9,4),(10,4)]
toMaxChunkNumber :: Int -> Int
toMaxChunkNumber len = case len `compare` 1 of
    LT -> error "length cannot be less than 1"
    EQ -> 1
    GT -> ceiling . sqrt $ fromIntegral len + (2 :: Double)

zapWith :: a -> b -> (a -> b -> c) -> [a] -> [b] -> [c]
zapWith xz yz f = go where
    go []     ys     = map (\y -> f xz y) ys
    go xs     []     = map (\x -> f x yz) xs
    go (x:xs) (y:ys) = f x y : go xs ys

-- >>> map (\p@(i, j) -> (p, toChunkNumber i j)) $ concatMap (\i -> map (\j -> (i, j)) [1..i]) [1..5]
-- [((1,1),1),((2,1),1),((2,2),1),((3,1),1),((3,2),2),((3,3),1),((4,1),1),((4,2),3),((4,3),3),((4,4),1),((5,1),1),((5,2),4),((5,3),6),((5,4),4),((5,5),1)]
--
-- | Calculate the number ofways to divide a list of length @len@ into @chunkNum@ chunks.
-- Equals to @C(len - 1, chunksNum - 1)@.
toChunkNumber :: Int -> Int -> Int
toChunkNumber len chunkNum =
    -- Not calculating factorials directly, since those grow way too quickly.
    round @Double . product $ zapWith 1 1 (\x y -> fromIntegral x / fromIntegral y)
        [len - 1, len - 2 .. len - chunkNum + 1]
        [chunkNum - 1, chunkNum - 2 .. 2]

toChunkFrequencies :: Int -> Int -> [(Int, Int)]
toChunkFrequencies len chunkMax = map (\num -> (toChunkNumber len num, num)) [1 .. chunkMax]

toChunks :: [Int] -> [a] -> [[a]]
toChunks []       xs = [xs]
toChunks (n : ns) xs = chunk : toChunks ns xs' where
    (chunk, xs') = splitAt n xs

multiSplit :: [a] -> Gen [NonEmptyList a]
multiSplit [] = pure []
multiSplit xs = do
    let len = length xs
        chunkMax = toMaxChunkNumber len
    chunkNum <- frequency . map (fmap pure) $ toChunkFrequencies len chunkMax
    breakpointsSet <- uniqueVectorOf (chunkNum - 1) $ choose (1, len - 1)
    let breakpoints = sort breakpointsSet
        chunkLens = zipWith (-) breakpoints (0 : breakpoints)
    pure . coerce $ toChunks chunkLens xs

genCostRose :: NonEmptyList SatInt -> Gen CostRose
genCostRose (NonEmpty [])             = error "an impossible happened"
genCostRose (NonEmpty (cost : costs)) = CostRose cost <$> do
    forest <- multiSplit costs
    traverse genCostRose forest

fromCostRose :: CostRose -> NonEmptyList SatInt
fromCostRose (CostRose cost costs) =
    NonEmpty $ cost : concatMap (getNonEmpty . fromCostRose) costs

instance Arbitrary CostRose where
    arbitrary = arbitrary >>= genCostRose

    shrink (CostRose cost costs) = do
        (costs', cost') <- shrink (costs, cost)
        pure $ CostRose cost' costs'

test_multiSplitDistributionAt :: Int -> TestTree
test_multiSplitDistributionAt n =
    testProperty ("for a list of length " ++ show n) $
        withMaxSuccess 10000 . forAll (multiSplit $ replicate n ()) $ \aSplit ->
            label (show $ map length aSplit) True

test_multiSplitDistribution :: TestTree
test_multiSplitDistribution =
    testGroup ("distribution of values generated by multiSplit") $
        [ test_multiSplitDistributionAt 1
        , test_multiSplitDistributionAt 2
        , test_multiSplitDistributionAt 3
        , test_multiSplitDistributionAt 4
        , test_multiSplitDistributionAt 5
        ]

collectListLengths :: CostRose -> [Int]
collectListLengths (CostRose _ costs) = length costs : concatMap collectListLengths costs

test_CostRoseDistribution :: TestTree
test_CostRoseDistribution =
    testProperty "distribution of list lengths in CostRose values" $
        withMaxSuccess 5000 $ \rose ->
            tabulate "" (map show $ collectListLengths rose) True

test_genCostRoseSound :: TestTree
test_genCostRoseSound =
    testProperty "genCostRose puts 100% of its input and nothing else into the output" $
        withMaxSuccess 5000 $ \costs ->
            forAll (genCostRose costs) $ \rose ->
                fromCostRose rose ===
                    costs

test_flattenCostRoseSound :: TestTree
test_flattenCostRoseSound =
    testProperty "flattenCostRose puts 100% of its input and nothing else into the output" $
        withMaxSuccess 5000 $ \rose ->
            -- This assumes that 'flattenCostRose' is left-biased, which isn't really
            -- necessarily, but it doesn't seem like we're giving up on the assumption any time soon
            -- anyway, so why not keep it simple instead of sorting the results.
            checkEqualsVia eqCostStream
                (flattenCostRose rose)
                (fromCostList $ fromCostRose rose)

test_costing :: TestTree
test_costing = testGroup "costing"
    [ test_SatIntDistribution
    , test_CostStreamDistribution
    , test_toCostListRoundtrip
    , test_fromCostListRoundtrip
    , test_unconsCostRoundtrip
    , test_sumCostStreamIsSum
    , test_mapCostStreamIsMap
    , test_addCostStreamIsAdd
    , test_minCostStreamIsMin
    , test_zipCostStreamIsZip
    , test_mapCostStreamReasonableSize
    , test_addCostStreamReasonableSize
    , test_minCostStreamReasonableSize
    , test_zipCostStreamReasonableSize
    , test_mapCostStreamHandlesBottom
    , test_addCostStreamHandlesBottom
    , test_minCostStreamHandlesBottom
    , test_zipCostStreamHandlesBottom
    , test_flattenCostRoseIsLinear
    , test_multiSplitDistribution
    , test_CostRoseDistribution
    , test_genCostRoseSound
    , test_flattenCostRoseSound
    ]
