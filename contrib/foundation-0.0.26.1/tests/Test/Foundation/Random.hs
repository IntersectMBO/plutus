{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Test.Foundation.Random
    ( testRandom
    ) where

import Foundation
import Foundation.Check
import Foundation.Primitive
import Foundation.Array
import Foundation.Collection
import Foundation.System.Entropy
import Foundation.Random
import qualified Prelude
import qualified Data.List
import GHC.ST

testRandom :: Test
testRandom = Group "random"
    [ CheckPlan "entropy" entropyCheck
    , CheckPlan "rngv1" rngv1Check
    ]

entropyCheck, rngv1Check :: Check ()
entropyCheck = pick "get-entropy" (getEntropy 1024) >>= testDataAppearRandom
rngv1Check = pick "get-rng" getRng >>= testDataAppearRandom
  where getRng = do rng <- randomNew :: IO RNG
                    pure $ mconcat $ fst $ withRandomGenerator rng $ mapM getRandomBytes [1,2,4,8,32,80,250,2139]

-- property to check that the data appears random enough
--
-- if this test fails it doesn't necessarily means it's not normal.
testDataAppearRandom :: UArray Word8 -> Check ()
testDataAppearRandom dat = do
    validate "entropy"     $ (\x -> x > 6.5 && x <= 8)    (res_entropy v)
    validate "mean"        $ (\x -> x >= 112 && x <= 144) (res_mean v)
    validate "compression" $ (\x -> x >= 0 && x <= 5.0)   (res_compressionPercent v)
  where
    v = randomTest dat

-------- generic random testing

data RandomTestResult = RandomTestResult
    { res_totalChars         :: Word64 -- ^ Total number of characters
    , res_entropy            :: Double -- ^ Entropy per byte
    , res_chi_square         :: Double -- ^ Chi Square
    , res_mean               :: Double -- ^ Arithmetic Mean
    , res_compressionPercent :: Double -- ^ Theorical Compression percent
    , res_probs              :: [Double] -- ^ Probability of every bucket
    } deriving (Show,Eq)

-- | Mutable random test State
newtype RandomTestState s = RandomTestState (MUArray Word64 (PrimState (ST s)))

-- | Initialize new state to run tests
randomTestInitialize :: ST s (RandomTestState s)
randomTestInitialize = do
    m <- mutNew 256
    forM_ [0..255] $ \i -> mutWrite m i 0
    return $ RandomTestState m

-- | Append random data to the test state
randomTestAppend :: RandomTestState s -> UArray Word8 -> ST s ()
randomTestAppend (RandomTestState buckets) = mapM_ (addVec 1 . Offset . fromIntegral) . toList
  where
    addVec a i = mutRead buckets i >>= \d -> mutWrite buckets i $! d+a

-- | Finalize random test state into some result
randomTestFinalize :: RandomTestState s -> ST s RandomTestResult
randomTestFinalize (RandomTestState buckets) = (calculate . toList) <$> freeze buckets

randomTest :: UArray Word8 -> RandomTestResult
randomTest a = runST $ do
    st <- randomTestInitialize
    randomTestAppend st a
    randomTestFinalize st

calculate :: [Word64] -> RandomTestResult
calculate buckets = RandomTestResult
    { res_totalChars = totalChars
    , res_entropy    = entropy
    , res_chi_square = chisq
    , res_mean       = fromIntegral datasum Prelude./ fromIntegral totalChars
    , res_compressionPercent = 100.0 * (8 - entropy) Prelude./ 8.0
    , res_probs      = probs
    }
  where totalChars = Prelude.sum buckets
        probs = fmap (\v -> fromIntegral v Prelude./ fromIntegral totalChars :: Double) buckets
        entropy = Data.List.foldl' accEnt 0.0 probs
        cexp    = fromIntegral totalChars Prelude./ 256.0 :: Double
        (datasum, chisq) = foldl' accMeanChi (0, 0.0) $ Prelude.zip [0..255] buckets
        --chip' = abs (sqrt (2.0 * chisq) - sqrt (2.0 * 255.0 - 1.0))

        accEnt ent pr
            | pr > 0.0  = ent + (pr * xlog (1 Prelude./ pr))
            | otherwise = ent
        xlog v = Prelude.logBase 10 v * (Prelude.logBase 2 10)

        accMeanChi :: (Word64, Double) -> (Int, Word64) -> (Word64, Double)
        accMeanChi (dataSum, chiSq) (i, ccount) =
            let a      = fromIntegral ccount - cexp
             in (dataSum + fromIntegral i * ccount, chiSq + (a * a Prelude./ cexp))
