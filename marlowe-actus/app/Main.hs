{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Complex
import qualified Language.R as R
import Language.R (R)
import Language.R.QQ

-- Call R's FFT
r_fft :: [Complex Double] -> R s [Complex Double]
r_fft nums = do
    R.dynSEXP <$> [r| fft(nums_hs) |]

main :: IO ()
main = R.withEmbeddedR R.defaultConfig $ do
    result <- R.runRegion $ r_fft [1,2,1]
    print result