module Data.Double.Conversion.Text
    (
      toExponential
    , toFixed
    , toPrecision
    , toShortest
    ) where

import Data.Text (Text)

toExponential :: Int -> Double -> Text
toExponential _ _ = error "toExponential not implemented"

toFixed :: Int -> Double -> Text
toFixed _ _ = error "toFixed not implemented"

toShortest :: Double -> Text
toShortest _ = error "toShortest not implemented"

toPrecision :: Int -> Double -> Text
toPrecision _ = error "toPrecision not implemented"

