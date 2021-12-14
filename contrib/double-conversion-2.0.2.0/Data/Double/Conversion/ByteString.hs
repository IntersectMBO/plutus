module Data.Double.Conversion.ByteString
    (
      toExponential
    , toFixed
    , toPrecision
    , toShortest
    ) where

import Data.ByteString.Internal (ByteString)

toExponential :: Int -> Double -> ByteString
toExponential _ _ = error "toExponential not implemented"

toFixed :: Int -> Double -> ByteString
toFixed _ _ = error "toFixed not implemented"

toShortest :: Double -> ByteString
toShortest _ = error "toShortest not implemented"

toPrecision :: Int -> Double -> ByteString
toPrecision _ = error "toPrecision not implemented"

