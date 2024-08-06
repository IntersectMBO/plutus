{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module PlutusTx.Sqrt(
    Sqrt (..)
    , rsqrt
    , isqrt
    ) where

import PlutusTx.IsData (makeIsDataIndexed)
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude (Integer, divide, negate, otherwise, ($), (*), (+), (<), (<=), (==))
import PlutusTx.Ratio (Rational, denominator, numerator, unsafeRatio)
import Prelude qualified as Haskell

-- | Integer square-root representation, discarding imaginary integers.
data Sqrt
  -- | The number was negative, so we don't even attempt to compute it;
  -- just note that the result would be imaginary.
  = Imaginary
  -- | An exact integer result. The 'rsqrt' of 4 is 'Exactly 2'.
  | Exactly Integer
  -- | The Integer component (i.e. the floor) of a non-integral result. The
  -- 'rsqrt 2' is 'Approximately 1'.
  | Approximately Integer
  deriving stock (Haskell.Show, Haskell.Eq)

{-# INLINABLE rsqrt #-}
-- | Calculates the sqrt of a ratio of integers. As x / 0 is undefined,
-- calling this function with `d=0` results in an error.
rsqrt :: Rational -> Sqrt
rsqrt r
    | n * d < 0 = Imaginary
    | n == 0    = Exactly 0
    | n == d    = Exactly 1
    | n < d     = Approximately 0
    | n < 0     = rsqrt $ unsafeRatio (negate n) (negate d)
    | otherwise = go 1 $ 1 + divide n d
  where
    n = numerator r
    d = denominator r
    go :: Integer -> Integer -> Sqrt
    go l u
        | l * l * d == n = Exactly l
        | u == (l + 1)   = Approximately l
        | otherwise      =
              let
                m = divide (l + u) 2
              in
                if m * m * d <= n then go m u
                                  else go l m

{-# INLINABLE isqrt #-}
-- | Calculates the integer-component of the sqrt of 'n'.
isqrt :: Integer -> Sqrt
isqrt n = rsqrt (unsafeRatio n 1)

makeLift ''Sqrt
makeIsDataIndexed ''Sqrt [ ('Imaginary,     0)
                         , ('Exactly,       1)
                         , ('Approximately, 2)
                         ]
