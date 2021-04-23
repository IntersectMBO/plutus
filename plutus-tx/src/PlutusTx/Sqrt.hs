{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module PlutusTx.Sqrt(
    Sqrt (..)
    , rsqrt
    , isqrt
    ) where

import           PlutusTx.IsData  (makeIsDataIndexed)
import           PlutusTx.Lift    (makeLift)
import           PlutusTx.Prelude (divide, negate, otherwise, ($), (*), (+), (<), (<=), (==))
import           Prelude          (Integer)
import qualified Prelude          as Haskell

-- | Integer square-root representation, discarding imaginary integers.
data Sqrt
  = Imaginary
  | Exact Integer
  | Irrational Integer
  deriving stock Haskell.Show

{-# INLINABLE rsqrt #-}
-- | Calculates `rsqrt n d` the 'Integer' component of the d'th root of `n`
-- and tags whether it was 'Exact', or 'Irrationa'. If it's imaginary, we
-- don't return the integer part, and simple return 'Imaginary'. As the 0'th
-- root of n is undefined, calling this function with `d = 0` results in an
-- error.
rsqrt :: Integer -> Integer -> Sqrt
rsqrt n d
    | n * d < 0 = Imaginary
    | n == 0    = Exact 0
    | n == d    = Exact 1
    | n < 0     = rsqrt (negate n) (negate d)
    | otherwise = go 1 $ 1 + divide n d
  where
    go :: Integer -> Integer -> Sqrt
    go l u
        | l * l * d == n = Exact l
        | u == (l + 1)   = Irrational l
        | otherwise      =
              let
                m = divide (l + u) 2
              in
                if m * m * d <= n then go m u
                                  else go l m

{-# INLINABLE isqrt #-}
-- | Calculates the integer-component of the sqrt of 'n'.
isqrt :: Integer -> Sqrt
isqrt n = rsqrt n 1

makeLift ''Sqrt
makeIsDataIndexed ''Sqrt [ ('Imaginary,  0)
                         , ('Exact,      1)
                         , ('Irrational, 2)
                         ]
