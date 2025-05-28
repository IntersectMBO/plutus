{-# OPTIONS_GHC -O1 #-}

module Budget.WithGHCOptimisations where

import PlutusTx.Prelude qualified as PlutusTx

f :: Integer -> Integer -> Bool
f x y = (PlutusTx.&&) (x PlutusTx.< (3 :: Integer)) (y PlutusTx.< (3 :: Integer))
