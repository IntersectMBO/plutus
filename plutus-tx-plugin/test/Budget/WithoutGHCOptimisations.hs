{-# OPTIONS_GHC -O0 -fmax-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Budget.WithoutGHCOptimisations where

import PlutusTx.Prelude qualified as PlutusTx

f :: Integer -> Integer -> Bool
f x y = (PlutusTx.&&) (x PlutusTx.< (3 :: Integer)) (y PlutusTx.< (3 :: Integer))
